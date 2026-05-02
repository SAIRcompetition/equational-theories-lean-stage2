"""
Marathon-mode local LLM proxy.

The proxy interposes between the solver subprocess and the real upstream
(OpenRouter / OpenAI / DeepSeek). It exists to give marathon mode the same
defensive posture Solo gets from ``pipeline/proxy.py``:

  * The real upstream API key is never exposed to the solver — the proxy
    holds it, the solver only sees a localhost base URL plus a per-run
    shared secret.
  * Token budget is enforced at the network layer. Even a solver that
    bypasses ``marathon_llm.call_llm`` and uses the OpenAI SDK directly
    has to go through this proxy (because that is the only LLM endpoint
    reachable from the solver's env), so the meter cannot be bypassed.

The proxy speaks an OpenAI-compatible subset:

  POST /v1/chat/completions   — forwarded upstream, ``usage`` is parsed
                                and added to the running token total.

It binds to 127.0.0.1 only and authenticates callers via a shared secret
generated per run (``Authorization: Bearer <secret>``). The secret is
delivered to the solver as ``OPENAI_API_KEY``; any local process without
the secret is rejected.

Token accounting is held in memory under a lock and is the sole authority
for the running total — the runner watchdog reads it via
``proxy_handle.tokens_used()`` (in-process call, no file I/O). The proxy
also writes a telemetry file ``<state_dir>/tokens_used.txt`` for offline
debugging, but ``state_dir`` is a runner-private directory NOT exposed to
the solver subprocess. A solver that writes to its own
``<scratch>/tokens_used.txt`` cannot influence the counter the runner
watchdog or budget pre-check consults.
"""
from __future__ import annotations

import json
import os
import secrets
import socket
import threading
import time
from dataclasses import dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any


_TOKENS_FILE_NAME = "tokens_used.txt"
# Pessimistic estimate when the upstream omits ``usage`` — keeps the meter
# moving so a buggy / hostile upstream can't be used to underflow the
# budget. Real cost lands on the next call when usage is present.
_CHARS_PER_TOKEN_FALLBACK = 4
# Max body size we'll accept from the solver (4 MB). Larger requests are
# rejected to prevent disk/CPU DoS via Content-Length spoofing.
_MAX_REQUEST_BYTES = 4 * 1024 * 1024
# Hard ceiling on per-call output tokens. Mirrors Solo's
# ``llm.max_output_tokens`` reference value. The proxy clamps the
# solver's requested ``max_tokens`` down to this; a solver cannot
# unilaterally inflate the per-call reservation past this cap.
_MAX_OUTPUT_TOKENS_PER_CALL = 65536


def _prompt_chars_for_messages(messages: Any) -> int:
    """Count prompt characters across all messages.

    Supports both content shapes the OpenAI chat schema accepts:

      * ``content: str``                    — count its length.
      * ``content: list[{"type": "text",
                         "text": str}]``    — sum the part lengths.

    Pre-fix this used ``len(m.get("content") or "")`` blindly, so a
    solver that sent a multi-part list of texts had its prompt
    underestimated as the list length (one or two characters), letting
    a multi-MB payload slip past the reservation gate. Non-text parts
    (``image_url``, ``input_audio``, …) are intentionally rejected by
    ``_validate_messages`` upstream of this helper, so we don't have to
    estimate their token cost here.
    """
    total = 0
    if not isinstance(messages, list):
        return 0
    for m in messages:
        if not isinstance(m, dict):
            continue
        content = m.get("content")
        if isinstance(content, str):
            total += len(content)
        elif isinstance(content, list):
            for part in content:
                if isinstance(part, dict):
                    text = part.get("text")
                    if isinstance(text, str):
                        total += len(text)
    return total


def _validate_messages(messages: Any) -> str | None:
    """Reject message shapes the budget gate cannot reason about.

    The proxy enforces the token budget via a pessimistic reservation;
    that reservation is only meaningful if every supported content
    shape is enumerable as plain text. Non-text content parts
    (``image_url``, ``input_audio``, etc.) carry fixed multimodal token
    costs that vary per provider, so we refuse them outright rather
    than paper over the gap with a fudge factor that an attacker could
    sneak under.
    """
    if not isinstance(messages, list):
        return "messages must be a JSON array"
    for idx, m in enumerate(messages):
        if not isinstance(m, dict):
            return f"messages[{idx}] is not an object"
        content = m.get("content")
        if content is None or isinstance(content, str):
            continue
        if isinstance(content, list):
            for j, part in enumerate(content):
                if not isinstance(part, dict):
                    return (
                        f"messages[{idx}].content[{j}] is not an object"
                    )
                t = part.get("type")
                if t != "text":
                    return (
                        f"messages[{idx}].content[{j}].type={t!r} is "
                        "not supported (text-only multipart allowed)"
                    )
                if not isinstance(part.get("text"), str):
                    return (
                        f"messages[{idx}].content[{j}].text must be a "
                        "string"
                    )
            continue
        return (
            f"messages[{idx}].content must be string or list, got "
            f"{type(content).__name__}"
        )
    return None


@dataclass
class ProxyConfig:
    """Per-run config the runner hands to the proxy.

    All fields are immutable for the lifetime of the proxy. The runner
    snapshots upstream credentials before the proxy starts so a malicious
    solver cannot influence them by editing env mid-run.

    ``state_dir`` is the proxy's *private* working directory (telemetry
    only). It is intentionally distinct from the solver's scratch dir —
    the solver has no env reference to it and cannot reach it without a
    filesystem-traversal escalation. The on-disk telemetry file is *not*
    consulted by the runner; the in-memory counter under
    ``_tokens_lock`` is the single authority.
    """
    state_dir: Path
    budget_tokens: int
    upstream_base_url: str = "https://openrouter.ai/api/v1"
    upstream_api_key: str = ""
    upstream_provider_env: dict[str, str] | None = None
    request_timeout_seconds: float = 600.0


class _AuthError(Exception):
    pass


class _BudgetExhausted(Exception):
    pass


class _MarathonProxyHandler(BaseHTTPRequestHandler):
    """HTTP request handler for the marathon proxy.

    Server-side state (config, secret, tokens_used) lives on the
    ``ThreadingHTTPServer`` instance so handlers stay stateless.
    """

    server_version = "MarathonProxy/1.0"

    # Per-operation socket timeout. ``BaseHTTPRequestHandler.handle`` reads
    # this and calls ``request.settimeout(self.timeout)``, so any single
    # send/recv that stalls for more than this long raises and the thread
    # exits. This defangs the simple form of slowloris (open many TCP
    # connections, then never send anything) — each idle connection costs
    # at most ``timeout`` seconds of a thread's life.
    timeout = 5.0

    # Quiet the default access log; the runner already logs solver activity
    # via stderr drains. The proxy writes only its own warnings/errors.
    def log_message(self, fmt: str, *args: Any) -> None:
        return

    def _read_body_with_deadline(self, length: int, deadline_seconds: float = 5.0) -> bytes:
        """Read exactly ``length`` body bytes within ``deadline_seconds``.

        Plain ``self.rfile.read(length)`` is bounded by the per-op socket
        timeout — but a slow-trickle attacker that drips one byte every
        ``timeout - epsilon`` seconds keeps the connection alive
        indefinitely while the runner-side thread blocks. This helper
        reads in fixed-size chunks and enforces a total deadline; if the
        body isn't fully read in time, it raises ``OSError``.
        """
        end = time.monotonic() + deadline_seconds
        out = bytearray()
        while len(out) < length:
            if time.monotonic() > end:
                raise OSError("body read deadline exceeded")
            chunk_size = min(64 * 1024, length - len(out))
            chunk = self.rfile.read(chunk_size)
            if not chunk:
                raise OSError("connection closed before body fully read")
            out.extend(chunk)
        return bytes(out)

    def _reject(self, status: int, message: str) -> None:
        body = json.dumps({"error": {"message": message}}).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _check_auth(self) -> None:
        header = self.headers.get("Authorization", "")
        if not header.startswith("Bearer "):
            raise _AuthError("missing Authorization: Bearer")
        secret = header[len("Bearer "):].strip()
        expected = self.server.shared_secret  # type: ignore[attr-defined]
        # Constant-time compare to defeat timing attacks even on localhost.
        if not secrets.compare_digest(secret, expected):
            raise _AuthError("invalid shared secret")

    def do_POST(self) -> None:  # noqa: N802 — http.server API
        try:
            self._check_auth()
        except _AuthError as exc:
            self._reject(401, f"unauthorized: {exc}")
            return

        if self.path not in ("/v1/chat/completions", "/chat/completions"):
            self._reject(404, f"unsupported endpoint: {self.path}")
            return

        try:
            length = int(self.headers.get("Content-Length", "0") or "0")
        except ValueError:
            self._reject(400, "invalid Content-Length")
            return
        if length <= 0 or length > _MAX_REQUEST_BYTES:
            self._reject(413, f"request body must be 1..{_MAX_REQUEST_BYTES} bytes")
            return
        try:
            raw = self._read_body_with_deadline(length)
        except (OSError, ValueError) as exc:
            self._reject(400, f"read failed: {exc}")
            return
        try:
            payload = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            self._reject(400, f"invalid JSON body: {exc}")
            return
        if not isinstance(payload, dict):
            self._reject(400, "request body must be a JSON object")
            return

        config: ProxyConfig = self.server.config  # type: ignore[attr-defined]

        # Clamp the per-call output ceiling so the reservation we're
        # about to make is bounded. A solver that asks for max_tokens
        # bigger than the policy ceiling gets it silently lowered —
        # this prevents one call from monopolising or overshooting the
        # global budget.
        try:
            requested_max = int(payload.get("max_tokens", 4096))
        except (TypeError, ValueError):
            requested_max = 4096
        if requested_max <= 0:
            requested_max = 4096
        if requested_max > _MAX_OUTPUT_TOKENS_PER_CALL:
            requested_max = _MAX_OUTPUT_TOKENS_PER_CALL
        payload["max_tokens"] = requested_max

        # Validate message shape BEFORE estimating the prompt. The
        # estimate only handles the two text-shaped content forms; a
        # solver-sent ``image_url`` or ``input_audio`` part would
        # silently bypass the meter otherwise.
        msgs = payload.get("messages", [])
        invalid = _validate_messages(msgs)
        if invalid is not None:
            self._reject(400, invalid)
            return

        # Pessimistic reservation = prompt-token estimate + clamped
        # output ceiling. The reservation is held under a lock for the
        # full upstream round trip and replaced with the actual usage
        # on response. This is what makes the budget check correct
        # under concurrent solver requests — a parallel burst can't
        # all see settled-only consumption and pass.
        prompt_chars = _prompt_chars_for_messages(msgs)
        prompt_estimate = max(1, prompt_chars // _CHARS_PER_TOKEN_FALLBACK)
        reservation = prompt_estimate + requested_max

        granted, effective_after_reserve = self.server.reserve_tokens(reservation)  # type: ignore[attr-defined]
        if not granted:
            self._reject(402, "token budget exhausted")
            return

        # Forward upstream via the OpenAI SDK (same client surface the
        # Solo proxy uses). Routes / extra fields like the OpenRouter
        # ``provider`` and ``reasoning`` blocks pass through untouched —
        # the solver controls what it asks for; the proxy only enforces
        # auth + token counting.
        #
        # Billing rule on failure: if the upstream call raised after we
        # started forwarding, the upstream provider may have already
        # consumed real tokens (e.g., partial generation cut short by a
        # timeout, or 5xx after the request was accepted). Settling
        # ``actual=0`` would turn unreliable upstreams into a free-call
        # vector — a hostile solver could deliberately trigger
        # timeouts to make calls cost-free against the meter. Instead
        # we bill the full reservation in that case, which is the
        # pessimistic upper bound the proxy already promised the
        # budget gate.
        tokens_used_call = 0
        billing_floor = 0
        try:
            try:
                response, tokens_used_call = self.server.forward_upstream(payload)  # type: ignore[attr-defined]
            except _BudgetExhausted:
                # Reserved but never reached upstream; nothing to bill.
                self._reject(402, "token budget exhausted")
                return
            except Exception as exc:  # noqa: BLE001 — SDK raises many shapes
                # Upstream attempted; bill at least the reservation.
                billing_floor = reservation
                self._reject(502, f"upstream error: {type(exc).__name__}: {exc}")
                return
        finally:
            # Always settle: release the reservation; bill the larger
            # of (actual usage, billing_floor). Skipping this on the
            # error paths above would leak reservations and starve
            # future calls.
            self.server.settle_reservation(  # type: ignore[attr-defined]
                reservation, max(int(tokens_used_call), int(billing_floor))
            )

        body = json.dumps(response).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        # Echo our running totals so the SDK caller can read them without
        # a separate file probe. Solvers that ignore these still work.
        new_total = self.server.read_tokens_used()  # type: ignore[attr-defined]
        self.send_header("X-Marathon-Tokens-Used-Call", str(tokens_used_call))
        self.send_header("X-Marathon-Tokens-Used-Total", str(new_total))
        # Mirror reserve_tokens() semantics:
        #   cap > 0  → exact remaining headroom
        #   cap == 0 → 0 (zero budget; no calls would be granted anyway)
        #   cap < 0  → -1 sentinel (unlimited)
        cap = config.budget_tokens
        if cap > 0:
            remaining = max(0, cap - new_total)
        elif cap == 0:
            remaining = 0
        else:
            remaining = -1
        self.send_header("X-Marathon-Tokens-Remaining", str(remaining))
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass


class _MarathonProxyServer(ThreadingHTTPServer):
    """ThreadingHTTPServer subclass that carries per-run state."""

    daemon_threads = True

    # Concurrency cap on handler threads. ``ThreadingHTTPServer`` spawns a
    # thread per accepted connection with no upper bound, so an attacker
    # who opens N TCP sockets without sending data forces the runner to
    # carry N idle threads for up to ``timeout`` seconds each. Even with
    # the body-read deadline in place, a sustained slowloris would still
    # pin O(connections) threads. A semaphore around ``process_request``
    # keeps the live thread count bounded; excess connections queue
    # briefly on accept() and are dropped by the OS backlog if the
    # attacker outpaces drain. 64 is two orders of magnitude over what a
    # legitimate solver needs (one in-flight call at a time in marathon
    # mode) and well below any reasonable thread budget.
    _MAX_CONCURRENT_HANDLERS = 64

    def __init__(self, address: tuple[str, int], handler: type) -> None:
        super().__init__(address, handler)
        self.config: ProxyConfig | None = None
        self.shared_secret: str = ""
        self._tokens_lock = threading.Lock()
        self._handler_semaphore = threading.BoundedSemaphore(
            self._MAX_CONCURRENT_HANDLERS
        )
        # Authoritative running totals. The on-disk telemetry file is a
        # write-only mirror; readers (runner watchdog, pre-call budget
        # check) MUST go through these values under the lock.
        #
        #   _tokens_used_total: settled cost of completed calls.
        #   _tokens_reserved:   pessimistic reservation for in-flight
        #                       calls (released and replaced with the
        #                       actual usage on response).
        #
        # Effective consumption (the value compared against
        # ``budget_tokens``) is the sum of the two — a concurrent burst
        # of calls cannot all pass a pre-check that only sees settled
        # cost.
        self._tokens_used_total: int = 0
        self._tokens_reserved: int = 0

    # ─── Connection admission ────────────────────────────────────────

    def process_request_thread(self, request, client_address):  # type: ignore[override]
        """Per-connection entry point — acquire the concurrency semaphore.

        ``ThreadingMixIn`` spawns a fresh thread per accepted connection
        and calls this method inside it. We bracket the actual handling
        with a non-blocking semaphore acquire: under load (slowloris
        flood, or a legitimate burst of solver calls past the cap), the
        excess connections are closed immediately with no body read so
        the runner thread count stays bounded. Legitimate solvers see
        at most one in-flight call at a time and never hit this gate.
        """
        if not self._handler_semaphore.acquire(blocking=False):
            try:
                self.shutdown_request(request)
            except Exception:  # noqa: BLE001
                pass
            return
        try:
            super().process_request_thread(request, client_address)  # type: ignore[misc]
        finally:
            self._handler_semaphore.release()

    # ─── Token bookkeeping ────────────────────────────────────────────

    def _tokens_path(self) -> Path:
        assert self.config is not None
        return self.config.state_dir / _TOKENS_FILE_NAME

    def read_tokens_used(self) -> int:
        """Return the effective consumption (settled + reserved).

        The runner watchdog and any external observer compares this
        against ``budget_tokens``. Including reservations in the
        observed total is what makes the reservation pattern
        load-bearing — otherwise a thread that has reserved 50k
        tokens would still appear to have spent 0 until its upstream
        call returns, allowing parallel callers to all pass the
        pre-check.
        """
        with self._tokens_lock:
            return int(self._tokens_used_total + self._tokens_reserved)

    def read_tokens_settled(self) -> int:
        """Settled total only — exposed for telemetry / final summary."""
        with self._tokens_lock:
            return int(self._tokens_used_total)

    def _write_tokens_telemetry(self, value: int) -> None:
        """Best-effort write of telemetry file. Failures are non-fatal —
        the in-memory counter is authoritative; this file is for humans."""
        try:
            path = self._tokens_path()
            path.parent.mkdir(parents=True, exist_ok=True)
            tmp = path.with_suffix(".tmp")
            tmp.write_text(str(int(value)), encoding="utf-8")
            os.replace(tmp, path)
        except OSError:
            pass

    def reserve_tokens(self, n: int) -> tuple[bool, int]:
        """Atomically reserve ``n`` tokens against the budget.

        Returns ``(granted, effective_total_after)``. If the reservation
        would push effective consumption past ``budget_tokens``, the
        request is denied and no state changes. The caller MUST settle
        a granted reservation via ``settle_reservation`` (even on
        upstream failure; pass actual=reservation to bill it).

        Budget semantics:
          * ``budget_tokens > 0`` — finite cap, normal check.
          * ``budget_tokens == 0`` — zero LLM budget; every reservation
            is denied (the proxy still runs so non-LLM endpoints work,
            but no upstream forwarding will happen).
          * ``budget_tokens < 0`` — unlimited; reservations are always
            granted (tracked but not capped). Use this for
            organizer-internal probes; production runs never set it.
        """
        n = max(0, int(n))
        with self._tokens_lock:
            assert self.config is not None
            effective = self._tokens_used_total + self._tokens_reserved
            cap = self.config.budget_tokens
            if cap == 0:
                return False, effective
            if cap > 0 and effective + n > cap:
                return False, effective
            self._tokens_reserved += n
            return True, self._tokens_used_total + self._tokens_reserved

    def settle_reservation(self, reserved: int, actual: int) -> int:
        """Replace an outstanding reservation with the call's actual cost.

        Returns the new effective total. Always idempotent over multiple
        calls is NOT a goal — call exactly once per ``reserve_tokens``.
        """
        reserved = max(0, int(reserved))
        actual = max(0, int(actual))
        with self._tokens_lock:
            self._tokens_reserved = max(0, self._tokens_reserved - reserved)
            self._tokens_used_total += actual
            settled = self._tokens_used_total
            effective = settled + self._tokens_reserved
        self._write_tokens_telemetry(settled)
        return effective

    def _preseed_tokens(self, value: int) -> None:
        """Test-only seed of the settled counter. Used by the harness to
        drive token-kill flows without a real upstream. NOT exposed via any
        HTTP route — only the runner (in-process) can call this."""
        with self._tokens_lock:
            self._tokens_used_total = max(0, int(value))
            seeded = self._tokens_used_total
        self._write_tokens_telemetry(seeded)

    def _preseed_reservation(self, value: int) -> None:
        """Test-only seed of the in-flight reservation counter.

        Used by the watchdog regression to hold reservation > budget
        without an actual in-flight upstream call. The watchdog, which
        reads ``tokens_settled()`` only, must remain quiet under this
        condition; pre-fix it would have fired because it observed
        ``settled + reserved`` and saw a value over budget. There is no
        HTTP path that can drive this — it's runner-only.
        """
        with self._tokens_lock:
            self._tokens_reserved = max(0, int(value))

    # ─── Upstream forwarding ──────────────────────────────────────────

    def forward_upstream(self, payload: dict) -> tuple[dict, int]:
        """Forward a chat-completions payload upstream, return (json, tokens).

        Pure forward + parse: token-counter mutation is handled by the
        caller via ``settle_reservation`` so the reserve/forward/settle
        sequence stays atomic from the budget's point of view.
        """
        assert self.config is not None
        from openai import OpenAI
        client = OpenAI(
            api_key=self.config.upstream_api_key,
            base_url=self.config.upstream_base_url,
            timeout=self.config.request_timeout_seconds,
        )
        # Strip our auth-relevant fields; pass everything else through.
        kwargs = dict(payload)
        # The OpenAI SDK's chat.completions.create accepts most JSON-shaped
        # arguments directly. Any unknown kwargs are forwarded via the
        # ``extra_body`` parameter automatically by the SDK when present in
        # the payload — but to be conservative we lift OpenRouter-specific
        # fields out and pack them into extra_body explicitly.
        extra_body: dict[str, Any] = {}
        for k in ("provider", "reasoning", "transforms", "models", "route"):
            if k in kwargs:
                extra_body[k] = kwargs.pop(k)
        if extra_body:
            kwargs["extra_body"] = extra_body

        completion = client.chat.completions.create(**kwargs)

        # Convert the SDK response object back to a plain dict. The OpenAI
        # SDK exposes .model_dump() on Pydantic models.
        try:
            response = completion.model_dump()
        except AttributeError:
            response = json.loads(completion.json())  # type: ignore[attr-defined]

        usage = response.get("usage") if isinstance(response, dict) else None
        if isinstance(usage, dict) and isinstance(usage.get("total_tokens"), int):
            tokens_used_call = int(usage["total_tokens"])
        else:
            # Fallback estimate: prompt + (completion content if any).
            # Same multipart-aware logic as the request-side helper so a
            # provider that omits ``usage`` for multipart calls is still
            # billed for the actual prompt length.
            prompt_chars = _prompt_chars_for_messages(payload.get("messages", []))
            content = ""
            try:
                content = response["choices"][0]["message"].get("content") or ""
            except (KeyError, IndexError, TypeError):
                content = ""
            tokens_used_call = max(
                1,
                (prompt_chars + len(content)) // _CHARS_PER_TOKEN_FALLBACK,
            )

        return response, tokens_used_call


@dataclass
class MarathonProxyHandle:
    """Caller-facing handle returned by ``start_marathon_proxy``."""
    base_url: str          # what the solver should put in OPENAI_BASE_URL
    api_key: str           # what the solver should put in OPENAI_API_KEY
    host: str
    port: int
    _server: _MarathonProxyServer
    _thread: threading.Thread

    def stop(self, timeout: float = 5.0) -> None:
        """Shut the proxy down. Idempotent — safe to call multiple times."""
        try:
            self._server.shutdown()
        except Exception:  # noqa: BLE001
            pass
        try:
            self._server.server_close()
        except Exception:  # noqa: BLE001
            pass
        self._thread.join(timeout=timeout)

    def tokens_used(self) -> int:
        """Effective consumption: settled + outstanding reservations.

        For pre-call gating decisions ("can this caller reserve more?")
        the proxy already enforces this internally. Use
        ``tokens_settled`` for watchdog or final-summary purposes —
        billing should not include speculative reservations.
        """
        return self._server.read_tokens_used()

    def tokens_settled(self) -> int:
        """Settled-only running total — what the run actually paid.

        The runner watchdog uses this so an exact-budget legal
        reservation isn't killed mid-flight: settled stays under cap
        until the reservation completes, regardless of how much
        speculative reservation is held. Mirrors
        ``read_tokens_settled`` on the server.
        """
        return self._server.read_tokens_settled()


def _pick_free_port() -> int:
    """Bind a transient socket to find an unused port. The proxy server
    will rebind to it; tiny race window, harmless on localhost."""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def start_marathon_proxy(
    *,
    state_dir: Path,
    budget_tokens: int,
    upstream_base_url: str | None = None,
    upstream_api_key: str | None = None,
    request_timeout_seconds: float = 600.0,
    preseed_settled_tokens: int = 0,
    preseed_reserved_tokens: int = 0,
) -> MarathonProxyHandle:
    """Start the proxy on 127.0.0.1:<random>. Caller must call ``.stop()``.

    The shared secret is generated fresh per call. Upstream credentials
    default to the env (``OPENAI_BASE_URL`` / ``OPENROUTER_API_KEY`` etc.)
    so the runner can pass through whatever the operator configured.

    ``state_dir`` is a runner-private directory used for write-only
    telemetry; it MUST NOT be the solver's scratch dir. The on-disk file
    written there is informational only — readers should call
    ``handle.tokens_used()`` for the authoritative total.

    ``preseed_settled_tokens`` and ``preseed_reserved_tokens`` are
    test-only kwargs used by the marathon harness to drive
    budget-boundary regressions without standing up a stub upstream.
    They are explicit kwargs (NOT read from process env) so production
    runs cannot be influenced by a stray env var that escaped a CI
    config or a contestant-controlled environment.
    """
    if upstream_base_url is None:
        upstream_base_url = (
            os.environ.get("OPENAI_BASE_URL")
            or "https://openrouter.ai/api/v1"
        )
    if upstream_api_key is None:
        upstream_api_key = (
            os.environ.get("OPENROUTER_API_KEY")
            or os.environ.get("OPENAI_API_KEY")
            or ""
        )
    if not upstream_api_key:
        raise RuntimeError(
            "marathon_proxy: no upstream API key — set OPENROUTER_API_KEY "
            "or OPENAI_API_KEY before launching the marathon runner"
        )

    state_dir = Path(state_dir)
    state_dir.mkdir(parents=True, exist_ok=True)

    config = ProxyConfig(
        state_dir=state_dir,
        budget_tokens=int(budget_tokens),
        upstream_base_url=upstream_base_url,
        upstream_api_key=upstream_api_key,
        request_timeout_seconds=float(request_timeout_seconds),
    )

    port = _pick_free_port()
    server = _MarathonProxyServer(("127.0.0.1", port), _MarathonProxyHandler)
    server.config = config
    server.shared_secret = secrets.token_urlsafe(32)

    # Test-only preseed: lets the harness drive a token-kill flow
    # without standing up a stub upstream. Both seeds are explicit
    # kwargs (NOT process env) so a stray env var cannot silently
    # influence a production run. Production callers always pass 0/0.
    if int(preseed_settled_tokens) > 0:
        server._preseed_tokens(int(preseed_settled_tokens))
    if int(preseed_reserved_tokens) > 0:
        server._preseed_reservation(int(preseed_reserved_tokens))

    thread = threading.Thread(
        target=server.serve_forever,
        kwargs={"poll_interval": 0.2},
        name=f"marathon-proxy-{port}",
        daemon=True,
    )
    thread.start()
    # Give serve_forever a moment to enter its loop before returning so the
    # caller can immediately send requests without a race.
    time.sleep(0.05)

    return MarathonProxyHandle(
        base_url=f"http://127.0.0.1:{port}/v1",
        api_key=server.shared_secret,
        host="127.0.0.1",
        port=port,
        _server=server,
        _thread=thread,
    )
