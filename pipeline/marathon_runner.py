"""
Marathon-mode runner: launches a solver subprocess with a *global* budget
spanning N problems, instead of one subprocess per problem.

This is a separate entry point from ``pipeline/runner.py`` (Solo). The
Solo path is unchanged.

Solver contract (env vars; absent → solver runs in Solo stdin/stdout mode
and this module is irrelevant):

    JUDGE_MARATHON_MANIFEST       /abs/problems.jsonl     read-only manifest
    JUDGE_MARATHON_OUTPUT         /abs/answers.jsonl      append-only JSONL
    JUDGE_MARATHON_BUDGET_SECONDS 30000                   global wall-clock
    JUDGE_MARATHON_BUDGET_TOKENS  3276800                 global LLM tokens
    JUDGE_MARATHON_SCRATCH_DIR    /abs/scratch            wiped each run

Output JSONL line format (last-write-wins per id):

    {"id": "normal_0042", "verdict": "true", "code": "<full Lean source>"}

The runner enforces only the wall-clock budget. Token budget enforcement
lives in ``pipeline/marathon_proxy.py`` (PR2). The runner SIGTERMs the
solver process group at the deadline and SIGKILLs 5 s later; output JSONL
is frozen at SIGTERM time (late writes that hit disk after SIGTERM are
ignored at scoring).

This file does no Lean work. Scoring lives in ``pipeline/marathon_score.py``.
"""
from __future__ import annotations

import collections
import json
import os
import shutil
import signal
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]


KILL_GRACE_SECONDS = 5.0

# Mirror Solo's ``judge.max_solver_bytes`` (500 KB). A single-file solver
# that exceeds this is rejected before launch — same contract as Solo,
# same value (memory: project_stage2_budgets).
SOLVER_MAX_BYTES = 500 * 1024

# Bounded I/O caps. A hostile or buggy solver could otherwise OOM the
# runner with stderr spam, fill the disk with answer-file noise, or
# trick the runner into reading a multi-GB manifest into memory.
#
#   _MAX_DRAIN_LINES_PER_STREAM — rolling tail of recent log lines per
#       stream. Old lines drop off the front of a deque as new ones
#       arrive. The runner only ever reports ``stderr_tail``, so a
#       short tail is sufficient for postmortem.
#   _MAX_DRAIN_LINE_BYTES       — per-line truncation, before the line
#       hits the deque. Stops a single multi-MB line from blowing the
#       memory bound.
#   _MAX_OUTPUT_BYTES           — answer-file size cap. The watchdog
#       polls and SIGTERMs with reason="output" if exceeded.
#   _MAX_MANIFEST_BYTES         — manifest read-into-memory cap.
_MAX_DRAIN_LINES_PER_STREAM = 512
_MAX_DRAIN_LINE_BYTES = 1024
_MAX_OUTPUT_BYTES = 50 * 1024 * 1024
_MAX_MANIFEST_BYTES = 50 * 1024 * 1024


@dataclass(frozen=True)
class MarathonRunResult:
    exit_code: int | None
    wall_seconds: float
    sigterm_fired: bool
    sigkill_fired: bool
    sigterm_reason: str | None  # "wall" | "tokens" | "output" | None
    tokens_used: int
    tokens_exhausted: bool
    stderr_tail: str
    output_path: Path
    manifest_path: Path
    scratch_dir: Path
    budget_seconds: float
    budget_tokens: int
    # Snapshot of the manifest as the runner read it before launching the
    # solver. Scoring uses this rather than re-reading the manifest off
    # disk, so a solver that overwrites JUDGE_MARATHON_MANIFEST cannot
    # poison the score path.
    manifest_problems: tuple[dict, ...] = ()


def _validate_solver_layout(submission_dir: Path) -> str | None:
    """Single-file contract — same rule as Solo: solver.py and nothing else."""
    try:
        entries = list(submission_dir.iterdir())
    except OSError as exc:
        return f"cannot read submission directory: {exc}"
    solver = submission_dir / "solver.py"
    extras = sorted(e.name for e in entries if e.name != "solver.py")
    if extras:
        return f"submission must contain only solver.py; found extras: {extras!r}"
    if not solver.exists():
        return "solver.py not found"
    if solver.is_symlink() or not solver.is_file():
        return "solver.py must be a regular file, not a symlink"
    try:
        size = solver.stat().st_size
    except OSError as exc:
        return f"cannot stat solver.py: {exc}"
    if size > SOLVER_MAX_BYTES:
        return (
            f"solver.py is {size} bytes, exceeds the {SOLVER_MAX_BYTES}-byte "
            f"limit (Solo reference)"
        )
    return None


def _wipe_dir(path: Path) -> None:
    if path.exists():
        shutil.rmtree(path, ignore_errors=True)
    path.mkdir(parents=True, exist_ok=True)


def _load_manifest_snapshot(manifest_path: Path) -> tuple[dict, ...]:
    """Read the manifest off disk *before* the solver starts.

    Supports both JSONL (one problem per line) and a top-level JSON list,
    matching the score module's loader. The returned tuple is the
    authoritative copy used by scoring; the solver only ever sees a writable
    copy under its scratch dir.

    Refuses manifests larger than ``_MAX_MANIFEST_BYTES``: organizer
    manifests are normally a few MB, and refusing earlier prevents an
    accidental 100 GB problem dump from being slurped into memory.
    """
    try:
        size = manifest_path.stat().st_size
    except OSError as exc:
        raise ValueError(f"{manifest_path}: cannot stat: {exc}") from exc
    if size > _MAX_MANIFEST_BYTES:
        raise ValueError(
            f"{manifest_path}: {size} bytes exceeds the "
            f"{_MAX_MANIFEST_BYTES}-byte manifest limit"
        )
    text = manifest_path.read_text(encoding="utf-8")
    stripped = text.lstrip()
    if not stripped:
        return ()
    if stripped[0] == "[":
        data = json.loads(text)
        if not isinstance(data, list):
            raise ValueError(f"{manifest_path}: top-level JSON must be a list")
        return tuple(data)
    out: list[dict] = []
    for lineno, raw in enumerate(text.splitlines(), 1):
        if not raw.strip():
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise ValueError(
                f"{manifest_path}:{lineno}: invalid JSONL ({exc})"
            ) from exc
        if not isinstance(obj, dict) or "id" not in obj:
            raise ValueError(
                f"{manifest_path}:{lineno}: expected problem dict with 'id'"
            )
        out.append(obj)
    return tuple(out)


def _write_manifest_copy(problems: tuple[dict, ...], dest: Path) -> None:
    """Write the snapshot back out as JSONL for the solver to read.

    Always JSONL regardless of the input format — solvers shouldn't have to
    handle two shapes, and a single canonical shape simplifies the contract.
    """
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open("w", encoding="utf-8") as fh:
        for prob in problems:
            fh.write(json.dumps(prob, ensure_ascii=False) + "\n")


# NOTE: real upstream API keys (OPENROUTER_API_KEY, DEEPSEEK_API_KEY,
# KIMI_API_KEY, …) are intentionally NOT forwarded into the solver
# subprocess. Marathon mode interposes a local HTTP proxy
# (``pipeline/marathon_proxy.py``) that holds the real key and enforces
# the token budget at the network layer. The solver only ever sees a
# 127.0.0.1 base URL plus a per-run shared secret as ``OPENAI_API_KEY``.
# This is the marathon analogue of the Solo ``pipeline/proxy.py``
# stdin/stdout mediation — same defensive posture, different I/O shape.

# Where the marathon-side helper module (marathon_llm.py) lives. The
# runner injects its parent directory into the solver's PYTHONPATH so
# ``from marathon_llm import call_llm`` works inside the solver.
_MARATHON_LIB_DIR = Path(__file__).resolve().parent


def _build_solver_env(
    *,
    manifest_path: Path,
    output_path: Path,
    scratch_dir: Path,
    budget_seconds: float,
    budget_tokens: int,
    proxy_base_url: str | None,
    proxy_api_key: str | None,
    extra_env: dict[str, str] | None = None,
) -> dict[str, str]:
    """Minimal env handed to the solver subprocess.

    Same allowlist philosophy as ``pipeline/proxy.py``: drop everything
    except the few vars Python and the OS actually need, then add the
    marathon contract vars. Real upstream API keys are NOT forwarded —
    if a proxy is running, ``OPENAI_BASE_URL`` and ``OPENAI_API_KEY`` are
    set to point the solver's OpenAI SDK at the local proxy instead.
    """
    allowed = ("PATH", "HOME", "USER", "LANG", "TERM", "TMPDIR",
               "PYTHONPATH", "PYTHONIOENCODING")
    env = {k: os.environ[k] for k in allowed if k in os.environ}
    env["PYTHONIOENCODING"] = "utf-8"
    env["PYTHONUNBUFFERED"] = "1"
    env["JUDGE_MARATHON_MANIFEST"] = str(manifest_path.resolve())
    env["JUDGE_MARATHON_OUTPUT"] = str(output_path.resolve())
    env["JUDGE_MARATHON_SCRATCH_DIR"] = str(scratch_dir.resolve())
    env["JUDGE_MARATHON_BUDGET_SECONDS"] = str(int(budget_seconds))
    env["JUDGE_MARATHON_BUDGET_TOKENS"] = str(int(budget_tokens))
    env["JUDGE_MARATHON_LIB_DIR"] = str(_MARATHON_LIB_DIR)
    # Make the helper importable without the solver having to munge sys.path.
    existing_pp = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_MARATHON_LIB_DIR}{os.pathsep}{existing_pp}" if existing_pp
        else str(_MARATHON_LIB_DIR)
    )
    if proxy_base_url and proxy_api_key:
        env["OPENAI_BASE_URL"] = proxy_base_url
        env["OPENAI_API_KEY"] = proxy_api_key
    if extra_env:
        for k, v in extra_env.items():
            env[k] = v
    return env


def run_marathon(
    *,
    submission_dir: str | Path,
    manifest_path: str | Path,
    output_path: str | Path,
    scratch_dir: str | Path,
    budget_seconds: float,
    budget_tokens: int,
    extra_env: dict[str, str] | None = None,
    enable_proxy: bool = True,
    log_stream=None,
    test_preseed_settled_tokens: int = 0,
    test_preseed_reserved_tokens: int = 0,
) -> MarathonRunResult:
    """Run a marathon solver subprocess under the given budgets.

    Returns when the solver exits cleanly OR when the wall-clock budget is
    exhausted (SIGTERM, then SIGKILL after grace). Either way the output
    file is left on disk for the score path.

    ``log_stream`` is an optional file-like object for live status lines
    (used by ``scripts/run_marathon.py``). Pass ``None`` for silent.
    """
    submission_dir = Path(submission_dir)
    manifest_path = Path(manifest_path)
    output_path = Path(output_path)
    scratch_dir = Path(scratch_dir)

    layout_err = _validate_solver_layout(submission_dir)
    if layout_err is not None:
        raise ValueError(f"marathon: invalid submission: {layout_err}")
    if not manifest_path.exists():
        raise FileNotFoundError(f"marathon: manifest not found: {manifest_path}")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    if output_path.exists():
        output_path.unlink()
    output_path.touch()

    _wipe_dir(scratch_dir)

    # The proxy's tokens-used telemetry file lives here, NOT under
    # ``scratch_dir``. The solver only sees ``JUDGE_MARATHON_SCRATCH_DIR``
    # in its env, so it has no path reference to this directory and
    # cannot tamper with the file the watchdog uses for authority. (In
    # fact the watchdog reads the in-memory counter via
    # ``proxy_handle.tokens_used()`` — the file is now write-only
    # telemetry — but keeping it out of scratch_dir prevents any future
    # confusion about the trust boundary.)
    proxy_state_dir = output_path.parent / "_proxy_state"
    _wipe_dir(proxy_state_dir)

    # Snapshot the manifest in-memory before launching the solver, then hand
    # the solver a *copy* under its scratch dir. Scoring uses the in-memory
    # snapshot, so a solver that overwrites JUDGE_MARATHON_MANIFEST cannot
    # poison the score path. The original manifest path is never exposed
    # to the solver.
    manifest_problems = _load_manifest_snapshot(manifest_path)
    solver_manifest_path = scratch_dir / "manifest.jsonl"
    _write_manifest_copy(manifest_problems, solver_manifest_path)

    # Start the local LLM proxy (if requested and an upstream key is
    # available). The proxy holds the upstream credentials so the solver
    # never sees them and refuses calls past the token budget.
    proxy_handle = None
    proxy_base_url: str | None = None
    proxy_api_key: str | None = None
    if enable_proxy:
        from pipeline.marathon_proxy import start_marathon_proxy
        try:
            proxy_handle = start_marathon_proxy(
                state_dir=proxy_state_dir,
                budget_tokens=budget_tokens,
                preseed_settled_tokens=int(test_preseed_settled_tokens),
                preseed_reserved_tokens=int(test_preseed_reserved_tokens),
            )
            proxy_base_url = proxy_handle.base_url
            proxy_api_key = proxy_handle.api_key
            if log_stream is not None:
                print(f"[marathon] proxy listening at {proxy_base_url}",
                      file=log_stream, flush=True)
        except RuntimeError as exc:
            # No upstream key configured. The run still proceeds; solvers
            # that try to call LLMs will fail loudly. This is expected for
            # brute-force-only tests and the offline harness.
            if log_stream is not None:
                print(f"[marathon] proxy disabled: {exc}",
                      file=log_stream, flush=True)

    env = _build_solver_env(
        manifest_path=solver_manifest_path,
        output_path=output_path,
        scratch_dir=scratch_dir,
        budget_seconds=budget_seconds,
        budget_tokens=budget_tokens,
        proxy_base_url=proxy_base_url,
        proxy_api_key=proxy_api_key,
        extra_env=extra_env,
    )

    if log_stream is not None:
        print(
            f"[marathon] launch solver={submission_dir.name} "
            f"manifest={manifest_path.name} "
            f"budget={int(budget_seconds)}s/{int(budget_tokens)}tok",
            file=log_stream, flush=True,
        )

    # Launch under its own process group so SIGTERM reaches descendants too
    # (a solver that spawns helpers should die with the parent).
    proc = subprocess.Popen(
        [sys.executable, "solver.py"],
        cwd=str(submission_dir.resolve()),
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )

    # Drain stdout/stderr in background threads so a chatty solver can't
    # deadlock on the kernel pipe buffer. Bounded with a deque + per-line
    # truncation so a hostile solver can't OOM the runner by streaming
    # gigabytes of stderr.
    stdout_lines: collections.deque[str] = collections.deque(
        maxlen=_MAX_DRAIN_LINES_PER_STREAM
    )
    stderr_lines: collections.deque[str] = collections.deque(
        maxlen=_MAX_DRAIN_LINES_PER_STREAM
    )
    stdout_lock = threading.Lock()
    stderr_lock = threading.Lock()

    def _drain(stream, sink, lock):
        # Chunked-read iterator. ``stream.readline()`` would buffer the
        # entire output up to the next ``\n``, so a hostile solver that
        # writes hundreds of MB without a newline could OOM the runner
        # *before* per-line truncation has any chance to run. We instead
        # read in fixed-size chunks and split on newlines manually,
        # truncating any partial line that exceeds the per-line cap.
        buf_limit = _MAX_DRAIN_LINE_BYTES
        chunk_size = 4096
        partial = ""
        try:
            while True:
                chunk = stream.read(chunk_size)
                if not chunk:
                    break
                partial += chunk
                # Emit complete lines.
                while "\n" in partial:
                    nl = partial.index("\n")
                    line = partial[: nl + 1]
                    partial = partial[nl + 1:]
                    if len(line) > buf_limit:
                        line = line[:buf_limit] + "...[truncated]\n"
                    with lock:
                        sink.append(line)
                    if log_stream is not None and stream is proc.stderr:
                        print(f"[marathon:stderr] {line.rstrip()}",
                              file=log_stream, flush=True)
                # If the partial line has grown past the cap, flush it
                # as a truncated line and drop the rest until we see a
                # newline. This prevents unbounded buffer growth on
                # newline-less streams.
                if len(partial) > buf_limit:
                    truncated = partial[:buf_limit] + "...[truncated]\n"
                    with lock:
                        sink.append(truncated)
                    if log_stream is not None and stream is proc.stderr:
                        print(f"[marathon:stderr] {truncated.rstrip()}",
                              file=log_stream, flush=True)
                    # Discard up to next newline (or up to next chunk).
                    if "\n" in partial:
                        partial = partial[partial.index("\n") + 1:]
                    else:
                        partial = ""
            # Stream closed; flush any final partial line.
            if partial:
                if len(partial) > buf_limit:
                    partial = partial[:buf_limit] + "...[truncated]"
                with lock:
                    sink.append(partial)
        except (OSError, ValueError):
            return
        finally:
            try:
                stream.close()
            except OSError:
                pass

    t_out = threading.Thread(
        target=_drain, args=(proc.stdout, stdout_lines, stdout_lock),
        daemon=True,
    )
    t_err = threading.Thread(
        target=_drain, args=(proc.stderr, stderr_lines, stderr_lock),
        daemon=True,
    )
    t_out.start()
    t_err.start()

    def _tokens_settled() -> int:
        # Settled-only counter. The watchdog deliberately ignores
        # in-flight reservations because a legal exact-budget reservation
        # transiently makes ``settled + reserved == cap`` — pre-fix the
        # watchdog observed that and SIGTERMed the solver mid-call. The
        # proxy's reserve_tokens() gate is the authoritative pre-flight
        # check; the watchdog only fires if billed cost has actually
        # exceeded budget (e.g., upstream returned more than reserved).
        if proxy_handle is None:
            return 0
        try:
            return int(proxy_handle.tokens_settled())
        except Exception:  # noqa: BLE001 — proxy already gone, treat as 0
            return 0

    t_start = time.monotonic()
    deadline = t_start + budget_seconds
    sigterm_fired = False
    sigkill_fired = False
    sigterm_reason: str | None = None

    # Budget semantics (must match marathon_proxy.reserve_tokens):
    #   cap > 0  → enforce normally
    #   cap == 0 → proxy denies all reservations; watchdog cannot
    #              meaningfully fire on tokens, so it stays disabled here
    #   cap < 0  → unlimited; watchdog never fires on tokens
    def _output_size() -> int:
        try:
            return int(output_path.stat().st_size)
        except OSError:
            return 0

    while True:
        rc = proc.poll()
        if rc is not None:
            break
        now = time.monotonic()
        wall_exceeded = now >= deadline
        tokens_exceeded = (
            budget_tokens > 0 and _tokens_settled() >= budget_tokens
        )
        output_exceeded = _output_size() > _MAX_OUTPUT_BYTES
        if wall_exceeded or tokens_exceeded or output_exceeded:
            sigterm_fired = True
            if wall_exceeded:
                sigterm_reason = "wall"
            elif tokens_exceeded:
                sigterm_reason = "tokens"
            else:
                sigterm_reason = "output"
            if log_stream is not None:
                if sigterm_reason == "output":
                    print(f"[marathon] output file exceeded "
                          f"{_MAX_OUTPUT_BYTES}-byte cap at "
                          f"{now - t_start:.1f}s — SIGTERM",
                          file=log_stream, flush=True)
                else:
                    print(f"[marathon] budget exhausted at "
                          f"{now - t_start:.1f}s ({sigterm_reason}) — SIGTERM",
                          file=log_stream, flush=True)
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            grace_end = now + KILL_GRACE_SECONDS
            while time.monotonic() < grace_end:
                if proc.poll() is not None:
                    break
                time.sleep(0.1)
            if proc.poll() is None:
                sigkill_fired = True
                if log_stream is not None:
                    print("[marathon] grace expired — SIGKILL",
                          file=log_stream, flush=True)
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                # Reap.
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
            break
        time.sleep(0.5)

    t_out.join(timeout=2)
    t_err.join(timeout=2)

    elapsed = time.monotonic() - t_start
    rc = proc.poll()

    # Snapshot the authoritative settled counter BEFORE the proxy is
    # shut down — accessor calls become unreliable post-stop(). The
    # final ``tokens_used`` reported in the run result is what the run
    # actually paid (settled), NOT the speculative effective total.
    final_tokens = _tokens_settled()
    tokens_exhausted = (
        budget_tokens > 0 and final_tokens >= budget_tokens
    )

    # Stop the proxy after the solver has exited so any in-flight LLM
    # call has a chance to finish; new connections get refused.
    if proxy_handle is not None:
        try:
            proxy_handle.stop(timeout=2.0)
        except Exception:  # noqa: BLE001
            pass

    # Defensive truncation. The output watchdog enforces ``_MAX_OUTPUT_BYTES``
    # on a ~0.5 s tick, but a hostile solver can catch SIGTERM and keep
    # writing through the 5 s grace window, growing the file past the cap.
    # The score path then ``read_text``s the whole file, so this is the
    # last chance to keep the runner's RSS bounded. We truncate at the
    # cap and accept that the byte-boundary cut may discard a partial
    # tail JSON line (the score parser already silently skips malformed
    # lines, so this falls into the existing semantics).
    try:
        if output_path.is_file() and not output_path.is_symlink():
            actual_size = output_path.stat().st_size
            if actual_size > _MAX_OUTPUT_BYTES:
                with output_path.open("r+b") as fh:
                    fh.truncate(_MAX_OUTPUT_BYTES)
                if log_stream is not None:
                    print(
                        f"[marathon] truncated output {actual_size} \u2192 "
                        f"{_MAX_OUTPUT_BYTES} bytes (grace-window overrun)",
                        file=log_stream, flush=True,
                    )
    except OSError:
        # If the path is gone, replaced, or unreadable, the score path
        # will treat it as empty — no further action needed here.
        pass

    with stderr_lock:
        stderr_tail = "".join(stderr_lines)[-8192:]

    if log_stream is not None:
        print(
            f"[marathon] exit rc={rc} wall={elapsed:.1f}s "
            f"sigterm={sigterm_fired} sigkill={sigkill_fired}",
            file=log_stream, flush=True,
        )

    return MarathonRunResult(
        exit_code=rc,
        wall_seconds=elapsed,
        sigterm_fired=sigterm_fired,
        sigkill_fired=sigkill_fired,
        sigterm_reason=sigterm_reason,
        tokens_used=final_tokens,
        tokens_exhausted=tokens_exhausted,
        stderr_tail=stderr_tail,
        output_path=output_path,
        manifest_path=manifest_path,
        scratch_dir=scratch_dir,
        budget_seconds=budget_seconds,
        budget_tokens=budget_tokens,
        manifest_problems=manifest_problems,
    )
