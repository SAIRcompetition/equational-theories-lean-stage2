"""
Marathon-mode solver-side LLM helper.

This module is imported BY THE SOLVER subprocess in marathon mode. It is
not part of any solver's submission directory — it lives in the repo and
the marathon runner adds its parent directory to the solver's
``PYTHONPATH`` via the ``JUDGE_MARATHON_LIB_DIR`` env var. From the solver:

    import os, sys
    sys.path.insert(0, os.environ["JUDGE_MARATHON_LIB_DIR"])
    from marathon_llm import call_llm

    resp = call_llm("hello", config={"model": "openai/gpt-oss-120b", ...})
    if "error" in resp:
        ...
    text = resp["response"]
    tokens_left = resp["budget_remaining"]

In production the runner starts a local HTTP proxy
(``pipeline/marathon_proxy.py``) and sets ``OPENAI_BASE_URL`` /
``OPENAI_API_KEY`` so this helper's OpenAI SDK call lands on the proxy.
The proxy holds the real upstream credentials and is the sole authority
for the running token total. After each successful call the proxy
returns the running total in the response body and the
``X-Marathon-Tokens-Used-Total`` response header; this helper caches the
last-seen value so ``tokens_used()`` and ``budget_remaining()`` keep
working between calls without any file I/O. There is no longer a
solver-readable ``tokens_used.txt`` — even a solver that bypasses this
helper and uses the OpenAI SDK directly still goes through the proxy
and gets metered.
"""
from __future__ import annotations

import json
import os
import time
from typing import Any


# Crude prompt-token estimate when the upstream doesn't return ``usage`` —
# used only to compute a pessimistic ``budget_remaining``. Real cost lands
# on the next call when ``usage`` is available.
_CHARS_PER_TOKEN_FALLBACK = 4

# Cached running total. Updated from each successful proxy response
# (response body or ``X-Marathon-Tokens-Used-Total`` header). The proxy
# in-memory counter is the single authority — this is just the most
# recent value the helper has observed. Initial value is 0; before any
# call has returned, callers see 0 used.
_last_seen_tokens_total: int = 0


def _budget_cap() -> int:
    """Read the global LLM token cap from env.

    Three semantics, kept in sync with ``marathon_proxy.reserve_tokens``:

      * ``cap > 0``  — finite budget, enforce normally.
      * ``cap == 0`` — zero budget, deny every LLM call.
      * ``cap < 0``  — unlimited (organizer probe / harness convenience).

    The default when the env var is missing is 0 (deny) rather than -1
    (unlimited) so an accidental ``unset JUDGE_MARATHON_BUDGET_TOKENS``
    fails closed: the helper refuses to call instead of silently going
    unmetered.
    """
    return int(os.environ.get("JUDGE_MARATHON_BUDGET_TOKENS", "0"))


def tokens_used() -> int:
    """Public read-only accessor for the most recently observed running total.

    Updated from each ``call_llm`` response. Between calls this lags the
    proxy's authoritative counter; for an exact value, inspect the
    ``tokens_used_total`` field of the last call's response.
    """
    return _last_seen_tokens_total


def budget_remaining() -> int:
    """Tokens left under ``JUDGE_MARATHON_BUDGET_TOKENS`` minus tokens already spent.

    Returns ``-1`` for the unlimited case (``cap < 0``); this is a
    sentinel, not a real count, and callers that bound their behaviour
    on ``budget_remaining`` must treat negatives as "no cap".
    """
    cap = _budget_cap()
    if cap < 0:
        return -1
    if cap == 0:
        return 0
    return max(0, cap - _last_seen_tokens_total)


def _estimate_prompt_tokens(prompt: str) -> int:
    return max(1, len(prompt) // _CHARS_PER_TOKEN_FALLBACK)


def _is_openrouter_base_url(base_url: str) -> bool:
    from urllib.parse import urlparse
    try:
        host = (urlparse(base_url).hostname or "").lower()
    except (ValueError, TypeError):
        return False
    return host == "openrouter.ai" or host.endswith(".openrouter.ai")


def call_llm(
    prompt: str,
    *,
    config: dict | None = None,
    max_seconds: float | None = None,
) -> dict[str, Any]:
    """Issue one LLM call under the marathon token budget.

    ``config`` is an optional override dict matching the ``llm`` block of
    ``pipeline/config.json`` (model / base_url / api_key_env /
    max_output_tokens / temperature / provider / reasoning_effort). When
    omitted, defaults are resolved from env vars and Stage 2 reference
    values, so the helper works out of the box for solvers that just want
    to call ``call_llm("...")``.

    Return shape:
        success → {"response": str, "tokens_used_call": int,
                   "tokens_used_total": int, "budget_remaining": int,
                   "truncated": bool (optional)}
        error   → {"error": str, "budget_remaining": int}
    """
    global _last_seen_tokens_total

    cfg = dict(config or {})
    model = cfg.get("model") or os.environ.get("JUDGE_MARATHON_MODEL", "openai/gpt-oss-120b")
    # In production these point at the marathon proxy. The runner refuses
    # to forward real upstream API keys into the solver subprocess, so
    # OPENROUTER_API_KEY etc. are not consulted here.
    base_url = (
        cfg.get("base_url")
        or os.environ.get("OPENAI_BASE_URL")
        or "https://openrouter.ai/api/v1"
    )
    api_key = cfg.get("api_key") or os.environ.get("OPENAI_API_KEY") or ""
    if not api_key:
        return {"error": "OPENAI_API_KEY not set (marathon proxy unreachable?)",
                "budget_remaining": budget_remaining()}

    cap = _budget_cap()
    used = _last_seen_tokens_total
    # Budget gate. Three branches mirror ``_budget_cap`` semantics:
    #   cap == 0  → deny every call
    #   cap > 0   → enforce against the cap
    #   cap < 0   → unlimited; skip the headroom check
    if cap == 0:
        return {"error": "token budget is zero — no LLM calls allowed",
                "budget_remaining": 0}
    if cap > 0 and used >= cap:
        return {"error": "token budget exhausted", "budget_remaining": 0}

    estimated = _estimate_prompt_tokens(prompt)
    max_out = int(cfg.get("max_output_tokens", 4096))
    # Refuse if even the cheapest possible response would blow the budget.
    if cap > 0 and (used + estimated + max_out) > cap:
        return {"error": "token budget would be exhausted by this call",
                "budget_remaining": budget_remaining()}

    try:
        from openai import OpenAI
        import openai
    except ImportError as exc:
        return {"error": f"openai SDK not installed: {exc}",
                "budget_remaining": budget_remaining()}

    http_timeout = float(cfg.get("http_timeout_seconds", 600.0))
    if max_seconds is not None:
        http_timeout = min(http_timeout, float(max_seconds))
    http_timeout = max(1.0, http_timeout)

    extra_body: dict[str, Any] = {}
    if _is_openrouter_base_url(base_url):
        if cfg.get("provider"):
            extra_body["provider"] = {"order": [cfg["provider"]]}
        if cfg.get("reasoning_effort"):
            extra_body["reasoning"] = {"effort": cfg["reasoning_effort"]}

    client = OpenAI(api_key=api_key, base_url=base_url, timeout=http_timeout)
    kwargs: dict[str, Any] = {
        "model": model,
        "messages": [{"role": "user", "content": prompt}],
        "max_tokens": max_out,
        "temperature": float(cfg.get("temperature", 0.0)),
    }
    if cfg.get("use_seed") and "seed" in cfg:
        kwargs["seed"] = cfg["seed"]
    if extra_body:
        kwargs["extra_body"] = extra_body

    t0 = time.monotonic()
    try:
        completion = client.chat.completions.create(**kwargs)
    except openai.APITimeoutError:
        return {"error": f"LLM request timed out ({http_timeout:.0f}s)",
                "budget_remaining": budget_remaining()}
    except openai.APIError as e:
        return {"error": f"LLM API error: {e}",
                "budget_remaining": budget_remaining()}
    except Exception as e:  # noqa: BLE001 — SDK raises many shapes
        return {"error": f"LLM call failed: {type(e).__name__}: {e}",
                "budget_remaining": budget_remaining()}
    _ = time.monotonic() - t0

    try:
        choice = completion.choices[0]
        message = choice.message
    except (AttributeError, IndexError, TypeError) as e:
        return {"error": f"LLM response parse error: {e}",
                "budget_remaining": budget_remaining()}
    finish_reason = getattr(choice, "finish_reason", None)
    content = getattr(message, "content", None)
    truncated = False
    if not content:
        content = (
            getattr(message, "reasoning", None)
            or getattr(message, "reasoning_content", None)
            or ""
        )
        if finish_reason == "length":
            truncated = True

    usage = getattr(completion, "usage", None)
    total_tokens = getattr(usage, "total_tokens", None) if usage else None
    if total_tokens is None:
        total_tokens = estimated + _estimate_prompt_tokens(content or "")

    # The proxy reports its post-call running total in the response body
    # (parsed below) and via the ``X-Marathon-Tokens-Used-Total`` header
    # (not surfaced through the SDK; we approximate by adding this
    # call's usage to our cached value). The proxy in-memory counter
    # remains the single authority — this cache is only the most-recent
    # value the helper has observed.
    _last_seen_tokens_total = _last_seen_tokens_total + int(total_tokens)
    new_total = _last_seen_tokens_total

    if cap < 0:
        remaining: int | None = -1
    elif cap == 0:
        remaining = 0
    else:
        remaining = max(0, cap - new_total)
    out: dict[str, Any] = {
        "response": content,
        "tokens_used_call": int(total_tokens),
        "tokens_used_total": new_total,
        "budget_remaining": remaining,
    }
    if truncated:
        out["truncated"] = True
    return out
