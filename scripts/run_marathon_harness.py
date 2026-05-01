"""
Marathon-mode harness: runs every case in tests/marathon_manifest.json and
asserts the documented behaviour. Exits 0 only when every case passes.

The Stage 2 harness (``scripts/run_harness.py``) is unchanged — this is a
parallel entry point so the marathon track has its own gate.

Usage:
    python3 scripts/run_marathon_harness.py
    python3 scripts/run_marathon_harness.py --filter token_kill,budget_kill
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tests" / "marathon_manifest.json"

sys.path.insert(0, str(ROOT))

from pipeline.marathon_runner import run_marathon  # noqa: E402
from pipeline.marathon_score import score_marathon  # noqa: E402


def _lean_available() -> bool:
    """True iff ``lean --version`` exits 0 in PATH. Used to gate Lean-dependent
    assertions; tests that don't need Lean still run without it."""
    try:
        rc = subprocess.run(
            ["lean", "--version"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            timeout=5,
        ).returncode
        return rc == 0
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError):
        return False


def _run_oversized_manifest_case(case: dict) -> tuple[bool, list[str]]:
    """Synthesize a >50 MB manifest and assert the runner rejects it.

    Mirrors the oversized-solver case shape: no real solver runs;
    ``run_marathon`` should raise ``ValueError`` containing the
    expected substring before launching the subprocess. This is the
    high-5 manifest-bound regression.
    """
    failures: list[str] = []
    a = case.get("assertions", {})
    expected_substr = a.get("expect_run_marathon_raises", "")

    with tempfile.TemporaryDirectory(prefix=f"marathon_{case['name']}_") as tmp:
        tmp_path = Path(tmp)
        # 51 MB of JSONL — one byte over the 50 MB cap. Each line is a
        # valid problem-shaped object; the test only cares that the
        # runner trips the size cap before reading.
        manifest_path = tmp_path / "huge.jsonl"
        line = json.dumps({
            "id": "x", "eq1_id": 1, "eq2_id": 2,
            "equation1": "G * G = G", "equation2": "G * G = G",
        }) + "\n"
        target_size = 50 * 1024 * 1024 + 1024
        with manifest_path.open("w", encoding="utf-8") as fh:
            written = 0
            while written < target_size:
                fh.write(line)
                written += len(line)

        output = tmp_path / "answers.jsonl"
        scratch = tmp_path / "scratch"
        submission = ROOT / case["submission_path"]

        raised: Exception | None = None
        try:
            run_marathon(
                submission_dir=submission,
                manifest_path=manifest_path,
                output_path=output,
                scratch_dir=scratch,
                budget_seconds=float(case["budget_seconds"]),
                budget_tokens=int(case["budget_tokens"]),
            )
        except ValueError as exc:
            raised = exc
        except Exception as exc:  # noqa: BLE001
            failures.append(
                f"expected ValueError from run_marathon, got "
                f"{type(exc).__name__}: {exc}"
            )
            return False, failures

        if raised is None:
            failures.append(
                "run_marathon accepted an oversized manifest; "
                "expected ValueError"
            )
        elif expected_substr and expected_substr not in str(raised):
            failures.append(
                f"ValueError message {str(raised)!r} did not contain "
                f"expected substring {expected_substr!r}"
            )

    return (not failures), failures


def _run_oversized_solver_case(case: dict) -> tuple[bool, list[str]]:
    """Synthesize a 500_001-byte solver.py and assert the runner rejects it.

    No solver actually runs. ``run_marathon`` should raise ValueError
    with a message containing the assertion's expected substring before
    the subprocess is spawned. This is the high-4 size-cap regression.
    """
    failures: list[str] = []
    a = case.get("assertions", {})
    expected_substr = a.get("expect_run_marathon_raises", "")

    with tempfile.TemporaryDirectory(prefix=f"marathon_{case['name']}_") as tmp:
        tmp_path = Path(tmp)
        sub_dir = tmp_path / "sub"
        sub_dir.mkdir()
        solver_py = sub_dir / "solver.py"
        # 500_001 bytes — exactly one byte over the 500 KB cap. A
        # comment + padding so the file is technically valid Python.
        header = b"# oversized fixture\npass\n"
        target_size = 500 * 1024 + 1
        padding = b"#" * (target_size - len(header))
        solver_py.write_bytes(header + padding)

        output = tmp_path / "answers.jsonl"
        scratch = tmp_path / "scratch"

        raised: Exception | None = None
        try:
            run_marathon(
                submission_dir=sub_dir,
                manifest_path=ROOT / case["manifest"],
                output_path=output,
                scratch_dir=scratch,
                budget_seconds=float(case["budget_seconds"]),
                budget_tokens=int(case["budget_tokens"]),
            )
        except ValueError as exc:
            raised = exc
        except Exception as exc:  # noqa: BLE001
            failures.append(
                f"expected ValueError from run_marathon, got "
                f"{type(exc).__name__}: {exc}"
            )
            return False, failures

        if raised is None:
            failures.append(
                "run_marathon accepted an oversized solver.py "
                f"({500 * 1024 + 1} bytes); expected ValueError"
            )
        elif expected_substr and expected_substr not in str(raised):
            failures.append(
                f"ValueError message {str(raised)!r} did not contain "
                f"expected substring {expected_substr!r}"
            )

    return (not failures), failures


def _run_case(case: dict, lean_ok: bool) -> tuple[bool, list[str]]:
    """Execute one case; return (passed, failure_messages)."""
    import os as _os
    failures: list[str] = []

    # Special path: ``synthesize_oversized_solver`` builds a 500_001-byte
    # solver.py in a temp dir and asserts that ``run_marathon`` rejects
    # it before launch. This case has no submission_path on disk; the
    # generated path replaces it.
    if case.get("synthesize_oversized_solver"):
        return _run_oversized_solver_case(case)
    if case.get("synthesize_oversized_manifest"):
        return _run_oversized_manifest_case(case)

    submission = ROOT / case["submission_path"]
    manifest = ROOT / case["manifest"]
    repeat = int(case.get("repeat", 1))

    scores: list[int] = []
    last_run = None
    last_summary = None
    last_output_text = ""

    for run_idx in range(repeat):
        with tempfile.TemporaryDirectory(prefix=f"marathon_{case['name']}_") as tmp:
            tmp_path = Path(tmp)
            output = tmp_path / "answers.jsonl"
            scratch = tmp_path / "scratch"

            for name in case.get("scratch_pre_populate", []):
                scratch.mkdir(parents=True, exist_ok=True)
                (scratch / name).write_bytes(b"x")

            inject = case.get("inject_runner_env", {}) or {}
            saved_env: dict[str, str | None] = {}
            for k, v in inject.items():
                saved_env[k] = _os.environ.get(k)
                _os.environ[k] = str(v)

            try:
                run = run_marathon(
                    submission_dir=submission,
                    manifest_path=manifest,
                    output_path=output,
                    scratch_dir=scratch,
                    budget_seconds=float(case["budget_seconds"]),
                    budget_tokens=int(case["budget_tokens"]),
                    test_preseed_settled_tokens=int(
                        case.get("preseed_settled_tokens", 0)
                    ),
                    test_preseed_reserved_tokens=int(
                        case.get("preseed_reserved_tokens", 0)
                    ),
                )
            finally:
                for k, prev in saved_env.items():
                    if prev is None:
                        _os.environ.pop(k, None)
                    else:
                        _os.environ[k] = prev
            summary = score_marathon(
                manifest_path=manifest,
                manifest_problems=run.manifest_problems,
                output_path=output,
                wall_seconds=run.wall_seconds,
                sigterm_fired=run.sigterm_fired,
                sigkill_fired=run.sigkill_fired,
                tokens_used=run.tokens_used,
                tokens_exhausted=run.tokens_exhausted,
            )
            scores.append(summary.score)
            last_run = run
            last_summary = summary
            # Capture output content before the temp dir is cleaned up.
            try:
                last_output_text = output.read_text(encoding="utf-8")
            except OSError:
                last_output_text = ""

    a = case.get("assertions", {})

    def fail(msg: str):
        failures.append(msg)

    if "exit_code_in" in a and last_run is not None:
        if last_run.exit_code not in a["exit_code_in"]:
            fail(f"exit_code={last_run.exit_code} not in {a['exit_code_in']}")
    if "sigterm_fired" in a and last_run is not None:
        if bool(last_run.sigterm_fired) != bool(a["sigterm_fired"]):
            fail(f"sigterm_fired={last_run.sigterm_fired} expected={a['sigterm_fired']}")
    if "sigterm_reason" in a and last_run is not None:
        if last_run.sigterm_reason != a["sigterm_reason"]:
            fail(f"sigterm_reason={last_run.sigterm_reason!r} expected={a['sigterm_reason']!r}")
    if "max_wall_seconds" in a and last_run is not None:
        if last_run.wall_seconds > float(a["max_wall_seconds"]):
            fail(f"wall_seconds={last_run.wall_seconds:.1f} > {a['max_wall_seconds']}")
    if "tokens_exhausted" in a and last_run is not None:
        if bool(last_run.tokens_exhausted) != bool(a["tokens_exhausted"]):
            fail(f"tokens_exhausted={last_run.tokens_exhausted} expected={a['tokens_exhausted']}")
    if "min_settled_tokens" in a and last_run is not None:
        if int(last_run.tokens_used) < int(a["min_settled_tokens"]):
            fail(
                f"settled tokens_used={last_run.tokens_used} < "
                f"min_settled_tokens={a['min_settled_tokens']}"
            )
    if "max_stderr_tail_bytes" in a and last_run is not None:
        # Bounded I/O: even a chatty solver must leave the runner with a
        # capped stderr tail. The deque has 512 entries × 1024-byte
        # truncation = ~512 KB upper bound; tests typically expect
        # ≤ 64 KB to assert the bound is meaningful.
        actual = len(last_run.stderr_tail.encode("utf-8", errors="replace"))
        if actual > int(a["max_stderr_tail_bytes"]):
            fail(
                f"stderr_tail is {actual} bytes, > "
                f"max_stderr_tail_bytes={a['max_stderr_tail_bytes']}"
            )
    if "max_output_bytes_after_run" in a and last_run is not None:
        # Bounded I/O: a solver that catches SIGTERM and floods output
        # during the 5 s grace window must end up truncated by the
        # runner before scoring reads the file.
        try:
            actual = last_run.output_path.stat().st_size
        except OSError:
            actual = 0
        if actual > int(a["max_output_bytes_after_run"]):
            fail(
                f"output_path is {actual} bytes after run, > "
                f"max_output_bytes_after_run={a['max_output_bytes_after_run']}"
            )
    if "score" in a and last_summary is not None:
        if last_summary.score != int(a["score"]):
            fail(f"score={last_summary.score} expected={a['score']}")
    if "not_attempted" in a and last_summary is not None:
        if last_summary.not_attempted != int(a["not_attempted"]):
            fail(f"not_attempted={last_summary.not_attempted} expected={a['not_attempted']}")
    if "by_status_min" in a and last_summary is not None:
        for status, minimum in a["by_status_min"].items():
            actual = last_summary.by_status.get(status, 0)
            if actual < int(minimum):
                fail(f"by_status[{status}]={actual} < {minimum}")
    if "min_score_with_lean" in a and last_summary is not None and lean_ok:
        if last_summary.score < int(a["min_score_with_lean"]):
            fail(f"score={last_summary.score} < min_score_with_lean={a['min_score_with_lean']}")
    if a.get("scores_must_match_across_runs"):
        if len(set(scores)) != 1:
            fail(f"scores not deterministic across runs: {scores}")

    if a.get("scratch_was_empty"):
        probe = None
        for line in last_output_text.splitlines():
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(obj, dict) and obj.get("id") == "anti_persist_probe":
                probe = obj
                break
        if probe is None:
            fail("anti_persist probe line not found")
        elif probe.get("scratch_entries"):
            fail(f"scratch was not empty at start: {probe['scratch_entries']!r}")

    if a.get("key_isolation_holds"):
        probe = None
        for line in last_output_text.splitlines():
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(obj, dict) and obj.get("id") == "key_isolation_probe":
                probe = obj
                break
        if probe is None:
            fail("key_isolation probe line not found")
        else:
            leaked = probe.get("leaked_upstream_keys") or []
            if leaked:
                fail(f"raw upstream keys leaked into solver env: {leaked}")
            # When the harness injects a fake OPENROUTER_API_KEY, the proxy
            # must start; verify the solver sees a loopback base url and a
            # proxy-issued OPENAI_API_KEY (not the raw upstream key).
            if probe.get("openai_base_url_present"):
                if not probe.get("openai_base_url_is_loopback"):
                    fail("OPENAI_BASE_URL in solver env is not loopback")
                if not probe.get("openai_api_key_present"):
                    fail("OPENAI_API_KEY missing from solver env (proxy not wired)")
            else:
                fail("OPENAI_BASE_URL not set in solver env "
                     "(proxy did not start despite injected upstream key)")

    if a.get("output_contains_post_sigterm_line"):
        # We can detect this by seeing two writes for the same id.
        ids = []
        for line in last_output_text.splitlines():
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(obj, dict) and "id" in obj:
                ids.append(obj["id"])
        if len(ids) < 2 or ids[0] != ids[-1]:
            fail(f"expected ≥2 writes for same id, got {ids}")

    if a.get("score_uses_last_write") and last_summary is not None:
        # late_writer's last write is a malformed 'false' / "(post-SIGTERM late write)".
        # That is not a verifiable Lean cert, so the result must not be 'accepted'.
        for r in last_summary.per_problem:
            if r.id == "normal_0003" and r.status == "accepted":
                fail(
                    "late_writer: score_uses_last_write expected last malformed line "
                    "to NOT produce 'accepted'; got accepted"
                )

    if a.get("score_used_last_line_only") and last_summary is not None:
        # duplicate_id writes a malformed line, then a real false cert. The
        # last (real) cert should be what scoring used; status should not
        # be 'malformed' for normal_0003.
        for r in last_summary.per_problem:
            if r.id == "normal_0003" and r.status == "malformed":
                fail("duplicate_id: score used FIRST malformed line instead of last real cert")

    if a.get("over_budget_pre_check_holds"):
        # over_budget_call fixture writes a marker line describing what
        # the proxy returned. Assert: the SDK saw a 402 status code
        # (i.e., the reservation pattern rejected the call before the
        # proxy forwarded upstream). Pre-fix this would have been a 200
        # because settled-only consumption was below budget.
        probe = None
        for line in last_output_text.splitlines():
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(obj, dict) and obj.get("id") == "over_budget_call_probe":
                probe = obj
                break
        if probe is None:
            fail("over_budget_call probe line not found")
        elif not probe.get("got_402"):
            fail(
                "expected proxy to reject with HTTP 402; "
                f"got status_code={probe.get('status_code')!r} "
                f"error={probe.get('error')!r}"
            )

    if a.get("multipart_prompt_holds"):
        # multipart_prompt_probe makes two calls:
        #   1. text-only multipart with ~50k chars → must 402 (the
        #      prompt-estimate must walk the parts list, not call
        #      ``len()`` on it).
        #   2. image_url part → must 400 (validator rejects non-text).
        probe = None
        for line in last_output_text.splitlines():
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(obj, dict) and obj.get("id") == "multipart_prompt_probe":
                probe = obj
                break
        if probe is None:
            fail("multipart_prompt probe line not found")
        else:
            if probe.get("text_parts_status") != 402:
                fail(
                    "multipart text prompt was not budget-checked; "
                    f"status={probe.get('text_parts_status')!r} "
                    f"error={probe.get('text_parts_error')!r}"
                )
            if probe.get("image_part_status") != 400:
                fail(
                    "non-text content part was not rejected by the "
                    f"validator; status={probe.get('image_part_status')!r} "
                    f"error={probe.get('image_part_error')!r}"
                )

    if a.get("zero_budget_holds"):
        # zero_budget_probe asserts both rejection paths fire when
        # budget_tokens=0:
        #   1. marathon_llm.call_llm returns an error string; no
        #      "response" field is set.
        #   2. A direct OpenAI SDK call hits the proxy's 402 deny path.
        # Pre-fix the proxy treated `cap == 0` as "unlimited" via a
        # truthy-check shortcut, so this same probe would have produced
        # a 200 (or a network error) instead of a 402.
        probe = None
        for line in last_output_text.splitlines():
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(obj, dict) and obj.get("id") == "zero_budget_probe":
                probe = obj
                break
        if probe is None:
            fail("zero_budget probe line not found")
        else:
            if probe.get("helper_response_present"):
                fail(
                    "marathon_llm.call_llm returned a response under "
                    "budget_tokens=0; helper preemption broken"
                )
            if not probe.get("helper_error"):
                fail("marathon_llm.call_llm did not return an error string")
            if not probe.get("got_402"):
                fail(
                    "expected proxy to reject with HTTP 402 for cap==0; "
                    f"got status_code={probe.get('status_code')!r} "
                    f"error={probe.get('error')!r}"
                )

    if a.get("score_uses_original_manifest") and last_summary is not None:
        # manifest_mutator overwrites the on-disk manifest with a single
        # 'hijacked_id' problem. Scoring must score the original ids, not
        # the hijacked one — so per_problem must contain normal_0001..0005
        # and must NOT contain hijacked_id.
        ids = [r.id for r in last_summary.per_problem]
        expected = ["normal_0001", "normal_0002", "normal_0003",
                    "normal_0004", "normal_0005"]
        if ids != expected:
            fail(f"manifest_mutation: scored ids={ids} expected={expected}")
        if "hijacked_id" in ids:
            fail("manifest_mutation: scoring credited the hijacked id")

    return (not failures), failures


def main() -> int:
    parser = argparse.ArgumentParser(description="Marathon-mode harness")
    parser.add_argument("--filter", default=None,
                        help="Comma-separated list of case names to run (default: all)")
    parser.add_argument("--manifest", default=str(MANIFEST),
                        help="Path to marathon manifest JSON")
    args = parser.parse_args()

    manifest = json.loads(Path(args.manifest).read_text(encoding="utf-8"))
    cases = manifest["cases"]
    if args.filter:
        wanted = set(s.strip() for s in args.filter.split(",") if s.strip())
        cases = [c for c in cases if c["name"] in wanted]

    lean_ok = _lean_available()
    print(f"Marathon harness — {len(cases)} cases, Lean available: {lean_ok}")
    print()

    passed = 0
    failed = 0

    # Regression: marathon_llm.py must import cleanly. Solver fixtures
    # routinely catch the import in try/except (so they can record helper
    # errors as data), which can mask SyntaxError-class regressions in
    # the helper module. A direct import smoke is the cheapest fence.
    helper_name = "marathon_llm.imports"
    try:
        import importlib
        helper = importlib.import_module("pipeline.marathon_llm")
        for attr in ("call_llm", "budget_remaining", "tokens_used"):
            if not callable(getattr(helper, attr, None)):
                raise AttributeError(f"pipeline.marathon_llm.{attr} missing or not callable")
        print(f"  [PASS] {helper_name}")
        passed += 1
    except Exception as exc:  # noqa: BLE001 — cover SyntaxError + ImportError + AttributeError
        print(f"  [FAIL] {helper_name}")
        print(f"         - {type(exc).__name__}: {exc}")
        failed += 1

    for case in cases:
        ok, fails = _run_case(case, lean_ok)
        tag = "PASS" if ok else "FAIL"
        print(f"  [{tag}] {case['name']}")
        if not ok:
            failed += 1
            for msg in fails:
                print(f"         - {msg}")
        else:
            passed += 1

    print()
    print(f"Marathon harness: {passed} passed, {failed} failed (Lean: {'on' if lean_ok else 'off'})")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
