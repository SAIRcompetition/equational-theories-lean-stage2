from __future__ import annotations

import ast
import inspect
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "tests" / "harness_manifest.json"
ARTIFACT_PARENT = ROOT / ".artifacts" / "harness"
CHALLENGER_ARTIFACT_PARENT = ROOT / ".artifacts" / "challenger"
# Per-run scratch dirs reassigned by main() — concurrent harness invocations
# (CI runners, an agent re-running the gate while another shell still has it
# open) used to race on rmtree/mkdir of these paths and corrupt each other's
# Lean artifact files mid-flight (one observed symptom: ``unknown module
# prefix JudgeProblem`` after the partner cleared the dir). The bare-dir
# values here are placeholders; ``main`` substitutes a per-PID mkdtemp.
ARTIFACT_ROOT = ARTIFACT_PARENT
CHALLENGER_ARTIFACT_ROOT = CHALLENGER_ARTIFACT_PARENT

sys.path.insert(0, str(ROOT))

from judge import verify as _verify_module  # noqa: E402
from judge.verify import (  # noqa: E402
    BANNED_PROOF_TOKENS,
    MAX_CODE_LENGTH,
    JudgeConfigurationError,
    JudgeInfrastructureError,
    JudgeConfig,
    verify_answer,
    _find_banned_token,
    _equation_def,
    _normalize_equation_text,
    _render_problem_source,
    _resolve_config,
    _strip_paths,
)
from judge.challenger import run_challenger_suite  # noqa: E402
from pipeline import proxy as _proxy  # noqa: E402
from pipeline.proxy import (  # noqa: E402
    DEFAULT_SANDBOX_CONFIG,
    MAX_STDOUT_LINE_CHARS,
    _build_solver_argv,
    _load_prompt_template,
    _solver_subprocess_env,
    _validate_submission_layout,
    load_config,
    run_solver,
)


def load_manifest() -> dict[str, Any]:
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def stable_projection(result: dict[str, Any]) -> dict[str, Any]:
    return {
        "status": result["status"],
        "error_code": result["error_code"],
        "message": result["message"],
        "verdict": result.get("verdict"),
        "direct_declarations": result.get("direct_declarations", []),
        "axioms": result.get("axioms", []),
        "stdout": result.get("stdout", ""),
        "stderr": result.get("stderr", ""),
    }


def run_case(case: dict[str, Any], config: JudgeConfig) -> dict[str, Any]:
    problem_path = ROOT / case["problem_path"]
    answer_path = ROOT / case["answer_path"]
    problem = json.loads(problem_path.read_text(encoding="utf-8"))
    raw_answer = answer_path.read_text(encoding="utf-8")
    result = verify_answer(problem, raw_answer, config=config)
    ok = result["status"] == case["expected_status"]
    if "expected_error_code" in case:
        ok = ok and result["error_code"] == case["expected_error_code"]
    return {
        "name": case["name"],
        "expected_status": case["expected_status"],
        "expected_error_code": case.get("expected_error_code"),
        "result": stable_projection(result),
        "ok": ok,
    }


def run_repeatability(case: dict[str, Any], config: JudgeConfig, runs: int) -> dict[str, Any]:
    projections = [run_case(case, config)["result"] for _ in range(runs)]
    ok = all(projection == projections[0] for projection in projections[1:])
    return {
        "name": case["name"],
        "runs": runs,
        "ok": ok,
        "first": projections[0],
        "all_equal": ok,
    }


def run_cases(cases: list[dict[str, Any]], config: JudgeConfig) -> list[dict[str, Any]]:
    return [run_case(case, config) for case in cases]


def run_pipeline_prompt_cases() -> list[dict[str, Any]]:
    """Regression tests for pipeline.proxy._load_prompt_template resolution."""
    results: list[dict[str, Any]] = []

    def _record(name: str, ok: bool, detail: str = "") -> None:
        results.append({"name": name, "ok": ok, "detail": detail})

    # Every bundled Solo demo must ship as a single file: a non-empty PROMPT
    # with placeholder tokens, and no stray prompt.txt alongside.
    demo_names = [
        "baseline",
        "twophase",
        "opnorm",
    ]
    all_ok = True
    drift: list[str] = []
    for name in demo_names:
        d = ROOT / "examples" / "solo" / "demos" / name
        loaded_demo = _load_prompt_template(d)
        if not loaded_demo or "{problem." not in loaded_demo:
            all_ok = False
            drift.append(f"{name}: missing or placeholder-less PROMPT")
        if (d / "prompt.txt").exists():
            all_ok = False
            drift.append(f"{name}: stray prompt.txt present (single-file only)")
    _record(
        "pipeline_prompt_singlefile_ast",
        all_ok,
        "" if all_ok else "; ".join(drift),
    )

    # A stray prompt.txt next to solver.py must be ignored: the loader is
    # single-entry (solver.py PROMPT). If this test flips, the proxy has
    # regrown a legacy fallback and the contract has silently split.
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "prompt.txt").write_text("SHOULD_BE_IGNORED", encoding="utf-8")
        (tmp_path / "solver.py").write_text('PROMPT = "FROM_SOLVER"\n', encoding="utf-8")
        ignored = _load_prompt_template(tmp_path)
        _record(
            "pipeline_prompt_txt_sibling_is_ignored",
            ignored == "FROM_SOLVER",
            "" if ignored == "FROM_SOLVER" else f"prompt.txt was not ignored: got {ignored!r}",
        )

    with tempfile.TemporaryDirectory() as tmp:
        empty = _load_prompt_template(Path(tmp))
        _record(
            "pipeline_prompt_empty_dir_returns_empty",
            empty == "",
            "" if empty == "" else f"expected empty string, got {empty!r}",
        )

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text("x = 1\n", encoding="utf-8")
        no_prompt = _load_prompt_template(tmp_path)
        _record(
            "pipeline_prompt_solver_without_PROMPT_returns_empty",
            no_prompt == "",
            "" if no_prompt == "" else f"expected empty string, got {no_prompt!r}",
        )

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text('PROMPT = f"dynamic {1}"\n', encoding="utf-8")
        dynamic = _load_prompt_template(tmp_path)
        _record(
            "pipeline_prompt_fstring_not_supported_returns_empty",
            dynamic == "",
            "" if dynamic == "" else f"expected empty string, got {dynamic!r}",
        )

    # First-wins: earliest top-level PROMPT assignment is what we extract.
    # Later reassignments at module level are ignored on purpose so an
    # attacker cannot prepend a decoy literal then swap it out below.
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text(
            'PROMPT = "first"\nPROMPT = "second"\n', encoding="utf-8",
        )
        first = _load_prompt_template(tmp_path)
        _record(
            "pipeline_prompt_first_top_level_assignment_wins",
            first == "first",
            "" if first == "first" else f"expected 'first', got {first!r}",
        )

    # Nested-scope isolation: a PROMPT defined inside a function or class
    # must never be lifted out to the template. This is a security-relevant
    # invariant: AST scan only considers module body.
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text(
            'def _hidden():\n    PROMPT = "leaked"\n    return PROMPT\n',
            encoding="utf-8",
        )
        nested_fn = _load_prompt_template(tmp_path)
        _record(
            "pipeline_prompt_function_scope_not_extracted",
            nested_fn == "",
            "" if nested_fn == "" else f"expected empty, got {nested_fn!r}",
        )

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text(
            'class Solver:\n    PROMPT = "leaked"\n',
            encoding="utf-8",
        )
        nested_cls = _load_prompt_template(tmp_path)
        _record(
            "pipeline_prompt_class_scope_not_extracted",
            nested_cls == "",
            "" if nested_cls == "" else f"expected empty, got {nested_cls!r}",
        )

    # Non-string constants (int, bytes, None, tuple) must not be coerced.
    for label, src in [
        ("int", 'PROMPT = 42\n'),
        ("bytes", 'PROMPT = b"bytes"\n'),
        ("none", 'PROMPT = None\n'),
        ("tuple", 'PROMPT = ("a", "b")\n'),
    ]:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            (tmp_path / "solver.py").write_text(src, encoding="utf-8")
            result = _load_prompt_template(tmp_path)
            _record(
                f"pipeline_prompt_non_string_constant_rejected_{label}",
                result == "",
                "" if result == "" else f"{label}: expected empty, got {result!r}",
            )

    # Annotated (AnnAssign) and augmented (AugAssign) forms are intentionally
    # not supported by the current extractor. Lock in that behavior so any
    # future change is a deliberate decision, not silent drift.
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text(
            'PROMPT: str = "annotated"\n', encoding="utf-8",
        )
        annotated = _load_prompt_template(tmp_path)
        _record(
            "pipeline_prompt_annotated_assignment_not_supported",
            annotated == "",
            "" if annotated == "" else f"expected empty, got {annotated!r}",
        )

    # Hostile solver.py: embedded NUL byte raises ValueError from ast.parse
    # (not SyntaxError), so the except tuple must include ValueError or the
    # proxy will bubble the exception up and kill the run.
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_bytes(b'PROMPT = "x"\n\x00bad\n')
        nul = _load_prompt_template(tmp_path)
        ok_nul = nul == ""
        _record(
            "pipeline_prompt_solver_with_nul_byte_returns_empty",
            ok_nul,
            "" if ok_nul else f"expected empty, got {nul!r}",
        )

    # Hostile solver.py: invalid UTF-8 also must not crash.
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_bytes(b'PROMPT = "ok"\n\xff\xferaw\n')
        bad_utf8 = _load_prompt_template(tmp_path)
        ok_bad_utf8 = bad_utf8 == ""
        _record(
            "pipeline_prompt_solver_invalid_utf8_returns_empty",
            ok_bad_utf8,
            "" if ok_bad_utf8 else f"expected empty, got {bad_utf8!r}",
        )

    # ── sandbox argv construction ──
    fake_dir = ROOT / "examples" / "solo" / "demos" / "demo"

    argv_none, cwd_none, name_none = _build_solver_argv(fake_dir, {"mode": "none"})
    ok_none = (
        argv_none == [sys.executable, "solver.py"]
        and cwd_none == str(fake_dir.resolve())
        and name_none is None
    )
    _record(
        "pipeline_sandbox_mode_none_local_subprocess",
        ok_none,
        "" if ok_none else f"unexpected argv/cwd/name: {argv_none!r}, {cwd_none!r}, {name_none!r}",
    )

    argv_default, cwd_default, name_default = _build_solver_argv(fake_dir, DEFAULT_SANDBOX_CONFIG)
    ok_default = (
        argv_default == [sys.executable, "solver.py"]
        and cwd_default == str(fake_dir.resolve())
        and name_default is None
    )
    _record(
        "pipeline_sandbox_default_equals_none",
        ok_default,
        "" if ok_default else f"default sandbox should match mode=none",
    )

    docker_cfg = {
        "mode": "docker",
        "image": "ee-solver:test",
        "memory_mb": 256,
        "cpus": 2,
        "pids_limit": 32,
        "tmpfs_size_mb": 8,
    }
    argv_docker, cwd_docker, name_docker = _build_solver_argv(fake_dir, docker_cfg)
    expected_mount = f"{fake_dir.resolve()}:/solver:ro"
    required_flags = [
        "docker", "run", "--rm", "-i",
        "--user", "1000:1000",
        "--network=none",
        "--read-only",
        "--cap-drop=ALL",
        "--security-opt=no-new-privileges:true",
        "--memory=256m",
        "--memory-swap=256m",
        "--cpus=2",
        "--pids-limit=32",
    ]
    ok_docker = (
        cwd_docker is None
        and all(flag in argv_docker for flag in required_flags)
        and expected_mount in argv_docker
        and "ee-solver:test" in argv_docker
        and "/tmp:size=8m" in argv_docker
    )
    _record(
        "pipeline_sandbox_mode_docker_argv_shape",
        ok_docker,
        "" if ok_docker else f"unexpected docker argv: {argv_docker!r}",
    )

    # --name must be injected and returned so run_solver can `docker kill`
    # the container on timeout. Without this, a kill of the host docker CLI
    # leaves the daemon's container running — the orphan bug GPT flagged.
    ok_name_present = (
        isinstance(name_docker, str)
        and name_docker.startswith("ee-solver-")
        and "--name" in argv_docker
        and argv_docker[argv_docker.index("--name") + 1] == name_docker
    )
    _record(
        "pipeline_sandbox_docker_unique_name_for_cleanup",
        ok_name_present,
        "" if ok_name_present else f"missing/wrong --name: name={name_docker!r}, argv={argv_docker!r}",
    )

    # Names must be per-invocation unique so parallel proxies don't collide
    # on docker's name namespace (would fail with "name already in use").
    _, _, name_docker_2 = _build_solver_argv(fake_dir, docker_cfg)
    ok_unique = isinstance(name_docker_2, str) and name_docker_2 != name_docker
    _record(
        "pipeline_sandbox_docker_name_is_unique_per_invocation",
        ok_unique,
        "" if ok_unique else f"names collided: {name_docker!r} vs {name_docker_2!r}",
    )

    try:
        _build_solver_argv(fake_dir, {"mode": "unknown"})
        raised = False
    except ValueError:
        raised = True
    _record(
        "pipeline_sandbox_unknown_mode_raises",
        raised,
        "" if raised else "expected ValueError for unknown sandbox mode",
    )

    # Dockerfile must pin the base image by digest so rebuilds are
    # reproducible. A bare ``python:3.11-slim`` tag drifts silently.
    dockerfile = (ROOT / "Dockerfile").read_text(encoding="utf-8")
    from_line = next(
        (line for line in dockerfile.splitlines() if line.strip().startswith("FROM ")),
        "",
    )
    ok_digest = "@sha256:" in from_line and re.search(r"@sha256:[0-9a-f]{64}", from_line) is not None
    _record(
        "pipeline_sandbox_dockerfile_pinned_by_digest",
        ok_digest,
        "" if ok_digest else f"FROM line must include @sha256:<digest>, got: {from_line!r}",
    )

    # ── subprocess env selection ──
    # mode=none: Popen child IS the solver → stripped solver_env passes through.
    fake_solver_env = {"PATH": "/usr/bin", "DOCKER_HOST": "IF_THIS_LEAKS_WE_STRIP_IT"}
    env_none = _solver_subprocess_env({"mode": "none"}, fake_solver_env)
    ok_env_none = env_none == fake_solver_env
    _record(
        "pipeline_subprocess_env_mode_none_passes_stripped_env",
        ok_env_none,
        "" if ok_env_none else f"expected stripped env, got {env_none!r}",
    )

    # mode=docker: Popen child is the host docker CLI → must inherit host env
    # so DOCKER_HOST/DOCKER_CONFIG/TLS vars reach the daemon. Returning the
    # stripped solver_env here was a real regression — locked in forever now.
    env_docker = _solver_subprocess_env({"mode": "docker"}, fake_solver_env)
    ok_env_docker = env_docker is None
    _record(
        "pipeline_subprocess_env_mode_docker_inherits_host",
        ok_env_docker,
        "" if ok_env_docker else f"expected None, got {env_docker!r}",
    )

    # Default config (currently mode=none) must not break the env path either.
    env_default = _solver_subprocess_env(DEFAULT_SANDBOX_CONFIG, fake_solver_env)
    ok_env_default = env_default == fake_solver_env
    _record(
        "pipeline_subprocess_env_default_matches_mode_none",
        ok_env_default,
        "" if ok_env_default else f"default env path drifted: {env_default!r}",
    )

    # ── stderr drain regression (pipe deadlock prevention + diagnostics) ──
    # Static check: the *solver* Popen must use stderr=subprocess.PIPE and the
    # function must spawn a `_drain_stderr` thread. We parse the AST and look
    # specifically at the ``proc = subprocess.Popen(...)`` assignment — a regex
    # would either span the wrong call (e.g. the legitimate ``subprocess.run``
    # that fires ``docker kill`` with DEVNULL) or break on nested parens. The
    # behavioural noisy-stderr test below exercises the deadlock; this AST
    # check pins the design invariant.
    run_solver_src = inspect.getsource(run_solver)
    static_problems: list[str] = []
    try:
        run_solver_tree = ast.parse(run_solver_src)
        fn_node = run_solver_tree.body[0]
    except (SyntaxError, IndexError) as exc:
        static_problems.append(f"run_solver source did not parse: {exc!r}")
        fn_node = None

    def _is_popen_call(node: ast.AST) -> bool:
        if not isinstance(node, ast.Call):
            return False
        func = node.func
        return (
            isinstance(func, ast.Attribute)
            and func.attr == "Popen"
            and isinstance(func.value, ast.Name)
            and func.value.id == "subprocess"
        )

    solver_popen: ast.Call | None = None
    if fn_node is not None:
        for node in ast.walk(fn_node):
            if not isinstance(node, ast.Assign):
                continue
            if len(node.targets) != 1:
                continue
            target = node.targets[0]
            if not (isinstance(target, ast.Name) and target.id == "proc"):
                continue
            if _is_popen_call(node.value):
                solver_popen = node.value  # type: ignore[assignment]
                break

    def _kw_const_name(call: ast.Call, name: str) -> str | None:
        for kw in call.keywords:
            if kw.arg != name:
                continue
            v = kw.value
            if isinstance(v, ast.Attribute) and isinstance(v.value, ast.Name):
                return f"{v.value.id}.{v.attr}"
            return ast.unparse(v) if hasattr(ast, "unparse") else None
        return None

    if solver_popen is None:
        static_problems.append(
            "run_solver no longer assigns ``proc = subprocess.Popen(...)`` — "
            "the static stderr-drain check cannot locate the solver Popen"
        )
    else:
        stderr_arg = _kw_const_name(solver_popen, "stderr")
        if stderr_arg == "subprocess.DEVNULL":
            static_problems.append(
                "solver Popen uses stderr=subprocess.DEVNULL — that drops "
                "contestant tracebacks; use PIPE with a drain thread instead"
            )
        elif stderr_arg != "subprocess.PIPE":
            static_problems.append(
                f"solver Popen must use stderr=subprocess.PIPE (got {stderr_arg!r})"
            )
    if "_drain_stderr" not in run_solver_src:
        static_problems.append(
            "run_solver must spawn a _drain_stderr thread to avoid the "
            "kernel-pipe deadlock"
        )
    _record(
        "pipeline_run_solver_drains_stderr_to_bounded_buffer",
        not static_problems,
        "" if not static_problems else "; ".join(static_problems),
    )

    # Behavioral check: a solver that floods 512 KiB to stderr then exits
    # must complete well under the watchdog timeout. With stderr=PIPE and no
    # stderr reader, this would block at the kernel buffer (~64 KiB) and the
    # proxy would wait the full timeout_seconds. With DEVNULL it returns fast.
    noisy_solver = (
        "import sys\n"
        "sys.stderr.write('x' * 524288)\n"
        "sys.stderr.flush()\n"
        "sys.exit(0)\n"
    )
    fake_problem = {
        "id": "stderr_flood", "eq1_id": 1, "eq2_id": 2,
        "equation1": "x = x", "equation2": "x = x",
    }
    fake_config = {
        "solver": {"timeout_seconds": 10},
        "judge": {"max_code_length": 1000, "max_false_cert_bytes": 1000},
        "sandbox": {"mode": "none"},
    }
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text(noisy_solver, encoding="utf-8")
        start = time.time()
        run_solver(tmp_path, fake_problem, fake_config)
        elapsed = time.time() - start
    ok_fast = elapsed < 5.0
    _record(
        "pipeline_run_solver_noisy_stderr_does_not_deadlock",
        ok_fast,
        "" if ok_fast else f"took {elapsed:.1f}s — likely deadlocked on stderr pipe",
    )

    # ── Intake size cap regression (Stage 2 rule: solver.py ≤ 500 KB) ──
    # A solver larger than config.judge.max_solver_bytes must be rejected at
    # intake without ever launching a subprocess. The previous rule change
    # dropped call-count budgets; this rule is now the sole mechanism that
    # prevents pathological submissions from being scheduled at all.
    size_config = {
        "solver": {"timeout_seconds": 30},
        "judge": {
            "max_code_length": 1000,
            "max_false_cert_bytes": 1000,
            "max_solver_bytes": 1000,
        },
        "sandbox": {"mode": "none"},
    }
    fake_problem_size = {
        "id": "size_cap", "eq1_id": 1, "eq2_id": 2,
        "equation1": "x = x", "equation2": "x = x",
    }
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        # 2000 bytes > 1000-byte cap → must be rejected pre-launch.
        (tmp_path / "solver.py").write_text("x = 0\n" + ("# pad\n" * 400), encoding="utf-8")
        t0 = time.time()
        over_result = run_solver(tmp_path, fake_problem_size, size_config)
        over_elapsed = time.time() - t0
        # A small solver under the cap must still run (and fail naturally for
        # having no protocol response) — confirming the guard is not a blanket
        # bypass. This solver exits immediately without speaking JSON.
        (tmp_path / "solver.py").write_text("import sys\nsys.exit(0)\n", encoding="utf-8")
        under_result = run_solver(tmp_path, fake_problem_size, size_config)

    over_log = over_result.get("log", [])
    ok_oversized_rejected = (
        not over_result.get("solved")
        and any(
            entry.get("type") == "error"
            and "exceeds limit" in (entry.get("message") or "")
            for entry in over_log
        )
        and over_elapsed < 2.0
    )
    _record(
        "pipeline_intake_rejects_oversize_solver",
        ok_oversized_rejected,
        "" if ok_oversized_rejected else (
            f"oversize solver not rejected pre-launch: elapsed={over_elapsed:.2f}s "
            f"log={over_log!r}"
        ),
    )
    ok_undersized_runs = (
        not under_result.get("solved")
        and not any(
            entry.get("type") == "error"
            and "exceeds limit" in (entry.get("message") or "")
            for entry in under_result.get("log", [])
        )
    )
    _record(
        "pipeline_intake_allows_undersize_solver",
        ok_undersized_runs,
        "" if ok_undersized_runs else f"undersize solver wrongly rejected: {under_result!r}",
    )

    # ── #2: config cap matches the public 500 KB contract ──
    # The contest advertises "solver.py ≤ 500 KB". Drift between the JSON
    # value and the README value would let a 500,001-byte submission pass
    # locally while violating the stated rule.
    default_cfg = load_config()
    cap = default_cfg.get("judge", {}).get("max_solver_bytes")
    _record(
        "pipeline_config_cap_is_500000_bytes",
        cap == 500000,
        "" if cap == 500000 else f"expected 500000 bytes, got {cap!r}",
    )

    # ── #8: docs must not re-grow stale budget language ──
    # After removing per-call caps and changing token cap, the README/TUTORIAL
    # are single source of truth for contestants. A resurrected "Max LLM
    # calls" or "16,384" token row would silently mislead them.
    doc_files = [
        ROOT / "README.md",
        ROOT / "examples" / "solo" / "TUTORIAL.md",
        ROOT / "examples" / "marathon" / "TUTORIAL.md",
    ]
    forbidden_substrings = [
        "Max LLM calls",
        "Max judge calls",
        "16,384",
        "16384",
    ]
    doc_drift: list[str] = []
    for doc in doc_files:
        text = doc.read_text(encoding="utf-8")
        for needle in forbidden_substrings:
            if needle in text:
                doc_drift.append(f"{doc.name}: contains '{needle}'")
    _record(
        "pipeline_docs_no_stale_budget_language",
        not doc_drift,
        "" if not doc_drift else "; ".join(doc_drift),
    )

    # ── secret-file gitignore guard ──
    # The playground/solo wrappers persist OpenRouter / OpenAI keys to
    # repo-root ``.env`` and tell the user the file is gitignored. The check
    # below verifies that promise: every secret-target path the wrappers
    # reference must actually be ignored by git, so a careless ``git add -A``
    # cannot publish the key. We delegate to ``git check-ignore`` because it
    # is the authoritative answer and matches the user's local rules exactly.
    # When the playground is hidden from the public repo (``playground/``
    # gitignored), the wrappers are absent and the check is skipped silently.
    _playground_solo = ROOT / "playground" / "solo"
    wrapper_files = (
        [_playground_solo / "start.sh", _playground_solo / "start.bat"]
        if _playground_solo.is_dir()
        else []
    )
    secret_paths: list[str] = []
    secret_path_re = re.compile(r"""ENV_FILE\s*=\s*["']?([^"'\s]+)""")
    # Bash parameter expansion ``${VAR:-default}`` — the wrapper accepts an
    # override for the harness, but the in-tree default path is what we must
    # gitignore. Strip the wrapper to recover ``default``.
    bash_default_re = re.compile(r"^\$\{[A-Za-z_][A-Za-z0-9_]*:-(.+)\}$")
    for wf in wrapper_files:
        if not wf.exists():
            continue
        text = wf.read_text(encoding="utf-8", errors="replace")
        for m in secret_path_re.finditer(text):
            raw = m.group(1)
            bd = bash_default_re.match(raw)
            if bd:
                raw = bd.group(1)
            # The wrappers compose ENV_FILE from $REPO_ROOT / %REPO_ROOT% so
            # what we extract is a tail like "$REPO_ROOT/.env" or
            # "%REPO_ROOT%\.env". Stripping the prefix yields the in-tree
            # path we want to check.
            tail = (
                raw.replace("$REPO_ROOT/", "")
                .replace("%REPO_ROOT%\\", "")
                .replace("%REPO_ROOT%/", "")
                .replace("\\", "/")
            )
            if tail and tail not in secret_paths:
                secret_paths.append(tail)
    leaks: list[str] = []
    if secret_paths:
        try:
            proc = subprocess.run(
                ["git", "-C", str(ROOT), "check-ignore", "--", *secret_paths],
                capture_output=True,
                text=True,
                timeout=10,
            )
            ignored = {line.strip() for line in proc.stdout.splitlines() if line.strip()}
        except (OSError, subprocess.TimeoutExpired) as exc:
            ignored = set()
            leaks.append(f"git check-ignore unavailable: {exc}")
        for sp in secret_paths:
            if sp not in ignored:
                leaks.append(f"{sp} is NOT gitignored — wrapper would persist a secret to a tracked path")
    _record(
        "pipeline_wrapper_secret_files_are_gitignored",
        not leaks,
        "" if not leaks else "; ".join(leaks),
    )

    # Only the official public allowlist counts toward the canonical gate.
    # Local dev-only solver forks live under archive/ (gitignored); they must
    # not affect the harness verdict.
    public_demos = sorted(
        name for name in demo_names
        if (ROOT / "examples" / "solo" / "demos" / name).is_dir()
    )
    tutorial_text = (ROOT / "examples" / "solo" / "TUTORIAL.md").read_text(encoding="utf-8")
    demo_count_word = {3: "three", 4: "four", 5: "five"}.get(len(public_demos))
    ok_demo_count = (
        demo_count_word is not None
        and f"All {demo_count_word} demos" in tutorial_text
    )
    _record(
        "pipeline_tutorial_demo_count_matches_dirs",
        ok_demo_count,
        (
            ""
            if ok_demo_count
            else f"public demos={public_demos} but tutorial count phrase not found"
        ),
    )

    # ── #1: single-file layout enforcement ──
    # With helpers.py alongside solver.py a contestant could smuggle far more
    # than 500 KB of logic into the submission by imports at runtime. The
    # docker bind-mount makes every file in the directory visible to the
    # solver process, so this check is the only thing keeping the cap honest.
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text("PROMPT = ''\n", encoding="utf-8")
        err_only = _validate_submission_layout(tmp_path)
        _record(
            "pipeline_layout_solver_alone_accepted",
            err_only is None,
            "" if err_only is None else f"bare solver.py wrongly rejected: {err_only}",
        )

        (tmp_path / "helper.py").write_text("x = 1\n", encoding="utf-8")
        err_helper = _validate_submission_layout(tmp_path)
        _record(
            "pipeline_layout_helper_py_rejected",
            err_helper is not None and "helper.py" in err_helper,
            "" if (err_helper and "helper.py" in err_helper)
            else f"helper.py not rejected: {err_helper!r}",
        )

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text("PROMPT = ''\n", encoding="utf-8")
        (tmp_path / "payload.bin").write_bytes(b"\x00" * 2048)
        err_payload = _validate_submission_layout(tmp_path)
        _record(
            "pipeline_layout_data_payload_rejected",
            err_payload is not None and "payload.bin" in err_payload,
            "" if (err_payload and "payload.bin" in err_payload)
            else f"payload.bin not rejected: {err_payload!r}",
        )

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text("PROMPT = ''\n", encoding="utf-8")
        (tmp_path / "subdir").mkdir()
        err_subdir = _validate_submission_layout(tmp_path)
        _record(
            "pipeline_layout_subdirectory_rejected",
            err_subdir is not None and "subdir" in err_subdir,
            "" if (err_subdir and "subdir" in err_subdir)
            else f"subdir not rejected: {err_subdir!r}",
        )

    # A symlinked solver.py (target outside the submission dir) must be
    # rejected. The docker mount resolves symlinks on the host filesystem,
    # so without this check a contestant could escape the 500 KB cap by
    # pointing solver.py at a multi-MB file and shipping a tiny stub inside
    # the submission dir.
    with tempfile.TemporaryDirectory() as outer:
        outer_path = Path(outer)
        target = outer_path / "target.py"
        target.write_text("PROMPT = ''\n", encoding="utf-8")
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            (tmp_path / "solver.py").symlink_to(target)
            err_symlink = _validate_submission_layout(tmp_path)
        _record(
            "pipeline_layout_symlinked_solver_rejected",
            err_symlink is not None and "symlink" in err_symlink,
            "" if (err_symlink and "symlink" in err_symlink)
            else f"symlinked solver.py not rejected: {err_symlink!r}",
        )

    # Behavioral: run_solver must refuse a submission with a helper file
    # before launching any subprocess.
    size_cfg = {
        "solver": {"timeout_seconds": 30},
        "judge": {
            "max_code_length": 1000,
            "max_false_cert_bytes": 1000,
            "max_solver_bytes": 500000,
        },
        "sandbox": {"mode": "none"},
    }
    fake_problem_layout = {
        "id": "layout", "eq1_id": 1, "eq2_id": 2,
        "equation1": "x = x", "equation2": "x = x",
    }
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text("PROMPT = ''\n", encoding="utf-8")
        (tmp_path / "helper.py").write_text("print('leak')\n", encoding="utf-8")
        t0 = time.time()
        res = run_solver(tmp_path, fake_problem_layout, size_cfg)
        elapsed = time.time() - t0
    rejected = (
        not res.get("solved")
        and any(
            entry.get("type") == "error"
            and "submission must contain only solver.py" in (entry.get("message") or "")
            for entry in res.get("log", [])
        )
        and elapsed < 2.0
    )
    _record(
        "pipeline_run_solver_rejects_helper_file",
        rejected,
        "" if rejected else f"helper.py not rejected pre-launch: log={res.get('log')!r}",
    )

    # ── #4: bounded stdout line read ──
    # A hostile solver emitting a huge single line without a newline must not
    # exhaust proxy memory or stall the loop — readline is capped and the
    # proxy must abort the session with a logged error.
    huge_cfg = {
        "solver": {"timeout_seconds": 30},
        "judge": {
            "max_code_length": 1000,
            "max_false_cert_bytes": 1000,
            "max_solver_bytes": 500000,
        },
        "sandbox": {"mode": "none"},
    }
    fake_problem_huge = {
        "id": "huge_line", "eq1_id": 1, "eq2_id": 2,
        "equation1": "x = x", "equation2": "x = x",
    }
    # Write 2×cap chars with no newline, then flush and exit — exercises the
    # "line exceeds cap" branch without any wall-clock timeout kicking in.
    flood_solver = (
        "import sys\n"
        f"sys.stdout.write('x' * (2 * {MAX_STDOUT_LINE_CHARS}))\n"
        "sys.stdout.flush()\n"
        "sys.exit(0)\n"
    )
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text(flood_solver, encoding="utf-8")
        t0 = time.time()
        flood_result = run_solver(tmp_path, fake_problem_huge, huge_cfg)
        flood_elapsed = time.time() - t0
    flood_ok = (
        not flood_result.get("solved")
        and flood_elapsed < 15.0  # must not wait the full 30s timeout
        and any(
            entry.get("type") == "error"
            and "exceeded" in (entry.get("message") or "")
            and "chars" in (entry.get("message") or "")
            for entry in flood_result.get("log", [])
        )
    )
    _record(
        "pipeline_run_solver_caps_huge_stdout_line",
        flood_ok,
        "" if flood_ok else (
            f"unbounded-stdout solver not capped: elapsed={flood_elapsed:.1f}s "
            f"log={flood_result.get('log')!r}"
        ),
    )

    # ── #3: deadline-aware LLM/judge calls ──
    # Before this fix, a blocking call issued near the deadline could keep
    # the proxy sitting in requests.post for up to 300s past the watchdog.
    # These tests monkeypatch _call_llm and _call_judge to sleep past the
    # solver timeout; run_solver must still return within timeout + epsilon.
    slow_solver = (
        "import json, sys\n"
        "sys.stdin.readline()\n"
        "sys.stdout.write(json.dumps({'call':'llm','context':{}}) + chr(10))\n"
        "sys.stdout.flush()\n"
        "sys.stdin.readline()\n"  # wait for response that never comes fast enough
    )
    deadline_cfg = {
        "solver": {"timeout_seconds": 2},
        "judge": {
            "max_code_length": 1000,
            "max_false_cert_bytes": 1000,
            "max_solver_bytes": 500000,
        },
        "sandbox": {"mode": "none"},
        "llm": {
            "model": "test-model",
            "max_output_tokens": 16,
            "temperature": 0.0,
        },
    }
    fake_problem_deadline = {
        "id": "deadline", "eq1_id": 1, "eq2_id": 2,
        "equation1": "x = x", "equation2": "x = x",
    }

    captured_max_seconds: list[float | None] = []

    def _slow_llm(prompt, config, *, max_seconds=None, **_kwargs):
        captured_max_seconds.append(max_seconds)
        # Sleep long enough that the fixed 300s default would blow the deadline,
        # but respect the clamp so the test itself finishes fast.
        bounded = max(0.0, min(float(max_seconds or 300.0), 10.0))
        time.sleep(bounded + 0.1)
        return {"error": "forced slow path"}

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "solver.py").write_text(slow_solver, encoding="utf-8")
        # Set OPENROUTER_API_KEY briefly so _call_llm doesn't short-circuit
        # on the "not set" branch before ever honoring max_seconds.
        prev_key = os.environ.get("OPENROUTER_API_KEY")
        os.environ["OPENROUTER_API_KEY"] = "test-key"
        try:
            with patch.object(_proxy, "_call_llm", side_effect=_slow_llm):
                t0 = time.time()
                run_solver(tmp_path, fake_problem_deadline, deadline_cfg)
                elapsed_deadline = time.time() - t0
        finally:
            if prev_key is None:
                os.environ.pop("OPENROUTER_API_KEY", None)
            else:
                os.environ["OPENROUTER_API_KEY"] = prev_key
    ok_clamp_returned = bool(captured_max_seconds) and all(
        ms is not None and ms <= deadline_cfg["solver"]["timeout_seconds"] + 0.5
        for ms in captured_max_seconds
    )
    # With a 2s solver timeout, total wall-clock should be well under 5s —
    # before the fix it was ~302s because of the hardcoded 300s HTTP timeout.
    ok_hard_deadline = elapsed_deadline < 5.0
    _record(
        "pipeline_run_solver_passes_remaining_to_llm",
        ok_clamp_returned,
        "" if ok_clamp_returned else f"max_seconds values: {captured_max_seconds!r}",
    )
    _record(
        "pipeline_run_solver_honors_deadline_during_blocking_llm",
        ok_hard_deadline,
        "" if ok_hard_deadline else f"elapsed {elapsed_deadline:.1f}s — deadline not honored",
    )

    # ── #4: streaming _call_llm must honor total wall-clock deadline ──
    # SDK's ``timeout`` is per-chunk read in stream mode — every byte resets
    # it. A slow-drip reasoning model can dribble past http_timeout forever.
    # The streaming loop must enforce its own total deadline; this test
    # constructs a fake stream that yields forever and confirms _call_llm
    # returns a timeout error within max_seconds + a small epsilon.
    class _FakeDelta:
        def __init__(self, reasoning=None, content=None):
            self.reasoning = reasoning
            self.content = content

    class _FakeChoice:
        def __init__(self, delta):
            self.delta = delta

    class _FakeChunk:
        def __init__(self, reasoning=None, content=None):
            self.choices = [_FakeChoice(_FakeDelta(reasoning, content))]

    class _FakeResponse:
        def close(self):
            pass

    class _FakeStream:
        def __init__(self, interval=0.2):
            self.interval = interval
            self.response = _FakeResponse()

        def __iter__(self):
            while True:
                time.sleep(self.interval)
                yield _FakeChunk(reasoning="x")

    class _FakeCompletions:
        def create(self, **_kwargs):
            return _FakeStream(interval=0.2)

    class _FakeChat:
        def __init__(self):
            self.completions = _FakeCompletions()

    class _FakeOpenAI:
        def __init__(self, **_kwargs):
            self.chat = _FakeChat()

    stream_cfg = {
        "llm": {
            "model": "fake",
            "max_output_tokens": 16,
            "temperature": 0.0,
        }
    }
    chunks_seen: list[tuple[str, str]] = []
    prev_key_stream = os.environ.get("OPENROUTER_API_KEY")
    os.environ["OPENROUTER_API_KEY"] = "test-key"
    try:
        with patch.object(_proxy, "OpenAI", _FakeOpenAI):
            t0 = time.time()
            stream_res = _proxy._call_llm(
                "test prompt", stream_cfg, max_seconds=1.0,
                stream_chunk_hook=lambda k, t: chunks_seen.append((k, t)),
            )
            stream_elapsed = time.time() - t0
    finally:
        if prev_key_stream is None:
            os.environ.pop("OPENROUTER_API_KEY", None)
        else:
            os.environ["OPENROUTER_API_KEY"] = prev_key_stream

    ok_stream_timeout = (
        isinstance(stream_res, dict)
        and isinstance(stream_res.get("error"), str)
        and "timed out" in stream_res["error"]
        and stream_elapsed < 3.0
        and len(chunks_seen) >= 1
    )
    _record(
        "pipeline_call_llm_streaming_enforces_total_deadline",
        ok_stream_timeout,
        (
            ""
            if ok_stream_timeout
            else f"res={stream_res!r} elapsed={stream_elapsed:.2f}s chunks={len(chunks_seen)}"
        ),
    )

    # ── #4b: llm.http_timeout_seconds config knob is honored ──
    # Default LLM HTTP budget is 300 s, which is enough for typical multi-
    # round LLM loops under the 3600 s reference solver budget. Deep-mining
    # scripts on hard problems with reasoning_effort=high may need to raise
    # this knob too, otherwise a single LLM call still caps at 300 s and
    # gpt-oss-120b just drip-times-out. The proxy must therefore read
    # llm.http_timeout_seconds from config (bounded above by max_seconds).
    # Regression: use a fake stream at 0.2 s cadence with max_seconds=5.0
    # and config value 2.0 — the deadline should fire at ~2 s, proving the
    # knob was honored (not stuck at the 300 s default).
    stream_cfg_knob = {
        "llm": {
            "model": "fake",
            "max_output_tokens": 16,
            "temperature": 0.0,
            "http_timeout_seconds": 2.0,
        }
    }
    prev_key_knob = os.environ.get("OPENROUTER_API_KEY")
    os.environ["OPENROUTER_API_KEY"] = "test-key"
    try:
        with patch.object(_proxy, "OpenAI", _FakeOpenAI):
            t0 = time.time()
            knob_res = _proxy._call_llm(
                "test prompt", stream_cfg_knob, max_seconds=5.0,
                # Pass a hook so the streaming path is exercised — that's
                # where the deadline check lives (non-streaming uses the
                # SDK's own timeout and is not what this knob targets).
                stream_chunk_hook=lambda _k, _t: None,
            )
            knob_elapsed = time.time() - t0
    finally:
        if prev_key_knob is None:
            os.environ.pop("OPENROUTER_API_KEY", None)
        else:
            os.environ["OPENROUTER_API_KEY"] = prev_key_knob
    ok_knob = (
        isinstance(knob_res, dict)
        and isinstance(knob_res.get("error"), str)
        and "timed out" in knob_res["error"]
        # Deadline should fire near 2 s (not the 5 s max_seconds, not the
        # 300 s default). Epsilon ≥ 2 × chunk interval (0.4 s) for scheduler
        # jitter; upper bound proves it didn't revert to the 300 s default.
        and 1.5 < knob_elapsed < 4.0
    )
    _record(
        "pipeline_call_llm_honors_http_timeout_config_knob",
        ok_knob,
        (
            ""
            if ok_knob
            else f"res={knob_res!r} elapsed={knob_elapsed:.2f}s (expected ~2s)"
        ),
    )

    # ── #4c: llm.base_url + llm.api_key_env route to the chosen provider ──
    # Goal: the same proxy must talk to any OpenAI-compatible endpoint
    # (DeepSeek, Kimi/Moonshot, GLM, Minimax, Qwen, api.openai.com, ...)
    # without code changes, while the default (no llm.base_url set) still
    # points at OpenRouter with OPENAI_API_KEY / OPENROUTER_API_KEY. This
    # test captures the ctor kwargs of a stub OpenAI client and verifies
    # both branches land on the right (base_url, api_key) pair.
    captured_ctor: list[dict[str, Any]] = []
    captured_create: list[dict[str, Any]] = []

    class _CaptureOpenAI:
        def __init__(self, **kwargs):
            captured_ctor.append(dict(kwargs))
            # Return a completion immediately so _call_llm returns cleanly
            # (we're testing routing, not reasoning).
            class _Msg:
                content = "ok"
                reasoning = None

            class _Choice:
                message = _Msg()

            class _Completion:
                choices = [_Choice()]

            class _Completions:
                def create(self_inner, **kw):
                    captured_create.append(dict(kw))
                    return _Completion()

            class _Chat:
                def __init__(self):
                    self.completions = _Completions()

            self.chat = _Chat()

    # Branch A: config-driven routing (direct-to-provider).
    direct_cfg = {
        "llm": {
            "model": "deepseek-chat",
            "max_output_tokens": 16,
            "temperature": 0.0,
            "base_url": "https://api.deepseek.com/v1",
            "api_key_env": "HARNESS_FAKE_DEEPSEEK_KEY",
        }
    }
    prev_fake = os.environ.pop("HARNESS_FAKE_DEEPSEEK_KEY", None)
    os.environ["HARNESS_FAKE_DEEPSEEK_KEY"] = "fake-deepseek-key"
    try:
        with patch.object(_proxy, "OpenAI", _CaptureOpenAI):
            direct_res = _proxy._call_llm("hi", direct_cfg, max_seconds=5.0)
    finally:
        os.environ.pop("HARNESS_FAKE_DEEPSEEK_KEY", None)
        if prev_fake is not None:
            os.environ["HARNESS_FAKE_DEEPSEEK_KEY"] = prev_fake

    ok_direct = (
        len(captured_ctor) == 1
        and captured_ctor[0].get("base_url") == "https://api.deepseek.com/v1"
        and captured_ctor[0].get("api_key") == "fake-deepseek-key"
        and direct_res.get("response") == "ok"
    )
    _record(
        "pipeline_call_llm_routes_to_configured_provider",
        ok_direct,
        "" if ok_direct else f"ctor={captured_ctor!r} res={direct_res!r}",
    )

    # Branch B: missing api_key_env env var must fail fast with a precise
    # error (not a generic "OPENAI_API_KEY not set"), so contestants get a
    # useful signal when they typo the env var name.
    missing_cfg = {
        "llm": {
            "model": "deepseek-chat",
            "max_output_tokens": 16,
            "temperature": 0.0,
            "base_url": "https://api.deepseek.com/v1",
            "api_key_env": "HARNESS_MISSING_KEY_XYZ",
        }
    }
    prev_missing = os.environ.pop("HARNESS_MISSING_KEY_XYZ", None)
    try:
        missing_res = _proxy._call_llm("hi", missing_cfg, max_seconds=5.0)
    finally:
        if prev_missing is not None:
            os.environ["HARNESS_MISSING_KEY_XYZ"] = prev_missing
    ok_missing = (
        isinstance(missing_res, dict)
        and "HARNESS_MISSING_KEY_XYZ" in str(missing_res.get("error", ""))
    )
    _record(
        "pipeline_call_llm_reports_missing_keyed_api_env",
        ok_missing,
        "" if ok_missing else f"res={missing_res!r}",
    )

    # Branch C: default (no llm.base_url, no llm.api_key_env) must still
    # route to OpenRouter with the legacy env-var fallback. Backward-compat
    # anchor — every existing config in the repo, including opnorm
    # sweeps that are currently running, must keep working after this feature
    # lands.
    captured_ctor.clear()
    default_cfg = {
        "llm": {
            "model": "openai/gpt-oss-120b",
            "max_output_tokens": 16,
            "temperature": 0.0,
        }
    }
    prev_or = os.environ.pop("OPENROUTER_API_KEY", None)
    prev_oa = os.environ.pop("OPENAI_API_KEY", None)
    prev_base = os.environ.pop("OPENAI_BASE_URL", None)
    os.environ["OPENROUTER_API_KEY"] = "legacy-key"
    try:
        with patch.object(_proxy, "OpenAI", _CaptureOpenAI):
            _proxy._call_llm("hi", default_cfg, max_seconds=5.0)
    finally:
        os.environ.pop("OPENROUTER_API_KEY", None)
        if prev_or is not None:
            os.environ["OPENROUTER_API_KEY"] = prev_or
        if prev_oa is not None:
            os.environ["OPENAI_API_KEY"] = prev_oa
        if prev_base is not None:
            os.environ["OPENAI_BASE_URL"] = prev_base
    ok_default = (
        len(captured_ctor) == 1
        and captured_ctor[0].get("base_url") == "https://openrouter.ai/api/v1"
        and captured_ctor[0].get("api_key") == "legacy-key"
    )
    _record(
        "pipeline_call_llm_default_routes_to_openrouter",
        ok_default,
        "" if ok_default else f"ctor={captured_ctor!r}",
    )

    # ── #4d: migration path must not leak OpenRouter-only fields ──
    # The realistic migration is: take the repo's DEFAULT pipeline/config.json
    # (which ships with provider="deepinfra/bf16" + reasoning_effort="medium"
    # because the baseline runs on OpenRouter), and add just two fields —
    # base_url + api_key_env — to point it at DeepSeek / Kimi / GLM / etc.
    # The maintainer should not have to remember to strip OpenRouter private
    # config; the proxy must auto-detect the route and only emit OpenRouter's
    # extra_body envelope when base_url actually points at OpenRouter.
    #
    # This test is the anchor for that guarantee: start from the actual
    # on-disk default config, override only the two new routing fields, stub
    # the OpenAI client, and assert that no OpenRouter-only field ends up on
    # the wire to the direct provider.
    import copy as _copy
    default_cfg_path = ROOT / "pipeline" / "config.json"
    default_cfg_full = json.loads(default_cfg_path.read_text())
    # Sanity check: the default config IS the OpenRouter-flavored one this
    # test is designed to defend against. If this assertion fires, the
    # default config has been cleaned up and this test's premise no longer
    # matches reality — update both together.
    ok_premise = (
        "provider" in default_cfg_full.get("llm", {})
        and "reasoning_effort" in default_cfg_full.get("llm", {})
    )
    _record(
        "pipeline_call_llm_migration_premise_default_config_has_openrouter_extras",
        ok_premise,
        "" if ok_premise else (
            "default config no longer has provider/reasoning_effort; "
            "migration-leak test is now vacuous — either restore the default "
            "or delete this test pair"
        ),
    )

    migration_cfg = _copy.deepcopy(default_cfg_full)
    migration_cfg["llm"]["base_url"] = "https://api.deepseek.com/v1"
    migration_cfg["llm"]["api_key_env"] = "HARNESS_FAKE_MIGRATION_KEY"

    captured_ctor.clear()
    captured_create.clear()
    os.environ.pop("HARNESS_FAKE_MIGRATION_KEY", None)
    os.environ["HARNESS_FAKE_MIGRATION_KEY"] = "fake-migration-key"
    try:
        with patch.object(_proxy, "OpenAI", _CaptureOpenAI):
            _proxy._call_llm("hi", migration_cfg, max_seconds=5.0)
    finally:
        os.environ.pop("HARNESS_FAKE_MIGRATION_KEY", None)

    # 1) client built for the right provider
    ok_ctor = (
        len(captured_ctor) == 1
        and captured_ctor[0].get("base_url") == "https://api.deepseek.com/v1"
        and captured_ctor[0].get("api_key") == "fake-migration-key"
    )
    # 2) the actual request to create() must NOT carry OpenRouter privata
    create_kwargs = captured_create[0] if captured_create else {}
    eb = create_kwargs.get("extra_body", {}) or {}
    leaked: list[str] = []
    if "provider" in eb:
        leaked.append(f"extra_body.provider={eb['provider']!r}")
    if "reasoning" in eb:
        leaked.append(f"extra_body.reasoning={eb['reasoning']!r}")
    ok_no_leak = len(captured_create) == 1 and not leaked

    _record(
        "pipeline_call_llm_migration_no_openrouter_leak_to_direct_provider",
        ok_ctor and ok_no_leak,
        (
            ""
            if ok_ctor and ok_no_leak
            else f"ctor={captured_ctor!r} create_kwargs={create_kwargs!r} leaked={leaked!r}"
        ),
    )

    # Positive control: when base_url DOES point at OpenRouter, the extras
    # must still be emitted (otherwise the "auto-detect" gate would also
    # silently strip fields the current sweeps depend on). Same default
    # config, no overrides beyond the legacy env-key.
    captured_ctor.clear()
    captured_create.clear()
    openrouter_cfg = _copy.deepcopy(default_cfg_full)
    prev_or2 = os.environ.pop("OPENROUTER_API_KEY", None)
    prev_oa2 = os.environ.pop("OPENAI_API_KEY", None)
    prev_base2 = os.environ.pop("OPENAI_BASE_URL", None)
    os.environ["OPENROUTER_API_KEY"] = "or-key"
    try:
        with patch.object(_proxy, "OpenAI", _CaptureOpenAI):
            _proxy._call_llm("hi", openrouter_cfg, max_seconds=5.0)
    finally:
        os.environ.pop("OPENROUTER_API_KEY", None)
        if prev_or2 is not None:
            os.environ["OPENROUTER_API_KEY"] = prev_or2
        if prev_oa2 is not None:
            os.environ["OPENAI_API_KEY"] = prev_oa2
        if prev_base2 is not None:
            os.environ["OPENAI_BASE_URL"] = prev_base2
    or_create = captured_create[0] if captured_create else {}
    or_eb = or_create.get("extra_body", {}) or {}
    ok_or_extras = (
        len(captured_create) == 1
        and or_eb.get("provider", {}).get("order") == [default_cfg_full["llm"]["provider"]]
        and or_eb.get("reasoning", {}).get("effort") == default_cfg_full["llm"]["reasoning_effort"]
    )
    _record(
        "pipeline_call_llm_openrouter_route_still_emits_extras",
        ok_or_extras,
        "" if ok_or_extras else f"create_kwargs={or_create!r}",
    )

    # ── #5: _kill_container() must run in the finally block ──
    # Static check: cleanup must be reachable from any exit path, not only
    # the watchdog branch. A future refactor that removes the finally call
    # would silently regrow the orphan-container bug.
    run_solver_src_finally = inspect.getsource(run_solver)
    # Trim to the finally block so we're checking the right region.
    finally_idx = run_solver_src_finally.rfind("finally:")
    finally_tail = run_solver_src_finally[finally_idx:] if finally_idx >= 0 else ""
    ok_finally_kill = "_kill_container()" in finally_tail
    _record(
        "pipeline_run_solver_kills_container_in_finally",
        ok_finally_kill,
        "" if ok_finally_kill else "finally block must call _kill_container() on every exit path",
    )

    # ── #6: Windows wrapper must not let cmd parser see secret values ──
    # GPT round 4 finding: even though the final env-file write uses
    # PowerShell, an earlier version copied OPENROUTER_API_KEY through
    # ``set "API_KEY=%OPENROUTER_API_KEY%"`` and ``call set "X=%%%X%%%"`` —
    # both of which pass the value through cmd's %.../!...! parser, where
    # ``!`` is a delayed-expansion variable reference and unbalanced ``%``
    # is silently eaten. We now disable delayed expansion globally and
    # delegate ALL secret handling to a separate PowerShell script.
    # Skipped when the playground is held back from the public repo —
    # wrappers are not shipped, so there is nothing to audit.
    bat_path = ROOT / "playground" / "solo" / "start.bat"
    ps1_path = ROOT / "playground" / "solo" / "collect_keys.ps1"
    if not bat_path.is_file():
        # Playground held back from public repo — wrapper not shipped, no
        # cmd-parser path to audit. Keep the suite count stable so the
        # README consistency check matches in either repo configuration.
        _record(
            "pipeline_windows_wrapper_secret_handling_is_cmd_parser_free",
            True,
            "skipped: playground/solo/start.bat absent",
        )
    else:
        bat_text = bat_path.read_text(encoding="utf-8", errors="replace")
        win_problems: list[str] = []
        if "setlocal disabledelayedexpansion" not in bat_text.lower():
            win_problems.append("start.bat must use 'setlocal disabledelayedexpansion'")
        if "setlocal enabledelayedexpansion" in bat_text.lower():
            win_problems.append("start.bat still uses 'setlocal enabledelayedexpansion'")
        secret_var_patterns = (
            "%OPENROUTER_API_KEY%",
            "%OPENAI_API_KEY%",
            "%DEEPSEEK_API_KEY%",
            "%API_KEY%",
            "%API_KEY_INPUT%",
            "%ENV_KEY%",
            # JUDGE_SOLO_EXTRA_ENV used to ride into powershell as
            # ``-ExtraEnvCsv "%JUDGE_SOLO_EXTRA_ENV%"`` — that gave a hostile
            # value the chance to escape the quotes and inject extra cmd
            # commands. The fix is to let collect_keys.ps1 read the env var
            # directly, so the bat must not expand it at all.
            "%JUDGE_SOLO_EXTRA_ENV%",
        )
        for needle in secret_var_patterns:
            if needle in bat_text:
                win_problems.append(f"start.bat directly expands '{needle}' (cmd parser sees the value)")
        if "-ExtraEnvCsv" in bat_text:
            win_problems.append(
                "start.bat passes -ExtraEnvCsv to powershell; that re-introduces "
                "the cmd-parser injection path on JUDGE_SOLO_EXTRA_ENV"
            )
        if "collect_keys.ps1" not in bat_text:
            win_problems.append("start.bat does not invoke collect_keys.ps1")
        if not ps1_path.exists():
            win_problems.append("collect_keys.ps1 missing")
        else:
            ps1_text = ps1_path.read_text(encoding="utf-8")
            if "GetEnvironmentVariable" not in ps1_text:
                win_problems.append("collect_keys.ps1 must read env vars via [Environment]::GetEnvironmentVariable")
            if 'GetEnvironmentVariable("JUDGE_SOLO_EXTRA_ENV")' not in ps1_text:
                win_problems.append(
                    "collect_keys.ps1 must read JUDGE_SOLO_EXTRA_ENV via "
                    "[Environment]::GetEnvironmentVariable, not as a script param "
                    "— a script param means the value crossed cmd's parser"
                )
            for forbidden in ("Invoke-Expression", "iex ", "cmd /c", "cmd.exe /c"):
                if forbidden in ps1_text:
                    win_problems.append(f"collect_keys.ps1 uses unsafe primitive '{forbidden}'")
        _record(
            "pipeline_windows_wrapper_secret_handling_is_cmd_parser_free",
            not win_problems,
            "" if not win_problems else "; ".join(win_problems),
        )

    # ── #7: bash wrapper round-trips a special-char value byte-exact ──
    # End-to-end check that ``write_kv`` in start.sh preserves a value
    # containing every cmd/bash hot character (``! % & < > ^ "``) —
    # the canonical GPT-round-4 stress value. We invoke start.sh in a
    # non-tty subshell with a fake docker on PATH that captures the
    # ``--env-file`` contents; the bash side mirrors what the .ps1 must
    # also achieve on Windows. Skipped when the wrapper is held back from
    # the public repo.
    sh_path = ROOT / "playground" / "solo" / "start.sh"
    if not sh_path.is_file():
        # Playground held back from public repo — wrapper not shipped.
        # Skip with a passing record so the suite count stays stable.
        _record(
            "pipeline_bash_wrapper_special_char_value_round_trip",
            True,
            "skipped: playground/solo/start.sh absent",
        )
    else:
        stress_value = "abc!def%USERPROFILE%&x<y>z^q\"r"
        sh_problems: list[str] = []
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            capture_dir = tmp_root / "capture"
            capture_dir.mkdir()
            # Fake docker: copies the path argument after `--env-file` to a
            # known location, then exits 0 for any subcommand.
            fake_docker = tmp_root / "docker"
            fake_docker.write_text(
                "#!/usr/bin/env bash\n"
                "if [ \"$1\" = run ]; then\n"
                "  prev=\"\"\n"
                "  for a in \"$@\"; do\n"
                "    if [ \"$prev\" = --env-file ]; then\n"
                "      cp \"$a\" \"" + str(capture_dir) + "/envfile.out\"\n"
                "    fi\n"
                "    prev=\"$a\"\n"
                "  done\n"
                "fi\n"
                "exit 0\n",
                encoding="utf-8",
            )
            os.chmod(fake_docker, 0o755)
            env = os.environ.copy()
            env["PATH"] = str(tmp_root) + os.pathsep + env.get("PATH", "")
            env["OPENROUTER_API_KEY"] = stress_value
            env["JUDGE_SOLO_PORT"] = "0"
            env.pop("OPENAI_API_KEY", None)
            env.pop("OPENAI_BASE_URL", None)
            env.pop("JUDGE_SOLO_EXTRA_ENV", None)
            # Pin the .env scenario the script must tolerate: a real-world
            # state where the user has saved DEEPSEEK_API_KEY but no
            # OPENAI_API_KEY. Under ``set -o pipefail`` a no-match grep used
            # to abort the whole script (caught on 2026-04-26).
            synthetic_env = tmp_root / "dotenv"
            synthetic_env.write_text("DEEPSEEK_API_KEY=sk-test-only\n", encoding="utf-8")
            env["JUDGE_SOLO_ENV_FILE"] = str(synthetic_env)
            # Force non-interactive: redirect stdin from /dev/null so [ -t 0 ] is
            # false and start.sh skips every prompt branch.
            try:
                proc = subprocess.run(
                    ["bash", str(sh_path)],
                    cwd=tmp_root,
                    env=env,
                    stdin=subprocess.DEVNULL,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=30,
                )
            except (OSError, subprocess.TimeoutExpired) as exc:
                sh_problems.append(f"start.sh invocation failed: {exc}")
                proc = None
            if proc is not None:
                envfile_out = capture_dir / "envfile.out"
                if proc.returncode != 0:
                    sh_problems.append(
                        f"start.sh exited {proc.returncode}; stderr={proc.stderr.decode('utf-8', 'replace')[:300]!r}"
                    )
                elif not envfile_out.exists():
                    sh_problems.append("envfile.out not produced by fake docker — start.sh did not reach docker run")
                else:
                    content = envfile_out.read_bytes()
                    expected_line = f"OPENROUTER_API_KEY={stress_value}\n".encode("utf-8")
                    if expected_line not in content:
                        sh_problems.append(
                            f"envfile missing byte-exact line; got={content!r}, expected substring={expected_line!r}"
                        )
        _record(
            "pipeline_bash_wrapper_special_char_value_round_trip",
            not sh_problems,
            "" if not sh_problems else "; ".join(sh_problems),
        )

    # ── #7: _call_llm must recognise DeepSeek-style ``reasoning_content`` ──
    # OpenRouter streams reasoning under ``delta.reasoning`` while DeepSeek's
    # direct API uses ``delta.reasoning_content`` / ``message.reasoning_content``.
    # Observed live on 2026-04-26: deepseek-v4-flash burned 21 KB of reasoning
    # before emitting any final ``content``, and on rounds where reasoning
    # consumed the full max_tokens budget the proxy returned empty because
    # only ``reasoning`` was checked — losing the trace entirely. This test
    # builds a fake stream that emits only ``reasoning_content`` (no content)
    # and a fake non-streaming completion with only ``reasoning_content``,
    # asserting that both paths surface that text as the response.
    class _RcDelta:
        def __init__(self, reasoning_content=None, content=None):
            self.reasoning_content = reasoning_content
            self.content = content

    class _RcChoice:
        def __init__(self, delta=None, message=None, finish_reason=None):
            self.delta = delta
            self.message = message
            self.finish_reason = finish_reason

    class _RcChunk:
        def __init__(self, reasoning_content=None, content=None, finish_reason=None):
            self.choices = [_RcChoice(
                delta=_RcDelta(reasoning_content=reasoning_content, content=content),
                finish_reason=finish_reason,
            )]

    class _RcStream:
        def __init__(self):
            self.response = type("_R", (), {"close": lambda self: None})()

        def __iter__(self):
            yield _RcChunk(reasoning_content="step 1; ")
            yield _RcChunk(reasoning_content="step 2.")
            yield _RcChunk(finish_reason="length")

    class _RcMessage:
        def __init__(self):
            self.content = ""
            self.reasoning_content = "non-streaming reasoning trace"

    class _RcCompletionsStream:
        def create(self, **kwargs):
            if kwargs.get("stream"):
                return _RcStream()
            return type("_NS", (), {
                "choices": [_RcChoice(message=_RcMessage(), finish_reason="length")]
            })()

    class _RcChat:
        def __init__(self):
            self.completions = _RcCompletionsStream()

    class _RcOpenAI:
        def __init__(self, **_kwargs):
            self.chat = _RcChat()

    rc_cfg = {
        "llm": {
            "model": "deepseek-v4-flash",
            "base_url": "https://api.deepseek.com/v1",
            "api_key_env": "DEEPSEEK_API_KEY",
            "max_output_tokens": 16,
            "temperature": 0.0,
        }
    }
    prev_rc_key = os.environ.get("DEEPSEEK_API_KEY")
    os.environ["DEEPSEEK_API_KEY"] = "test-key"
    rc_problems: list[str] = []
    rc_chunks: list[tuple[str, str]] = []
    try:
        with patch.object(_proxy, "OpenAI", _RcOpenAI):
            stream_res = _proxy._call_llm(
                "p", rc_cfg, max_seconds=10.0,
                stream_chunk_hook=lambda k, t: rc_chunks.append((k, t)),
            )
            nonstream_res = _proxy._call_llm("p", rc_cfg, max_seconds=10.0)
    finally:
        if prev_rc_key is None:
            os.environ.pop("DEEPSEEK_API_KEY", None)
        else:
            os.environ["DEEPSEEK_API_KEY"] = prev_rc_key

    if not isinstance(stream_res, dict) or "step 1; step 2." not in (stream_res.get("response") or ""):
        rc_problems.append(f"streaming response missing reasoning_content: {stream_res!r}")
    if not any(kind == "reasoning" and "step 1" in text for kind, text in rc_chunks):
        rc_problems.append(f"stream_chunk_hook did not receive reasoning_content as 'reasoning' kind: {rc_chunks!r}")
    if not isinstance(nonstream_res, dict) or "non-streaming reasoning trace" not in (nonstream_res.get("response") or ""):
        rc_problems.append(f"non-streaming response missing reasoning_content fallback: {nonstream_res!r}")
    # Both fake completions report ``finish_reason=length`` with empty content,
    # so the proxy must surface ``truncated: True`` to tell the solver the
    # final answer was lost to token exhaustion (vs. a normal short reply).
    if not (isinstance(stream_res, dict) and stream_res.get("truncated") is True):
        rc_problems.append(f"streaming response missing truncated=True flag: {stream_res!r}")
    if not (isinstance(nonstream_res, dict) and nonstream_res.get("truncated") is True):
        rc_problems.append(f"non-streaming response missing truncated=True flag: {nonstream_res!r}")
    _record(
        "pipeline_call_llm_recognises_deepseek_reasoning_content",
        not rc_problems,
        "" if not rc_problems else "; ".join(rc_problems),
    )

    # ── #8: solver stderr is captured so contestant tracebacks are visible ──
    # Before the drain thread, ``stderr=DEVNULL`` was used to avoid a
    # kernel-pipe-buffer deadlock — but at the cost of throwing away every
    # Python traceback a contestant solver produced. A failed sweep then
    # showed only "EOF, no judge call", with no way to root-cause. The drain
    # thread now keeps the last ~64 KiB of stderr and emits a single
    # ``type=solver_stderr`` log entry on cleanup, giving harness/UI users
    # the diagnostic they need without re-introducing the deadlock.
    crash_solver_dir = ROOT / "tests" / "fixtures_tmp" / "stderr_drain_solver"
    crash_solver_dir.mkdir(parents=True, exist_ok=True)
    crash_solver = crash_solver_dir / "solver.py"
    crash_solver.write_text(
        'import sys\n'
        'sys.stdin.readline()  # consume startup\n'
        'sys.stderr.write("INTENTIONAL_TRACEBACK marker line\\n")\n'
        'raise RuntimeError("boom from contestant solver")\n',
        encoding="utf-8",
    )
    stderr_problems: list[str] = []
    try:
        # Minimal config: solver-only, no LLM/judge needed because the solver
        # crashes before issuing any call.
        crash_cfg = {
            "solver": {"timeout_seconds": 10},
            "judge": {
                "lean_timeout_seconds": 5,
                "max_code_length": 100000,
                "max_false_cert_bytes": 20000,
                "max_solver_bytes": 500000,
            },
            "sandbox": {"mode": "none"},
        }
        crash_problem = {
            "id": "stderr_drain_test",
            "eq1_id": 1,
            "eq2_id": 2,
            "equation1": "x = x",
            "equation2": "x = x",
        }
        result = _proxy.run_solver(crash_solver_dir, crash_problem, crash_cfg)
        log_entries = result.get("log") or []
        stderr_entries = [e for e in log_entries if e.get("type") == "solver_stderr"]
        if not stderr_entries:
            stderr_problems.append(
                f"no solver_stderr entry emitted; log types={[e.get('type') for e in log_entries]!r}"
            )
        else:
            tail = stderr_entries[-1].get("tail") or ""
            if "INTENTIONAL_TRACEBACK" not in tail:
                stderr_problems.append(
                    f"solver_stderr tail missing marker: {tail!r}"
                )
            if "RuntimeError" not in tail and "boom" not in tail:
                stderr_problems.append(
                    f"solver_stderr tail missing crash traceback: {tail!r}"
                )
    finally:
        try:
            crash_solver.unlink()
        except OSError:
            pass
        try:
            crash_solver_dir.rmdir()
        except OSError:
            pass
        try:
            (ROOT / "tests" / "fixtures_tmp").rmdir()
        except OSError:
            pass
    _record(
        "pipeline_solver_stderr_is_captured_for_diagnostics",
        not stderr_problems,
        "" if not stderr_problems else "; ".join(stderr_problems),
    )

    return results


def run_readme_consistency_check(summary: dict[str, Any]) -> list[dict[str, Any]]:
    """Verify README's testing-baseline table matches the live ``summary`` map.

    The previous regression hard-coded ``expected_counts`` so the table and
    the dict could go stale together. This check pulls every value from the
    actual ``passed_*_count`` fields the harness just produced, so adding a
    suite or a regression case auto-bumps the canonical numbers — README
    drift is the only way it can fail.
    """
    challenger = summary.get("challenger", {})
    label_to_value = {
        "Judge cases":         summary.get("passed_case_count", 0),
        "Judge internals":     summary.get("passed_judge_internal_count", 0),
        "Banned tokens":       summary.get("passed_banned_token_count", 0),
        "Repeatability":       summary.get("passed_repeatability_count", 0),
        "Pipeline regressions": summary.get("passed_pipeline_count", 0),
        "Verify branches":     summary.get("passed_verify_branch_count", 0),
        "Public challenger":   challenger.get("passed_public_attack_count", 0),
        "Infra challenger":    challenger.get("passed_infra_attack_count", 0),
    }
    expected_total = sum(label_to_value.values())

    readme_text = (ROOT / "README.md").read_text(encoding="utf-8")
    drift: list[str] = []
    for label, want in label_to_value.items():
        m = re.search(rf"\|\s*{re.escape(label)}\s*\|\s*(\d+)\s*\|", readme_text)
        if not m:
            drift.append(f"{label!r} row not found in README testing table")
        elif int(m.group(1)) != want:
            drift.append(f"{label}: README={m.group(1)} expected={want}")
    m_total = re.search(r"Current repo baseline: \*\*(\d+) green checks\*\*", readme_text)
    if not m_total:
        drift.append("baseline total line not found in README")
    elif int(m_total.group(1)) != expected_total:
        drift.append(f"baseline total: README={m_total.group(1)} expected={expected_total}")

    return [{
        "name": "readme_baseline_matches_harness_counts",
        "ok": not drift,
        "detail": "" if not drift else "; ".join(drift),
    }]


def run_verify_branch_cases(base_config: JudgeConfig) -> list[dict[str, Any]]:
    """Verify-layer branches that fixtures alone can't drive deterministically.

    Currently: LEAN_TIMEOUT. Constructing a reliably-slow Lean proof is
    machine-dependent; mocking ``subprocess.run`` lets us exercise the
    ``TimeoutExpired`` handler in ``verify_answer`` with zero wall time and
    zero cross-platform flake. The ``_ensure_support_module`` /
    ``_ensure_magma_module`` paths short-circuit when the oleans are present
    and up to date, so no subprocess call runs before the patched
    submission-compile call.
    """
    results: list[dict[str, Any]] = []

    problem_path = ROOT / "tests" / "fixtures" / "problems" / "p_true_basic.json"
    answer_path = ROOT / "tests" / "fixtures" / "answers" / "accepted_true_basic.answer.json"
    problem = json.loads(problem_path.read_text(encoding="utf-8"))
    raw_answer = answer_path.read_text(encoding="utf-8")

    # Under the PR #3 architecture the judge compiles `JudgeProblem.lean`
    # before the contestant submission.  The first `subprocess.run` call is
    # the judge-side compile (no timeout handler — it's the judge's own
    # code).  The second call compiles `Submission.lean`; that one is
    # guarded by a `TimeoutExpired` handler that maps to `LEAN_TIMEOUT`.
    # We succeed the first call and raise on the second.
    ok_proc = subprocess.CompletedProcess(args=["lean"], returncode=0, stdout="", stderr="")
    forced_timeout = subprocess.TimeoutExpired(cmd=["lean"], timeout=1)
    def _side_effect(*args, **kwargs):
        nonlocal _calls
        _calls += 1
        if _calls == 1:
            # Simulate a successful JudgeProblem compile: write the olean so
            # downstream logic sees a plausible artifact.
            art = kwargs.get("cwd")
            if art is not None:
                (Path(art) / "JudgeProblem.olean").write_bytes(b"")
            return ok_proc
        raise forced_timeout
    _calls = 0
    with patch.object(_verify_module.subprocess, "run", side_effect=_side_effect):
        result = verify_answer(problem, raw_answer, config=base_config)

    ok = result["status"] == "incorrect" and result["error_code"] == "LEAN_TIMEOUT"
    results.append({
        "name": "verify_lean_compile_timeout_maps_to_incorrect",
        "ok": ok,
        "detail": (
            ""
            if ok
            else f"expected incorrect/LEAN_TIMEOUT, got {result['status']}/{result['error_code']}"
        ),
    })

    # Budget-contract end-to-end: the false-cert cap fielded on JudgeConfig
    # actually governs the verify_answer FALSE_CERT_TOO_LARGE branch. With
    # cap=10 KB a 15 KB false-cert must be rejected; with cap=20 KB the same
    # payload must clear the size gate (proving the value is read from
    # config, not from a hard-coded constant).
    big_false_code = "x" + ("y" * 14_999)  # 15_000 bytes
    raw_false = json.dumps({"verdict": "false", "code": big_false_code})

    cfg_strict = JudgeConfig(
        lean_bin=base_config.lean_bin,
        lake_bin=base_config.lake_bin,
        artifact_dir=base_config.artifact_dir,
        lean_timeout_seconds=base_config.lean_timeout_seconds,
        max_code_length=100_000,
        max_false_cert_bytes=10_000,
    )
    res_strict = verify_answer(problem, raw_false, config=cfg_strict)
    results.append({
        "name": "verify_false_cert_rejects_above_config_cap",
        "ok": (
            res_strict["status"] == "malformed"
            and res_strict["error_code"] == "FALSE_CERT_TOO_LARGE"
        ),
        "detail": (
            f"got {res_strict['status']}/{res_strict['error_code']}"
        ),
    })

    cfg_lenient = JudgeConfig(
        lean_bin=base_config.lean_bin,
        lake_bin=base_config.lake_bin,
        artifact_dir=base_config.artifact_dir,
        lean_timeout_seconds=base_config.lean_timeout_seconds,
        max_code_length=100_000,
        max_false_cert_bytes=20_000,
    )
    # Mock the Lean subprocess so we don't actually compile: any non-malformed
    # outcome here means the FALSE_CERT_TOO_LARGE gate did NOT fire — that's
    # what we're asserting (cap=20 KB admits a 15 KB blob).
    _calls = 0
    with patch.object(_verify_module.subprocess, "run", side_effect=_side_effect):
        res_lenient = verify_answer(problem, raw_false, config=cfg_lenient)
    results.append({
        "name": "verify_false_cert_accepts_under_config_cap",
        "ok": res_lenient.get("error_code") != "FALSE_CERT_TOO_LARGE",
        "detail": (
            f"got {res_lenient.get('status')}/{res_lenient.get('error_code')}"
        ),
    })
    return results


def run_loader_cases() -> list[dict[str, Any]]:
    """Regressions for ``pipeline.proxy.load_problems`` — the shared loader.

    The project ships two on-disk formats:
    * JSON array (``examples/problems_{20,200}.json`` — local samples)
    * JSONL (``examples/problems/*.jsonl`` — byte-identical HF mirror)

    Both callers (``pipeline.runner``, ``scripts/submit.py``) must round-trip
    either shape to the same ``list[dict]``. Malformed input must raise a
    caller-friendly ``ValueError`` instead of a cryptic ``JSONDecodeError``.
    """
    from pipeline.proxy import load_problems

    results: list[dict[str, Any]] = []

    def _record(name: str, ok: bool, detail: str = "") -> None:
        results.append({"name": name, "ok": ok, "detail": detail})

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        rows = [
            {"id": "a", "eq1_id": 1, "eq2_id": 2, "equation1": "x = x", "equation2": "x = x"},
            {"id": "b", "eq1_id": 3, "eq2_id": 4, "equation1": "x = y", "equation2": "y = x"},
        ]

        # JSON array path.
        arr_path = tmp_path / "set.json"
        arr_path.write_text(json.dumps(rows), encoding="utf-8")
        got_arr = load_problems(arr_path)
        _record(
            "loader_accepts_json_array",
            got_arr == rows,
            "" if got_arr == rows else f"got {got_arr!r}",
        )

        # JSONL path — one object per line, trailing newline, windows-style
        # CRLF between some lines to prove the splitter is tolerant.
        jsonl_path = tmp_path / "set.jsonl"
        jsonl_path.write_text(
            json.dumps(rows[0]) + "\r\n" + json.dumps(rows[1]) + "\n",
            encoding="utf-8",
        )
        got_jsonl = load_problems(jsonl_path)
        _record(
            "loader_accepts_jsonl",
            got_jsonl == rows,
            "" if got_jsonl == rows else f"got {got_jsonl!r}",
        )

        # Round-trip: both formats must decode to the same list.
        _record(
            "loader_array_and_jsonl_agree",
            got_arr == got_jsonl,
            "" if got_arr == got_jsonl else "array vs jsonl disagree",
        )

        # Blank lines inside JSONL must be skipped, not parsed as "null".
        blank_jsonl = tmp_path / "blanks.jsonl"
        blank_jsonl.write_text(
            "\n" + json.dumps(rows[0]) + "\n\n" + json.dumps(rows[1]) + "\n\n",
            encoding="utf-8",
        )
        got_blank = load_problems(blank_jsonl)
        _record(
            "loader_jsonl_skips_blank_lines",
            got_blank == rows,
            "" if got_blank == rows else f"got {got_blank!r}",
        )

        # Empty file → caller-friendly error, not "unexpected end of input".
        empty_path = tmp_path / "empty.jsonl"
        empty_path.write_text("", encoding="utf-8")
        try:
            load_problems(empty_path)
            _record("loader_empty_file_raises", False, "no exception raised")
        except ValueError as exc:
            _record(
                "loader_empty_file_raises",
                "empty" in str(exc).lower(),
                "" if "empty" in str(exc).lower() else f"message was {exc!r}",
            )

        # Bad JSONL line → error includes the file path and 1-based line no.
        bad_jsonl = tmp_path / "bad.jsonl"
        bad_jsonl.write_text(
            json.dumps(rows[0]) + "\n" + "{not json" + "\n" + json.dumps(rows[1]) + "\n",
            encoding="utf-8",
        )
        try:
            load_problems(bad_jsonl)
            _record("loader_bad_jsonl_line_reports_lineno", False, "no exception raised")
        except ValueError as exc:
            ok = ":2:" in str(exc) and "bad.jsonl" in str(exc)
            _record(
                "loader_bad_jsonl_line_reports_lineno",
                ok,
                "" if ok else f"message was {exc!r}",
            )

        # Top-level non-array JSON → rejected, not silently coerced.
        object_path = tmp_path / "object.json"
        object_path.write_text(json.dumps({"problems": rows}), encoding="utf-8")
        try:
            load_problems(object_path)
            _record("loader_rejects_top_level_object", False, "no exception raised")
        except ValueError:
            _record("loader_rejects_top_level_object", True)

    return results


def run_submit_cli_cases() -> list[dict[str, Any]]:
    """Regressions for scripts/submit.py — the colorized local CLI.

    The client wraps ``pipeline.proxy.run_solver`` without spawning a server,
    so the regressions patch ``run_solver`` to avoid subprocess/network work
    and verify: (a) argparse accepts the expected flag set, (b) ``--problem-ids``
    filters to the matching subset, (c) exit code is 0 iff every selected
    problem is solved, (d) output file is written when ``--output`` is set,
    (e) ``_style`` is a no-op when stdout is not a TTY.
    """
    import contextlib
    import importlib.util
    import io

    spec = importlib.util.spec_from_file_location(
        "submit_cli", ROOT / "scripts" / "submit.py"
    )
    submit_cli = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(submit_cli)

    @contextlib.contextmanager
    def _silence_stdout():
        buf_out, buf_err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(buf_out), contextlib.redirect_stderr(buf_err):
            yield

    results: list[dict[str, Any]] = []

    def _record(name: str, ok: bool, detail: str = "") -> None:
        results.append({"name": name, "ok": ok, "detail": detail})

    # Non-TTY passthrough. Our harness runs with stdout captured, so _isatty
    # is False and every color helper must return the string unchanged.
    ok_style = (
        submit_cli.GREEN("hi") == "hi"
        and submit_cli.RED("x") == "x"
        and submit_cli.BOLD("y") == "y"
    )
    _record(
        "submit_cli_style_non_tty_passthrough",
        ok_style,
        "" if ok_style else "ANSI escapes leaked into non-TTY output",
    )

    # _fmt_bytes must cover all three size buckets; a regression here would
    # mean the per-problem row shows numbers in the wrong unit.
    ok_bytes = (
        submit_cli._fmt_bytes(None) == "-"
        and submit_cli._fmt_bytes(512) == "512 B"
        and submit_cli._fmt_bytes(2048).endswith("KB")
        and submit_cli._fmt_bytes(5 * 1024 * 1024).endswith("MB")
    )
    _record("submit_cli_fmt_bytes_buckets", ok_bytes)

    # End-to-end: patch run_solver with a deterministic stub, feed a fake
    # problems.json, assert exit code + output file contents.
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        submission_dir = tmp_path / "sub"
        submission_dir.mkdir()
        (submission_dir / "solver.py").write_text("PROMPT = 'x'\n", encoding="utf-8")

        problems_path = tmp_path / "problems.json"
        problems_path.write_text(json.dumps([
            {"id": "p1", "eq1_id": 1, "eq2_id": 2, "equation1": "x = x", "equation2": "x = x"},
            {"id": "p2", "eq1_id": 3, "eq2_id": 4, "equation1": "x = x", "equation2": "x = x"},
            {"id": "p3", "eq1_id": 5, "eq2_id": 6, "equation1": "x = x", "equation2": "x = x"},
        ]), encoding="utf-8")

        results_path = tmp_path / "out.json"

        def fake_run_solver(_submission, problem, _config):
            return {
                "solved": problem["id"] in {"p1", "p3"},
                "verdict": "true" if problem["id"] in {"p1", "p3"} else None,
                "code": "",
                "llm_calls": 0,
                "judge_calls": 1,
                "log": [],
            }

        # Mixed success → exit 1.
        argv = [
            "submit.py",
            "--submission", str(submission_dir),
            "--problems", str(problems_path),
            "--output", str(results_path),
        ]
        with patch.object(submit_cli, "run_solver", side_effect=fake_run_solver), \
                patch.object(sys, "argv", argv), \
                _silence_stdout():
            rc_mixed = submit_cli.main()
        _record(
            "submit_cli_exit_1_when_not_all_solved",
            rc_mixed == 1,
            "" if rc_mixed == 1 else f"expected 1, got {rc_mixed}",
        )

        written = json.loads(results_path.read_text(encoding="utf-8"))
        ok_written = (
            isinstance(written, list)
            and len(written) == 3
            and sum(1 for r in written if r["solved"]) == 2
        )
        _record(
            "submit_cli_writes_output_json",
            ok_written,
            "" if ok_written else f"unexpected output shape: {written!r}",
        )

        # --problem-ids filter narrows to the matching subset, and when only
        # solvable ones are selected the exit code flips to 0.
        argv_filter = [
            "submit.py",
            "--submission", str(submission_dir),
            "--problems", str(problems_path),
            "--problem-ids", "p1,p3",
        ]
        with patch.object(submit_cli, "run_solver", side_effect=fake_run_solver), \
                patch.object(sys, "argv", argv_filter), \
                _silence_stdout():
            rc_all = submit_cli.main()
        _record(
            "submit_cli_exit_0_when_all_solved",
            rc_all == 0,
            "" if rc_all == 0 else f"expected 0 when filter selects only solvable, got {rc_all}",
        )

        # Non-matching --problem-ids must fail fast (exit 2), not crash.
        argv_empty = [
            "submit.py",
            "--submission", str(submission_dir),
            "--problems", str(problems_path),
            "--problem-ids", "nope",
        ]
        with patch.object(submit_cli, "run_solver", side_effect=fake_run_solver), \
                patch.object(sys, "argv", argv_empty), \
                _silence_stdout():
            rc_empty = submit_cli.main()
        _record(
            "submit_cli_exit_2_on_no_matching_ids",
            rc_empty == 2,
            "" if rc_empty == 2 else f"expected 2 for empty filter, got {rc_empty}",
        )

        # Partial-typo --problem-ids: at least one ID matches, at least one
        # does not. The old behaviour silently dropped the typo; the fix must
        # exit 2 and name the missing IDs on stderr.
        argv_partial = [
            "submit.py",
            "--submission", str(submission_dir),
            "--problems", str(problems_path),
            "--problem-ids", "p1,nope",
        ]
        partial_err = io.StringIO()
        with patch.object(submit_cli, "run_solver", side_effect=fake_run_solver), \
                patch.object(sys, "argv", argv_partial), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(partial_err):
            rc_partial = submit_cli.main()
        ok_partial = rc_partial == 2 and "nope" in partial_err.getvalue()
        _record(
            "submit_cli_partial_typo_exits_fatal",
            ok_partial,
            "" if ok_partial else (
                f"rc={rc_partial}, stderr={partial_err.getvalue()!r}"
            ),
        )

        # Empty problem set (valid JSON, empty array) must FATAL (exit 2)
        # rather than silently exit 0. The old code exited 0 because the
        # solved / total both equalled 0.
        empty_problems = tmp_path / "empty.json"
        empty_problems.write_text("[]", encoding="utf-8")
        argv_empty_set = [
            "submit.py",
            "--submission", str(submission_dir),
            "--problems", str(empty_problems),
        ]
        empty_err = io.StringIO()
        with patch.object(submit_cli, "run_solver", side_effect=fake_run_solver), \
                patch.object(sys, "argv", argv_empty_set), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(empty_err):
            rc_empty_set = submit_cli.main()
        ok_empty_set = rc_empty_set == 2 and "empty" in empty_err.getvalue().lower()
        _record(
            "submit_cli_empty_problem_set_exits_fatal",
            ok_empty_set,
            "" if ok_empty_set else (
                f"rc={rc_empty_set}, stderr={empty_err.getvalue()!r}"
            ),
        )

        # Atomic --output: if Path.write_text (non-atomic) were still in use,
        # a crash mid-write would leave a half-written file. With the atomic
        # helper the real target must never appear in a half-written state,
        # and a prior file must survive a mid-run crash intact.
        prior_path = tmp_path / "prior.json"
        prior_payload = '[{"id": "prior", "solved": true}]'
        prior_path.write_text(prior_payload, encoding="utf-8")

        def crashing_run_solver(_submission, _problem, _config):
            raise RuntimeError("synthetic mid-run crash")

        argv_crash = [
            "submit.py",
            "--submission", str(submission_dir),
            "--problems", str(problems_path),
            "--output", str(prior_path),
        ]
        with patch.object(submit_cli, "run_solver", side_effect=crashing_run_solver), \
                patch.object(sys, "argv", argv_crash), \
                _silence_stdout():
            try:
                submit_cli.main()
            except RuntimeError:
                pass
        survived = prior_path.read_text(encoding="utf-8") == prior_payload
        _record(
            "submit_cli_output_atomic_preserves_prior_on_crash",
            survived,
            "" if survived else "prior --output file clobbered by crashed run",
        )
        # No stray tmp file left behind.
        leftover = [
            p.name for p in prior_path.parent.iterdir()
            if p.name.startswith(f".{prior_path.name}.") and p.name.endswith(".tmp")
        ]
        _record(
            "submit_cli_output_atomic_no_tmp_litter",
            not leftover,
            "" if not leftover else f"tmp file survived crash: {leftover}",
        )

        # Per-stream TTY detection: _style must decide on the target stream,
        # not a module-level snapshot of stdout. A fake TTY stderr must get
        # ANSI even though the harness stdout is captured (non-TTY).
        class _FakeTTY(io.StringIO):
            def isatty(self) -> bool:
                return True

        fake_tty = _FakeTTY()
        coloured = submit_cli.RED("boom", fake_tty)
        plain = submit_cli.RED("boom")
        ok_stream = coloured.startswith("\033[31m") and plain == "boom"
        _record(
            "submit_cli_style_per_stream_tty",
            ok_stream,
            "" if ok_stream else f"coloured={coloured!r}, plain={plain!r}",
        )

    return results


def run_playground_cases() -> list[dict[str, Any]]:
    """Regressions for the SAIR-styled static local playground at ``playground/index.html``.

    This is a design-template artifact (not wired to a live server), so the
    regressions pin the shape rather than behavior: the file exists, parses as
    HTML without exception, contains the SAIR brand palette tokens, and ships
    the core form + results structure that a future server integration would
    bind to.

    Skipped silently when the playground is held back from the public repo
    (``playground/`` gitignored, dir absent on a clean clone).
    """
    import html.parser

    results: list[dict[str, Any]] = []

    if not (ROOT / "playground").is_dir():
        return results

    def _record(name: str, ok: bool, detail: str = "") -> None:
        results.append({"name": name, "ok": ok, "detail": detail})

    ui_path = ROOT / "playground" / "index.html"
    exists = ui_path.is_file()
    _record(
        "playground_file_exists",
        exists,
        "" if exists else f"missing: {ui_path}",
    )
    if not exists:
        return results

    text = ui_path.read_text(encoding="utf-8")

    class _Sink(html.parser.HTMLParser):
        def __init__(self):
            super().__init__()
            self.errors: list[str] = []

        def error(self, message: str) -> None:
            self.errors.append(message)

    sink = _Sink()
    parse_ok = True
    try:
        sink.feed(text)
    except Exception as exc:
        parse_ok = False
        sink.errors.append(str(exc))
    _record(
        "playground_html_parses",
        parse_ok and not sink.errors,
        "" if parse_ok and not sink.errors else "; ".join(sink.errors),
    )

    brand_tokens = ["#3b0e27", "--brand", "Helvetica Neue", "SAIR"]
    missing_brand = [t for t in brand_tokens if t not in text]
    _record(
        "playground_contains_sair_brand_tokens",
        not missing_brand,
        "" if not missing_brand else f"missing design tokens: {missing_brand}",
    )

    required_structure = [
        'id="submit-form"',
        'id="in-solver"',
        'id="job-panel"',
        'id="results-table"',
        'id="btn-submit"',
        'id="btn-mock"',
        'id="in-range-from"',
        'id="in-range-to"',
        'id="sel-problem-set"',
        'class="playground-tag"',
        'class="logo"',
        'value="normal"',
        'value="hard1"',
        'value="hard2"',
        'value="hard3"',
        "Submission",
        "Results",
        # Solo/Marathon track tabs (added 2026-05-01) — Marathon is a
        # static info panel pointing at the CLI; solo flow is unchanged.
        'id="tab-solo"',
        'id="tab-marathon"',
        'id="track-marathon"',
    ]
    missing_struct = [s for s in required_structure if s not in text]
    _record(
        "playground_core_structure_present",
        not missing_struct,
        "" if not missing_struct else f"missing: {missing_struct}",
    )

    # --ok must be distinct from --brand so accepted rows don't visually
    # collide with neutral brand chrome. Parse the two CSS values and
    # require inequality.
    ok_val = re.search(r"--ok:\s*([#0-9a-fA-F]+)\s*;", text)
    brand_val = re.search(r"--brand:\s*([#0-9a-fA-F]+)\s*;", text)
    ok_distinct = bool(
        ok_val and brand_val and ok_val.group(1).lower() != brand_val.group(1).lower()
    )
    _record(
        "playground_ok_token_distinct_from_brand",
        ok_distinct,
        "" if ok_distinct else (
            f"--ok={ok_val and ok_val.group(1)!r} must differ from "
            f"--brand={brand_val and brand_val.group(1)!r}"
        ),
    )

    # Accepted rows must render a check-mark glyph so success is readable
    # even at the edges of colour perception (deuteranopia, dim displays).
    has_check = "tr.accepted td.verdict::before" in text and "✓" in text
    _record(
        "playground_accepted_row_has_check_glyph",
        has_check,
        "" if has_check else "accepted rows missing check-mark ::before glyph",
    )

    # WCAG AA body-text contrast: --hint is used for helper text (labels,
    # placeholders). At the old #91919a on white it scored 3.22:1, below
    # the 4.5 AA threshold. Compute the contrast ratio and gate on 4.5.
    def _srgb_to_linear(c: float) -> float:
        return c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4

    def _rel_luminance(hex_color: str) -> float:
        h = hex_color.lstrip("#")
        r, g, b = (int(h[i:i + 2], 16) / 255.0 for i in (0, 2, 4))
        return (
            0.2126 * _srgb_to_linear(r)
            + 0.7152 * _srgb_to_linear(g)
            + 0.0722 * _srgb_to_linear(b)
        )

    def _contrast(fg: str, bg: str) -> float:
        l1, l2 = _rel_luminance(fg), _rel_luminance(bg)
        hi, lo = max(l1, l2), min(l1, l2)
        return (hi + 0.05) / (lo + 0.05)

    # Bundled SAIR problem sets must be a byte-identical JSONL mirror of the
    # upstream HuggingFace dataset: one JSON object per line, row counts that
    # match the published tree. Using JSONL lets users load the files via
    # `datasets.load_dataset` and compare with `wc -l`, instead of forcing a
    # format-conversion step.
    from pipeline.proxy import load_problems as _load_problems

    sair_dir = ROOT / "examples" / "problems"
    expected_counts = {"normal": 1000, "hard1": 69, "hard2": 200, "hard3": 400}
    sair_failures: list[str] = []
    for name, expected in expected_counts.items():
        path = sair_dir / f"{name}.jsonl"
        if not path.is_file():
            sair_failures.append(f"missing {path}")
            continue
        raw = path.read_text(encoding="utf-8")
        line_count = sum(1 for line in raw.splitlines() if line.strip())
        if line_count != expected:
            sair_failures.append(
                f"{name}: expected {expected} JSONL lines, got {line_count}"
            )
            continue
        try:
            data = _load_problems(path)
        except Exception as exc:
            sair_failures.append(f"{name}: load_problems failed ({exc})")
            continue
        if len(data) != expected:
            sair_failures.append(
                f"{name}: loader returned {len(data)} rows, expected {expected}"
            )
            continue
        sample = data[0]
        required = {"id", "eq1_id", "eq2_id", "equation1", "equation2"}
        missing = required - set(sample.keys())
        if missing:
            sair_failures.append(f"{name}: first row missing {sorted(missing)}")
    _record(
        "playground_sair_sets_bundled",
        not sair_failures,
        "; ".join(sair_failures),
    )

    # The selector resolves paths relative to playground/, so the symlink
    # (or copy) at playground/problems must exist and resolve to something
    # that contains the four JSONL sets.
    web_problems = ROOT / "playground" / "problems"
    has_link = web_problems.exists()
    has_all = has_link and all(
        (web_problems / f"{n}.jsonl").is_file() for n in expected_counts
    )
    _record(
        "playground_problems_symlink_resolves",
        has_all,
        "" if has_all else f"playground/problems missing or incomplete at {web_problems}",
    )

    # The playground JS must point at the new JSONL extension, otherwise a
    # regression to the old .json array extension would resolve to 404 at
    # runtime without any server-side signal.
    uses_jsonl = 'problems/hard1.jsonl' in text and 'problems/normal.jsonl' in text
    _record(
        "playground_selector_uses_jsonl_extension",
        uses_jsonl,
        "" if uses_jsonl else "playground/index.html must reference problems/*.jsonl",
    )

    contrast_failures: list[str] = []
    pairs = [
        ("--hint", "--bg"),
        ("--err", "--bg"),
        ("--warn", "--bg"),
        ("--ok", "--bg"),
    ]
    for fg_name, bg_name in pairs:
        fg_m = re.search(rf"{re.escape(fg_name)}:\s*(#[0-9a-fA-F]{{6}})\s*;", text)
        bg_m = re.search(rf"{re.escape(bg_name)}:\s*(#[0-9a-fA-F]{{6}})\s*;", text)
        if not (fg_m and bg_m):
            contrast_failures.append(f"{fg_name} or {bg_name} hex not found")
            continue
        ratio = _contrast(fg_m.group(1), bg_m.group(1))
        if ratio < 4.5:
            contrast_failures.append(
                f"{fg_name}={fg_m.group(1)} on {bg_name}={bg_m.group(1)} "
                f"contrast {ratio:.2f} < 4.5"
            )
    _record(
        "playground_wcag_aa_body_contrast",
        not contrast_failures,
        "; ".join(contrast_failures),
    )

    return results


def run_playground_server_cases() -> list[dict[str, Any]]:
    """Regressions for ``scripts/playground_server.py`` + equation index.

    The playground frontend depends on three server-side guarantees that are
    each easy to break in isolation:

    * the bundled ``equation_index.json`` stays non-empty and keeps schema v1;
    * ``_normalize_equation`` and ``build_equation_index.normalize`` use the
      exact same canonical form (any drift silently breaks lookups from the UI);
    * ``_resolve_static`` refuses path traversal and NUL-injected URLs instead
      of 500'ing;
    * ``_resolve_problems`` validates body shape, caps ``custom_problems``, and
      surfaces friendly errors instead of leaking tracebacks;
    * ``_read_json_body`` rejects non-dict payloads up front.

    These are unit-level — no real HTTP listener. Spinning up a socket each
    run invites port flakiness without adding coverage that the handler
    helpers don't already give us.

    Skipped silently when the playground is held back from the public repo.
    """
    results: list[dict[str, Any]] = []

    if not (ROOT / "scripts" / "playground_server.py").is_file():
        return results

    def _record(name: str, ok: bool, detail: str = "") -> None:
        results.append({"name": name, "ok": ok, "detail": detail})

    # Import the server module — it pulls pipeline.proxy, so surface a clear
    # harness failure rather than a cryptic import error below.
    try:
        import importlib.util
        server_path = ROOT / "scripts" / "playground_server.py"
        spec = importlib.util.spec_from_file_location("playground_server", server_path)
        server = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(server)
    except Exception as exc:  # noqa: BLE001
        _record("playground_server_imports", False, f"{type(exc).__name__}: {exc}")
        return results
    _record("playground_server_imports", True)

    # ── equation index shape ──
    index_path = ROOT / "playground" / "equation_index.json"
    if not index_path.is_file():
        _record("playground_equation_index_exists", False, f"missing {index_path}")
        return results
    _record("playground_equation_index_exists", True)

    payload = json.loads(index_path.read_text(encoding="utf-8"))
    schema_ok = payload.get("schema") == "v1"
    _record(
        "playground_equation_index_schema_v1",
        schema_ok,
        "" if schema_ok else f"schema={payload.get('schema')!r}",
    )
    entries = payload.get("entries") or {}
    # Coverage: the four SAIR JSONL sets alone contribute >2000 distinct
    # equations; the 2500 floor is a loose but real regression bound.
    count_ok = isinstance(entries, dict) and len(entries) >= 2500
    _record(
        "playground_equation_index_has_minimum_entries",
        count_ok,
        "" if count_ok else f"entries={len(entries) if isinstance(entries, dict) else 'non-dict'}",
    )

    # ── normalization parity: build_equation_index vs server ──
    # Any drift here silently breaks user lookups from the UI, since the
    # server normalizes the user input before looking it up in a table
    # built with the script's normalizer.
    import importlib.util as _u
    builder_path = ROOT / "scripts" / "build_equation_index.py"
    bspec = _u.spec_from_file_location("build_equation_index", builder_path)
    builder = _u.module_from_spec(bspec)
    assert bspec.loader is not None
    bspec.loader.exec_module(builder)
    parity_cases = [
        "x = y ◇ x",
        "  x   ◇   y = y  ",
        "x * y = y * x",
        "x\t◇\ty = y",
    ]
    parity_mismatches = [
        (s, server._normalize_equation(s), builder.normalize(s))
        for s in parity_cases
        if server._normalize_equation(s) != builder.normalize(s)
    ]
    _record(
        "playground_normalize_equation_parity_with_builder",
        not parity_mismatches,
        "" if not parity_mismatches else f"drift: {parity_mismatches}",
    )

    # ── equation lookup happy path ──
    # The very first SAIR problem uses Equation5 as equation1. The text
    # there is ``x = y ◇ x``; after normalization this must resolve to 5.
    eid = server._lookup_equation_id("x = y ◇ x")
    _record(
        "playground_equation_lookup_hits_known_id",
        eid == 5,
        "" if eid == 5 else f"got {eid!r}, expected 5",
    )

    # Whitespace / ◇-vs-* variations must normalize to the same id.
    variants = ["x = y ◇ x", "x = y * x", "  x   =   y   *   x  "]
    ids = [server._lookup_equation_id(v) for v in variants]
    _record(
        "playground_equation_lookup_normalizes_variants",
        all(i == ids[0] and i is not None for i in ids),
        "" if all(i == ids[0] and i is not None for i in ids) else f"got {ids}",
    )

    # ── _resolve_static path safety ──
    traversal_inputs = [
        "/../pipeline/config.json",
        "/./../README.md",
        "/playground/../README.md",
        "/\x00",
        "/%2E%2E/",       # literal segment, not decoded — should still miss
        "/../../etc/passwd",
    ]
    traversal_fails = []
    for t in traversal_inputs:
        try:
            out = server._resolve_static(t)
        except Exception as exc:  # noqa: BLE001
            traversal_fails.append(f"{t!r} raised {type(exc).__name__}: {exc}")
            continue
        if out is not None:
            traversal_fails.append(f"{t!r} resolved to {out!s}")
    _record(
        "playground_resolve_static_refuses_traversal",
        not traversal_fails,
        "; ".join(traversal_fails),
    )

    # Suffix allowlist: a .py file inside the playground dir should never
    # be served — the allowlist is the second line of defense after the
    # allowed-roots check.
    with tempfile.NamedTemporaryFile(
        dir=ROOT / "playground", suffix=".py", delete=False
    ) as fh:
        temp_py = Path(fh.name)
        fh.write(b"secret = True\n")
    try:
        resolved = server._resolve_static(f"/{temp_py.name}")
    finally:
        temp_py.unlink(missing_ok=True)
    _record(
        "playground_resolve_static_rejects_py_suffix",
        resolved is None,
        "" if resolved is None else f"served {resolved}",
    )

    # ── _resolve_problems validation ──
    try:
        server._resolve_problems({"problem_set": "nope"})
        raised = None
    except ValueError as exc:
        raised = str(exc)
    _record(
        "playground_resolve_problems_unknown_preset_error",
        raised is not None and "unknown" in raised.lower(),
        f"got {raised!r}",
    )

    try:
        server._resolve_problems({})
        raised = None
    except ValueError as exc:
        raised = str(exc)
    _record(
        "playground_resolve_problems_empty_body_error",
        raised is not None,
        f"got {raised!r}",
    )

    # custom_problems cap: MAX_CUSTOM_PROBLEMS+1 entries must be refused
    # before any Lean work starts.
    too_many = [
        {"equation1": "x = x", "equation2": "x = x"}
        for _ in range(server.MAX_CUSTOM_PROBLEMS + 1)
    ]
    try:
        server._resolve_problems({"custom_problems": too_many})
        raised = None
    except ValueError as exc:
        raised = str(exc)
    _record(
        "playground_resolve_problems_caps_custom_problems",
        raised is not None and "capped" in raised.lower(),
        f"got {raised!r}",
    )

    # custom_problems non-list must be rejected with a caller-friendly error,
    # not a TypeError.
    try:
        server._resolve_problems({"custom_problems": "not a list"})
        raised = None
    except ValueError as exc:
        raised = str(exc)
    _record(
        "playground_resolve_problems_custom_must_be_list",
        raised is not None and "list" in raised.lower(),
        f"got {raised!r}",
    )

    # An entry missing a field must be flagged with its 1-based index, so the
    # frontend can highlight the offending line.
    try:
        server._resolve_problems({"custom_problems": [{"equation1": "x = x"}]})
        raised = None
    except ValueError as exc:
        raised = str(exc)
    _record(
        "playground_resolve_problems_reports_missing_field",
        raised is not None and "#1" in raised,
        f"got {raised!r}",
    )

    # An equation text that isn't in the index must produce a caller-friendly
    # 'not found' message, not a KeyError.
    try:
        server._resolve_problems({
            "custom_problems": [
                {"equation1": "totally bogus equation zzz", "equation2": "x = x"}
            ]
        })
        raised = None
    except ValueError as exc:
        raised = str(exc)
    _record(
        "playground_resolve_problems_reports_missing_equation",
        raised is not None and "not found" in raised.lower(),
        f"got {raised!r}",
    )

    # ── _apply_overrides bounds + echo ──
    # Overrides must be clamped (10–600 for solver, 5–600 for lean) so a
    # malicious or buggy UI can't pin a Lean compile for an hour. The
    # applied list echoes back to the client for "what actually ran".
    cfg = {"solver": {"timeout_seconds": 120}, "judge": {"lean_timeout_seconds": 60}}
    applied = server._apply_overrides(cfg, {"solver_timeout_seconds": 45})
    ok_under = cfg["solver"]["timeout_seconds"] == 45 and any("45" in a for a in applied)
    _record("playground_apply_overrides_respects_valid",
            ok_under, f"cfg={cfg}, applied={applied}")

    cfg = {"solver": {"timeout_seconds": 120}, "judge": {"lean_timeout_seconds": 60}}
    server._apply_overrides(cfg, {"solver_timeout_seconds": 99999})
    ok_clamp_high = cfg["solver"]["timeout_seconds"] == 600
    _record("playground_apply_overrides_clamps_high",
            ok_clamp_high, f"expected 600, got {cfg['solver']['timeout_seconds']}")

    cfg = {"solver": {"timeout_seconds": 120}, "judge": {"lean_timeout_seconds": 60}}
    server._apply_overrides(cfg, {"solver_timeout_seconds": 1})
    ok_clamp_low = cfg["solver"]["timeout_seconds"] == 10
    _record("playground_apply_overrides_clamps_low",
            ok_clamp_low, f"expected 10, got {cfg['solver']['timeout_seconds']}")

    cfg = {"solver": {"timeout_seconds": 120}, "judge": {"lean_timeout_seconds": 60}}
    server._apply_overrides(cfg, {"solver_timeout_seconds": "bad"})
    ok_reject = cfg["solver"]["timeout_seconds"] == 120
    _record("playground_apply_overrides_ignores_non_numeric",
            ok_reject, f"expected unchanged 120, got {cfg['solver']['timeout_seconds']}")

    return results


def run_judge_internal_cases() -> list[dict[str, Any]]:
    """Unit-style checks for judge.verify internal helpers that back the public contract.

    Each check corresponds to a previously-observed failure mode:
      - `*→◇` normalization brittleness caused the entire v1-v20 solver chain to
        fail silently when raw HuggingFace text reached Lean.
      - `MAX_CODE_LENGTH` must be bytes, not Python chars; `◇` is 3 UTF-8 bytes.
      - `_strip_paths` hides the organizer's absolute artifact paths from any
        contestant-visible stderr.
      - `_render_problem_source` uses `example` (anonymous) so the judge cannot
        accidentally shadow a contestant-chosen name.
      - `_equation_def` generates per-problem equation abbreviations from
        problem text; sanitization keeps organizer data from becoming a
        Lean-injection channel.
    """
    results: list[dict[str, Any]] = []

    def _record(name: str, ok: bool, detail: str = "") -> None:
        results.append({"name": name, "ok": ok, "detail": detail})

    cases = [
        ("x = y * z", "x = y ◇ z"),
        ("x=y*z", "x=y◇z"),
        ("x*x = (y*z)*w", "x◇x = (y◇z)◇w"),
        ("x ◇ y = z * w", "x ◇ y = z ◇ w"),
        ("x ◇ y = z ◇ w", "x ◇ y = z ◇ w"),
    ]
    for raw, expected in cases:
        got = _normalize_equation_text(raw)
        ok = got == expected
        _record(
            f"judge_normalize_equation_{raw!r}",
            ok,
            "" if ok else f"expected {expected!r}, got {got!r}",
        )

    try:
        from judge.verify import _parse_answer_payload
        diamonds = "◇" * 20_000
        code = f"theorem submission : True := by trivial -- {diamonds}"
        assert len(code) < MAX_CODE_LENGTH
        assert len(code.encode("utf-8")) > MAX_CODE_LENGTH
        spec, early = _parse_answer_payload(json.dumps({"verdict": "true", "code": code}))
        ok = spec is None and early.get("error_code") == "CODE_TOO_LONG"
        _record(
            "judge_code_too_long_uses_bytes",
            ok,
            "" if ok else f"expected CODE_TOO_LONG on UTF-8 byte overflow, got {early}",
        )
    except Exception as e:  # noqa: BLE001
        _record("judge_code_too_long_uses_bytes", False, f"raised: {e}")

    # Budget contract: the size caps advertised to the solver in the startup
    # message must equal the values the judge actually enforces. Previously
    # ``pipeline/config.json`` declared 100 KB / 20 KB / 300 s but the judge
    # silently kept hard-coded 50 KB / 10 KB / 120 s, so a 60 KB true proof
    # or 15 KB false-cert promised by the contract was rejected by the judge.
    try:
        from judge.verify import JudgeConfig, _parse_answer_payload
        cfg_path = ROOT / "pipeline" / "config.json"
        with cfg_path.open("r", encoding="utf-8") as fh:
            cfg = json.load(fh)
        judge_cfg = cfg["judge"]
        cfg_code = int(judge_cfg["max_code_length"])
        cfg_false = int(judge_cfg["max_false_cert_bytes"])
        cfg_lean_to = int(judge_cfg["lean_timeout_seconds"])

        # JudgeConfig must accept the three caps as fields (the type contract).
        jc = JudgeConfig(
            max_code_length=cfg_code,
            max_false_cert_bytes=cfg_false,
            lean_timeout_seconds=cfg_lean_to,
        )
        _record(
            "judge_config_carries_three_budget_fields",
            jc.max_code_length == cfg_code
            and jc.max_false_cert_bytes == cfg_false
            and jc.lean_timeout_seconds == cfg_lean_to,
            f"jc={jc!r}",
        )

        # A 60 KB true proof must pass the size check at the config cap.
        # 50 KB padding inside a 60 KB blob is still > the legacy 50 KB
        # default, so a regression to the hard-coded constant would reject
        # it and break this assertion.
        big_true = "by trivial -- " + ("X" * 59_500)
        assert len(big_true.encode("utf-8")) > 50_000
        assert len(big_true.encode("utf-8")) <= cfg_code
        spec_t, early_t = _parse_answer_payload(
            json.dumps({"verdict": "true", "code": big_true}),
            max_code_length=cfg_code,
        )
        _record(
            "judge_parse_accepts_true_proof_at_config_cap",
            spec_t is not None and not early_t,
            f"early={early_t}",
        )

        # A 15 KB false-cert must pass when config cap is 20 KB. We can't
        # exercise the verify_answer path without a real Lean compile, but
        # we can confirm the cap field is wired through by constructing a
        # JudgeConfig and checking parse-time bound is the larger value.
        big_false_size = 15_000
        big_false = "x" + ("y" * (big_false_size - 1))
        assert len(big_false.encode("utf-8")) == big_false_size
        spec_f, early_f = _parse_answer_payload(
            json.dumps({"verdict": "false", "code": big_false}),
            max_code_length=cfg_code,
        )
        # parse-level cap is max_code_length; the false-cert specific cap
        # is enforced inside verify_answer and is checked in the verify-branch
        # tests via a real call. Here we just assert the parse pipeline
        # admits a 15 KB blob given the config cap.
        _record(
            "judge_parse_accepts_false_cert_at_config_cap",
            spec_f is not None and not early_f,
            f"early={early_f}",
        )
    except Exception as e:  # noqa: BLE001
        _record("judge_config_carries_three_budget_fields", False, f"raised: {e}")

    sample_stderr = (
        f"{ROOT}/.artifacts/p_foo.abc123/Submission.lean:3:12: error: type mismatch\n"
        f"context: {ROOT}/some/path"
    )
    stripped = _strip_paths(sample_stderr, art_dir=ROOT / ".artifacts" / "p_foo.abc123")
    ok_strip = (
        "/.artifacts/" not in stripped
        and str(ROOT) not in stripped
        and "Submission.lean:3:12" in stripped
    )
    _record(
        "judge_strip_paths_hides_artifact_absolute_path",
        ok_strip,
        "" if ok_strip else f"paths leaked through: {stripped!r}",
    )

    # Problem.lean should be anonymous (``example : Goal := submission``) and
    # must not drag in ``equational_theories`` — the project is self-contained.
    src = _render_problem_source(nonce="n0")
    _record(
        "judge_problem_uses_anonymous_example",
        "theorem judge_verify" not in src
        and "example :" in src
        and "equational_theories" not in src,
        f"src head: {src[:120]!r}",
    )

    # `_equation_def` interpolates problem text verbatim into Lean source.
    # Organizer-side data is trusted but the validator still rejects anything
    # outside the declared grammar so malformed fixtures fail loudly rather
    # than silently forging Lean declarations.
    clean_cases = [
        ("Eq1", "x = y ◇ x"),
        ("Eq2", "x ◇ y = y ◇ ((y ◇ x) ◇ y)"),
        ("Eq3", "x = x"),
    ]
    for name, text in clean_cases:
        try:
            out = _equation_def(name, text)
            ok = (
                out.startswith("@[reducible] def ")
                and f" {name} " in out
                and text in out
            )
            _record(f"judge_equation_def_clean_{name}", ok, out[:80])
        except Exception as exc:  # noqa: BLE001
            _record(f"judge_equation_def_clean_{name}", False, f"raised {type(exc).__name__}: {exc}")

    injection_cases = [
        ("LhsInj", "x = x\nunsafe def evil := 0"),
        ("LhsInj", "x = x -- hidden"),
        ("LhsInj", "x = y; #eval 1"),
        ("LhsInj", 'x = x"'),
        ("LhsInj", "x = x\\n"),
        ("LhsInj", "x = f(y)"),  # 'f' is not a lowercase single-letter variable but f char allowed, however this tests parentheses grammar + multi-letter name
        ("LhsInj", "x = x)"),     # unbalanced parens
        ("LhsInj", "x = (x"),
        ("BadName", "x = x"),     # name must match the identifier rule; BadName is valid — use below
    ]
    disallowed_chars_only = [
        "x = x\nunsafe def evil := 0",
        "x = x -- hidden",
        "x = y; #eval 1",
        'x = x"',
        "x = x\\n",
    ]
    for text in disallowed_chars_only:
        try:
            _equation_def("LhsInj", text)
            _record(
                f"judge_equation_def_rejects_chars_{text[:20]!r}",
                False,
                "accepted disallowed characters",
            )
        except JudgeConfigurationError:
            _record(f"judge_equation_def_rejects_chars_{text[:20]!r}", True)
        except Exception as exc:  # noqa: BLE001
            _record(
                f"judge_equation_def_rejects_chars_{text[:20]!r}",
                False,
                f"raised {type(exc).__name__}: {exc}",
            )

    for text in ("x = x)", "x = (x", "x = ((x)"):
        try:
            _equation_def("LhsInj", text)
            _record(
                f"judge_equation_def_rejects_parens_{text!r}",
                False,
                "accepted unbalanced parens",
            )
        except JudgeConfigurationError:
            _record(f"judge_equation_def_rejects_parens_{text!r}", True)
        except Exception as exc:  # noqa: BLE001
            _record(
                f"judge_equation_def_rejects_parens_{text!r}",
                False,
                f"raised {type(exc).__name__}: {exc}",
            )

    for name in ("1Bad", "has space", "open Namespace", ""):
        try:
            _equation_def(name, "x = x")
            _record(
                f"judge_equation_def_rejects_name_{name!r}",
                False,
                "accepted bad name",
            )
        except JudgeConfigurationError:
            _record(f"judge_equation_def_rejects_name_{name!r}", True)
        except Exception as exc:  # noqa: BLE001
            _record(
                f"judge_equation_def_rejects_name_{name!r}",
                False,
                f"raised {type(exc).__name__}: {exc}",
            )

    # Regression for PR #1: `_parse_report` previously called `.get("nonce")`
    # without checking that the JSON payload was a dict, crashing with
    # AttributeError on `null`, arrays, strings, numbers, booleans. Any such
    # line on stdout (currently unreachable from contestant code, but possible
    # from future Lean/mathlib stdout channels) must be skipped, not crash.
    try:
        from judge.verify import _parse_report
        for payload in ("null", "[1,2,3]", '"str"', "42", "true"):
            try:
                _parse_report(f"JUDGE_REPORT {payload}\n", "nonce-x")
                crashed = False
            except JudgeInfrastructureError:
                crashed = False  # expected: no valid report → infra error
            except Exception as exc:  # noqa: BLE001
                crashed = True
                _record(
                    f"judge_parse_report_nondict_{payload}",
                    False,
                    f"raised {type(exc).__name__}: {exc}",
                )
                continue
            _record(f"judge_parse_report_nondict_{payload}", True)
        # Positive control: a valid dict payload must still round-trip.
        valid = '{"nonce":"nonce-x","axioms":[],"direct_declarations":[]}'
        got = _parse_report(f"JUDGE_REPORT {valid}\n", "nonce-x")
        _record(
            "judge_parse_report_valid_dict_roundtrips",
            isinstance(got, dict) and got.get("nonce") == "nonce-x",
            "" if isinstance(got, dict) else f"got {got!r}",
        )
    except Exception as exc:  # noqa: BLE001
        _record("judge_parse_report_nondict_suite", False, f"suite raised: {exc}")

    return results


def run_banned_token_cases() -> list[dict[str, Any]]:
    """Scanner-level regressions for judge.verify._find_banned_token.

    These tests pin down the expanded banned-token list (meta-programming,
    #-commands, and unsafe declaration attributes) and the dual matching
    strategy: `#`-prefixed tokens use substring match (`#` is not a word
    character), while identifier tokens use word-boundaries so
    ``syntaxExtensions`` is not falsely rejected.
    """
    results: list[dict[str, Any]] = []

    def _record(name: str, ok: bool, detail: str = "") -> None:
        results.append({"name": name, "ok": ok, "detail": detail})

    required = {
        "sorry", "admit", "sorryAx", "mkSorry",
        "dbg_trace", "dbgTrace",
        "run_tac", "initialize", "builtin_initialize",
        "#eval", "#exit", "#reduce", "#synth", "#check_eval",
        "elab", "elab_rules", "macro", "macro_rules", "syntax",
        "unsafe", "unsafeCast", "unsafeIO", "unsafePerformIO",
        "implemented_by", "extern",
    }
    missing = sorted(required - set(BANNED_PROOF_TOKENS))
    _record(
        "banned_tokens_required_set_present",
        not missing,
        "" if not missing else f"missing from BANNED_PROOF_TOKENS: {missing}",
    )

    # Each new token must be detected in a minimal positive sample.
    positive_samples: dict[str, str] = {
        "#eval": "theorem t : True := by\n  #eval 1 + 1\n  trivial\n",
        "#exit": "#exit\ntheorem t : True := trivial\n",
        "#reduce": "#reduce (1 + 1)\ntheorem t : True := trivial\n",
        "#synth": "#synth Inhabited Nat\ntheorem t : True := trivial\n",
        "#check_eval": "#check_eval 1\ntheorem t : True := trivial\n",
        "elab": "elab \"x\" : tactic => pure ()\ntheorem t : True := trivial\n",
        "elab_rules": "elab_rules | `(tactic| z) => pure ()\ntheorem t : True := trivial\n",
        "macro": "macro \"c\" : tactic => `(tactic| trivial)\ntheorem t : True := by c\n",
        "macro_rules": "macro_rules | `(tactic| z) => `(tactic| trivial)\ntheorem t : True := trivial\n",
        "syntax": "syntax \"z\" : tactic\ntheorem t : True := trivial\n",
        "unsafe": "unsafe def bad : Nat := 0\ntheorem t : True := trivial\n",
        "unsafeCast": "theorem t : True := by exact @unsafeCast _ _ ()\n",
        "unsafeIO": "theorem t : True := by exact unsafeIO (pure ())\n",
        "unsafePerformIO": "theorem t : True := by exact unsafePerformIO (pure ())\n",
        "implemented_by": "@[implemented_by foo] def bar : Nat := 0\ntheorem t : True := trivial\n",
        "extern": "@[extern \"c\"] def bar : Nat := 0\ntheorem t : True := trivial\n",
        "mkSorry": "theorem t : True := by exact mkSorry\n",
    }
    for token, code in positive_samples.items():
        hit = _find_banned_token(code)
        ok = hit is not None
        _record(
            f"banned_token_detected_{token.replace('#', 'hash_')}",
            ok,
            "" if ok else f"token {token!r} was not detected in sample",
        )

    # Identifier tokens must be word-bounded so legitimate-looking longer
    # identifiers are NOT rejected.
    word_bounded_negatives = {
        "elaborate": "def elaborate (x : Nat) : Nat := x\n",
        "macroLike": "def macroLike (x : Nat) : Nat := x\n",
        "syntaxTree": "def syntaxTree (x : Nat) : Nat := x\n",
        "externalConfig": "def externalConfig : Nat := 0\n",
        "unsafeCastLike": "def unsafeCastLike (x : Nat) : Nat := x\n",
    }
    for label, code in word_bounded_negatives.items():
        hit = _find_banned_token(code)
        ok = hit is None
        _record(
            f"banned_token_word_bounded_{label}",
            ok,
            "" if ok else f"false positive: matched {hit!r} inside longer identifier",
        )

    # `#`-prefixed tokens must be matched via substring even when they
    # sit flush against punctuation (they are not word-bounded because
    # `#` is not a word character).
    hash_positive = _find_banned_token("(#eval 1)\n")
    _record(
        "banned_token_hash_prefix_substring_match",
        hash_positive == "#eval",
        ""
        if hash_positive == "#eval"
        else f"expected #eval, got {hash_positive!r}",
    )

    return results


def main() -> int:
    global ARTIFACT_ROOT, CHALLENGER_ARTIFACT_ROOT
    artifact_run_dir: Path | None = None
    challenger_run_dir: Path | None = None
    try:
        manifest = load_manifest()
        # Per-run unique subdirs prevent two harness invocations from
        # rmtree'ing each other's Lean artifacts mid-run (observed:
        # ``unknown module prefix JudgeProblem`` when a sibling process
        # cleared the shared dir). mkdtemp ensures uniqueness; we clean
        # it up in the finally block so the parent doesn't accumulate.
        ARTIFACT_PARENT.mkdir(parents=True, exist_ok=True)
        CHALLENGER_ARTIFACT_PARENT.mkdir(parents=True, exist_ok=True)
        artifact_run_dir = Path(tempfile.mkdtemp(
            prefix=f"run-{os.getpid()}-", dir=str(ARTIFACT_PARENT)))
        challenger_run_dir = Path(tempfile.mkdtemp(
            prefix=f"run-{os.getpid()}-", dir=str(CHALLENGER_ARTIFACT_PARENT)))
        ARTIFACT_ROOT = artifact_run_dir
        CHALLENGER_ARTIFACT_ROOT = challenger_run_dir

        # Let _resolve_config read env vars (LEAN_BIN, LAKE_BIN, etc.)
        # then override artifact_dir for harness isolation.
        env_config = _resolve_config(None)
        base_config = JudgeConfig(
            lake_bin=env_config.lake_bin,
            lean_bin=env_config.lean_bin,
            artifact_dir=ARTIFACT_ROOT,
            lean_timeout_seconds=env_config.lean_timeout_seconds,
        )
        case_results = run_cases(manifest["cases"], base_config)

        repeat_names = set(manifest.get("repeatability_cases", []))
        repeat_runs = int(manifest.get("repeatability_runs", 3))
        repeatability_results = [
            run_repeatability(case, base_config, repeat_runs)
            for case in manifest["cases"]
            if case["name"] in repeat_names
        ]
        challenger_summary = run_challenger_suite(artifact_dir=CHALLENGER_ARTIFACT_ROOT)
        pipeline_results = run_pipeline_prompt_cases()
        verify_branch_results = run_verify_branch_cases(base_config)
        judge_internal_results = run_judge_internal_cases()
        banned_token_results = run_banned_token_cases()
        submit_cli_results = run_submit_cli_cases()
        playground_results = run_playground_cases()
        playground_server_results = run_playground_server_cases()
        loader_results = run_loader_cases()

        failing_cases = [case for case in case_results if not case["ok"]]
        failing_repeatability = [item for item in repeatability_results if not item["ok"]]
        failing_pipeline = [item for item in pipeline_results if not item["ok"]]
        failing_verify_branch = [item for item in verify_branch_results if not item["ok"]]
        failing_judge_internal = [item for item in judge_internal_results if not item["ok"]]
        failing_banned_token = [item for item in banned_token_results if not item["ok"]]
        failing_submit_cli = [item for item in submit_cli_results if not item["ok"]]
        failing_playground = [item for item in playground_results if not item["ok"]]
        failing_playground_server = [item for item in playground_server_results if not item["ok"]]
        failing_loader = [item for item in loader_results if not item["ok"]]
        challenger_failed = bool(
            challenger_summary["failing_public_attacks"]
            or challenger_summary["failing_infra_attacks"]
            or challenger_summary.get("failing_false_negatives")
        )
        summary = {
            "case_count": len(case_results),
            "passed_case_count": sum(1 for case in case_results if case["ok"]),
            "repeatability_count": len(repeatability_results),
            "passed_repeatability_count": sum(1 for item in repeatability_results if item["ok"]),
            "pipeline_count": len(pipeline_results),
            "passed_pipeline_count": sum(1 for item in pipeline_results if item["ok"]),
            "verify_branch_count": len(verify_branch_results),
            "passed_verify_branch_count": sum(1 for item in verify_branch_results if item["ok"]),
            "judge_internal_count": len(judge_internal_results),
            "passed_judge_internal_count": sum(1 for item in judge_internal_results if item["ok"]),
            "banned_token_count": len(banned_token_results),
            "passed_banned_token_count": sum(1 for item in banned_token_results if item["ok"]),
            "submit_cli_count": len(submit_cli_results),
            "passed_submit_cli_count": sum(1 for item in submit_cli_results if item["ok"]),
            "playground_count": len(playground_results),
            "passed_playground_count": sum(1 for item in playground_results if item["ok"]),
            "playground_server_count": len(playground_server_results),
            "passed_playground_server_count": sum(1 for item in playground_server_results if item["ok"]),
            "loader_count": len(loader_results),
            "passed_loader_count": sum(1 for item in loader_results if item["ok"]),
            "failing_cases": failing_cases,
            "failing_repeatability": failing_repeatability,
            "failing_pipeline": failing_pipeline,
            "failing_verify_branch": failing_verify_branch,
            "failing_judge_internal": failing_judge_internal,
            "failing_banned_token": failing_banned_token,
            "failing_submit_cli": failing_submit_cli,
            "failing_playground": failing_playground,
            "failing_playground_server": failing_playground_server,
            "failing_loader": failing_loader,
            "challenger": challenger_summary,
        }

        # README baseline self-check runs AFTER the summary is built so the
        # comparison uses the live ``passed_*_count`` fields rather than a
        # second hard-coded dict that could go stale alongside README.md.
        readme_results = run_readme_consistency_check(summary)
        failing_readme = [item for item in readme_results if not item["ok"]]
        summary["readme_consistency_count"] = len(readme_results)
        summary["passed_readme_consistency_count"] = sum(1 for item in readme_results if item["ok"])
        summary["failing_readme_consistency"] = failing_readme

        print(json.dumps(summary, indent=2, sort_keys=True))
        all_ok = (
            not failing_cases
            and not failing_repeatability
            and not failing_pipeline
            and not failing_verify_branch
            and not failing_judge_internal
            and not failing_banned_token
            and not failing_submit_cli
            and not failing_playground
            and not failing_playground_server
            and not failing_loader
            and not failing_readme
            and not challenger_failed
        )
        return 0 if all_ok else 1
    except (JudgeConfigurationError, JudgeInfrastructureError) as exc:
        print(str(exc), file=sys.stderr)
        return 2
    finally:
        # Tear down the per-run artifact dirs so the parent does not grow
        # without bound. Best-effort: a stale dir from a crashed harness
        # leaves the same .gitignored .artifacts/ tree behind, which the
        # next invocation will simply ignore (it gets its own mkdtemp).
        for run_dir in (artifact_run_dir, challenger_run_dir):
            if run_dir is None:
                continue
            try:
                if run_dir.exists():
                    shutil.rmtree(run_dir, ignore_errors=True)
            except Exception:
                pass


if __name__ == "__main__":
    raise SystemExit(main())
