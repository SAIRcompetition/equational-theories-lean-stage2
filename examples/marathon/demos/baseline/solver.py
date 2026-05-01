"""
Marathon baseline solver — sequential, deterministic, no LLM.

Acts as the contract reference and the smoke baseline for marathon mode.
Two operating modes, dispatched by env vars:

    JUDGE_MARATHON_MANIFEST set  → marathon: read manifest, write JSONL
    (env vars unset)             → Solo: stdin/stdout JSON protocol

Strategy (both modes):

    For every problem, run a small finite-magma brute-force search up to
    Fin 3. If a counterexample is found, emit a "false" certificate using
    JudgeFinOp's ``finOpTable`` + ``decideFin!`` (same shape as
    examples/solo/demos/baseline). If no counterexample is found in the
    allotted slice, skip the problem (it will be reported as
    ``not_attempted`` in the marathon summary).

This baseline does not call the LLM and does not aim to maximize score —
it exists to prove the marathon E2E pipeline runs cleanly. Real solvers
(triage, fewshot) build on top of this contract.
"""

PROMPT = """You are solving equational theory problems in Lean 4.

Does {problem.equation1_id} imply {problem.equation2_id}?
Hypothesis: {problem.equation1}
Goal: {problem.equation2}

If true, provide a proof body (tactics only).
If false, provide a counterexample table on Fin N.

Previous attempts:
{history.attempts}

Respond with ONLY JSON, no markdown:
{"verdict": "true", "proof": "<tactic body>"}
or
{"verdict": "false", "counterexample_table": [[0,1],[1,0]]}
"""


import json
import os
import re
import sys
import time
from itertools import product


# ───────── Equation parsing & brute-force counterexample search ─────────

def _parse_equation(text):
    variables = []
    seen = set()
    for v in re.findall(r"\b([a-z])\b", text):
        if v not in seen:
            seen.add(v)
            variables.append(v)
    lhs_str, rhs_str = text.split("=", 1)

    def _to_expr(s):
        s = s.strip()
        while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
            depth = 0
            matched = True
            for i, c in enumerate(s):
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                if depth == 0 and i < len(s) - 1:
                    matched = False
                    break
            if matched:
                s = s[1:-1].strip()
            else:
                break
        depth = 0
        last_op = -1
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            elif c == "\u25c7" and depth == 0:
                last_op = i
        if last_op >= 0:
            left = _to_expr(s[:last_op])
            right = _to_expr(s[last_op + 1:])
            return lambda env, l=left, r=right: env["op"](l(env), r(env))
        s = s.strip()
        if len(s) == 1 and s in seen:
            return lambda env, v=s: env[v]
        raise ValueError(f"cannot parse: {s!r}")

    return variables, _to_expr(lhs_str), _to_expr(rhs_str)


def _check_eq(variables, lhs_fn, rhs_fn, n, op):
    for vals in product(range(n), repeat=len(variables)):
        env = {"op": op}
        for v, val in zip(variables, vals):
            env[v] = val
        if lhs_fn(env) != rhs_fn(env):
            return False
    return True


def search_counterexample(eq1_text, eq2_text, max_n=3, time_budget=None):
    """Brute-force enumerate Magma tables on Fin 2..max_n.

    Returns ``(n, table)`` for the first table that satisfies ``eq1`` and
    refutes ``eq2``, or ``(None, None)`` if no such table exists in the
    search space (or the time budget runs out).
    """
    try:
        lhs_vars, lhs_l, lhs_r = _parse_equation(eq1_text)
        rhs_vars, rhs_l, rhs_r = _parse_equation(eq2_text)
    except (ValueError, IndexError):
        return None, None
    deadline = (time.monotonic() + time_budget) if time_budget else None
    for n in range(2, max_n + 1):
        total = n ** (n * n)
        for enc in range(total):
            if deadline is not None and time.monotonic() > deadline:
                return None, None
            table = [[(enc // (n ** (i * n + j))) % n for j in range(n)]
                     for i in range(n)]
            op = lambda a, b, t=table: t[a][b]
            if not _check_eq(lhs_vars, lhs_l, lhs_r, n, op):
                continue
            if _check_eq(rhs_vars, rhs_l, rhs_r, n, op):
                continue
            return n, table
    return None, None


# ───────── Lean code generators ─────────

def make_false_code(n, table):
    table_str = json.dumps(table)
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        "def submission : Goal := by\n"
        f"  let m : Magma (Fin {n}) := {{\n"
        f"    op := finOpTable \"{table_str}\"\n"
        f"  }}\n"
        f"  refine \u27e8Fin {n}, m, ?_\u27e9\n"
        f"  decideFin!\n"
    )


# ───────── Marathon-mode driver ─────────

def _load_manifest(path):
    out = []
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            raw = raw.strip()
            if not raw:
                continue
            try:
                out.append(json.loads(raw))
            except json.JSONDecodeError:
                continue
    return out


def _append_answer(output_path, entry):
    """Append-only write — single JSON line, fsync so nothing is lost on SIGTERM."""
    line = json.dumps(entry, ensure_ascii=False) + "\n"
    with open(output_path, "a", encoding="utf-8") as fh:
        fh.write(line)
        fh.flush()
        try:
            os.fsync(fh.fileno())
        except OSError:
            pass


def run_marathon():
    manifest_path = os.environ["JUDGE_MARATHON_MANIFEST"]
    output_path = os.environ["JUDGE_MARATHON_OUTPUT"]
    budget_seconds = float(os.environ.get("JUDGE_MARATHON_BUDGET_SECONDS", "3600"))
    deadline = time.monotonic() + budget_seconds

    problems = _load_manifest(manifest_path)
    # Trivial triage: keep manifest order, but cap the per-problem search so
    # one stubborn problem can't eat the whole budget. Reserve a tail margin
    # so a SIGTERM near the end still leaves a moment to finish a write.
    tail_margin = 5.0
    per_problem_cap = max(2.0, budget_seconds / max(1, len(problems)))

    for prob in problems:
        if time.monotonic() + tail_margin >= deadline:
            break
        try:
            n, table = search_counterexample(
                prob["equation1"], prob["equation2"],
                max_n=3, time_budget=per_problem_cap,
            )
        except Exception:  # noqa: BLE001 — solver must never crash mid-marathon
            continue
        if n is None:
            continue
        code = make_false_code(n, table)
        _append_answer(output_path, {
            "id": prob["id"],
            "verdict": "false",
            "code": code,
        })


# ───────── Solo fallback (keeps the file dual-mode) ─────────

def _read_message():
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def _send_message(msg):
    print(json.dumps(msg), flush=True)


def run_solo():
    """Minimal Solo path: brute-force counterexample only, no LLM, no proof.

    This baseline isn't intended as a competitive Solo solver; the path
    exists so the dual-mode contract holds. A submission that wants to be
    competitive on Solo should start from one of the LLM-using Solo demos
    under ``examples/solo/demos/`` (e.g. ``twophase`` or ``opnorm``).
    """
    startup = _read_message()
    problem = startup["problem"]
    n, table = search_counterexample(problem["equation1"], problem["equation2"], max_n=3)
    if n is None:
        return
    code = make_false_code(n, table)
    _send_message({"call": "judge", "verdict": "false", "code": code})
    _read_message()


def main():
    if "JUDGE_MARATHON_MANIFEST" in os.environ:
        run_marathon()
    else:
        run_solo()


if __name__ == "__main__":
    main()
