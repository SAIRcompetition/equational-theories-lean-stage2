"""
Marathon few-shot solver — in-run lemma cache + few-shot transfer.

This demo showcases the single most marathon-distinctive strategy: a solver
that builds its own proof library from problems it has already solved
during the same run, then injects the k most-relevant prior wins into the
prompt for each subsequent LLM call. Solo cannot do this — every Solo
problem starts a fresh subprocess with no memory of prior successes.

Strategy:

  Pass A (free, brute force):
    Counterexample search on Fin 2..3 for every problem. ~40-50% of
    'normal' problems get a 'false' certificate here at zero token cost.

  Pass B (LLM with growing few-shot pool):
    Walk the remaining (likely true) problems in difficulty order. For
    each, look up the top-k most structurally similar prior wins from
    the in-memory cache, prepend them as worked examples to the prompt,
    and ask the LLM for a tactic body. Every accepted-shaped 'true'
    answer is appended to the cache so later problems benefit.

Why few-shot helps in marathon (and not Solo):
  * Solo reset → each problem's prompt starts empty.
  * Marathon → the solver carries an evolving library of proofs that
    actually worked on this very run's problem set. Style, naming, and
    common patterns transfer for free.

Cache durability: both in-memory (used for prompt building) and
appended to ``<scratch>/proof_lib.jsonl`` for offline analysis. The
scratch dir is wiped at run start by the runner, so the cache is
fresh per run — no cross-run state.

Known limitation (and a forking opportunity): the few-shot pool is
populated as soon as the solver *submits* an answer, not when the
judge accepts it. Judging happens after the solver exits, so any
proof the LLM hallucinated and submitted could enter the pool and
poison later prompts.

Two mitigations are wired in here:

  * Cheap *syntactic* prefilter on by default (banned placeholders,
    balanced delimiters, non-empty body). It costs ~µs per candidate
    and catches the most common LLM hallucinations. Set
    ``FEWSHOT_VERIFY_BEFORE_CACHE=0`` to disable for A/B comparison.
    It is a prefilter, NOT a real Lean check.
  * Full Lean validation (``lake env lean`` on a per-candidate
    JudgeProblem-equivalent module) is the stricter fork — see the
    ``_prefilter_proof`` docstring for the trade-off and pointer.

Submission behaviour is unchanged: every accepted-shape proof still
goes to the answer file. The flag only gates whether the proof is
allowed to seed the few-shot pool for *later* prompts.

Token discipline:
  * marathon_llm.call_llm self-polices and refuses past-budget calls.
  * Solver pre-checks budget_remaining() before each call; stops
    when projected next-call cost would exceed remaining budget.
"""

PROMPT_BASE = """You are solving an equational-theory implication in Lean 4.

Given two equational laws on a magma G with operation \u25c7:

  Law A ({problem.equation1_id}): {problem.equation1}
  Law B ({problem.equation2_id}): {problem.equation2}

Decide whether every magma satisfying A also satisfies B.

The proof goes inside this template (don't restate it):

    def submission : Goal := by
      intro G _ h
      <YOUR TACTIC BODY HERE>

``h : <Law A>`` is in scope. Use ``exact``, ``rw``, ``simp [h]``, ``intro``,
``apply``, ``have``, ``calc``, etc. No imports. No theorem statements.

If you believe the implication is FALSE, return a 2-D table on Fin n
(2 \u2264 n \u2264 4) instead.

Reply with ONLY one JSON object, no markdown:

    {"verdict": "true",  "proof": "<tactic body>"}
or
    {"verdict": "false", "counterexample_table": [[0,1],[1,0]]}
"""

PROMPT_FEWSHOT_HEADER = """You are solving an equational-theory implication in Lean 4.

Below are {n_examples} proofs that worked on similar problems earlier in
this run. They use the same response format and template you must
follow. Use them as style references — do NOT copy verbatim.

"""

PROMPT_FEWSHOT_EXAMPLE = """### Example {idx}: {ex_eq1_name} \u2192 {ex_eq2_name}
Law A: {ex_eq1}
Law B: {ex_eq2}
Accepted response:
{{"verdict": "true", "proof": {ex_proof_json}}}

"""

PROMPT_FEWSHOT_FOOTER = """### Now solve this:

  Law A ({problem.equation1_id}): {problem.equation1}
  Law B ({problem.equation2_id}): {problem.equation2}

Same template (don't restate it):

    def submission : Goal := by
      intro G _ h
      <YOUR TACTIC BODY HERE>

``h : <Law A>`` is in scope.

Reply with ONLY one JSON object, no markdown:

    {"verdict": "true",  "proof": "<tactic body>"}
or
    {"verdict": "false", "counterexample_table": [[0,1],[1,0]]}
"""

PROMPT = PROMPT_BASE  # Stage 2 fallback prompt (proxy AST-extracts this name).


import json
import os
import re
import sys
import time
from itertools import product
from pathlib import Path


_LIB_DIR = os.environ.get("JUDGE_MARATHON_LIB_DIR")
if _LIB_DIR and _LIB_DIR not in sys.path:
    sys.path.insert(0, _LIB_DIR)


# Number of prior wins to inject as few-shot examples per LLM call.
# Two is enough to demonstrate style transfer without ballooning prompts;
# raising this past ~4 starts to dominate the prompt-token budget.
FEWSHOT_K = 2

# Cap example proof body length so a pathological 80-line proof from an
# earlier problem doesn't crowd out the actual question.
MAX_EXAMPLE_PROOF_CHARS = 800

# Default ON: gate few-shot pool insertion on a cheap structural prefilter.
# The prefilter is ~µs per candidate and rejects the canonical
# pool-poisoners (sorry/admit, unbalanced delimiters, empty bodies);
# leaving it off lets one hallucinated proof contaminate every later
# prompt. Set ``FEWSHOT_VERIFY_BEFORE_CACHE=0`` (or false/no/off) to
# disable for an A/B comparison. See ``_prefilter_proof`` for the
# trade-off and the full-validation fork-target.
FEWSHOT_VERIFY_BEFORE_CACHE = os.environ.get(
    "FEWSHOT_VERIFY_BEFORE_CACHE", "1"
).strip().lower() not in ("0", "false", "no", "off")


# \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 Equation parsing & brute-force counterexample search \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

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


# \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 Lean code generators \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

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


def make_true_code(proof_body):
    proof_body = proof_body.strip()
    if ":= by" in proof_body:
        proof_body = re.sub(r"^.*?:=\s*by\s*\n?", "", proof_body, count=1, flags=re.DOTALL)
    proof_body = re.sub(r"^\s*by\s+", "", proof_body)
    proof_body = re.sub(r"^\s*import\s+.*\n?", "", proof_body, flags=re.MULTILINE)
    lines = proof_body.split("\n")
    indented = "\n".join("  " + ln if ln.strip() else "" for ln in lines)
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{indented}\n"
    )


_BANNED_PROOF_TOKENS = ("sorry", "admit", "unreachable!")
# Lean delimiters we balance-check. ``⟨⟩`` is anonymous-constructor;
# ``‹›`` is the autobound-variable bracket. A proof using only one
# half of any pair almost certainly didn't elaborate cleanly upstream.
_PROOF_DELIMITERS = {
    "(": ")",
    "[": "]",
    "{": "}",
    "\u27e8": "\u27e9",  # ⟨ ⟩
    "\u2039": "\u203a",  # ‹ ›
}

# Token pattern: a banned word surrounded by anything that isn't a
# Lean identifier continuation char. ``(?<![\\w!])`` and ``(?![\\w!])``
# catch ``(sorry)``, ``[sorry]``, ``;sorry;``, ``\n sorry\n``, ``‹sorry›``,
# while still allowing ``sorrySalient`` (a hypothetical identifier
# starting with the banned word) to pass — that boundary uses ``!``
# in the lookahead because Lean tactic ``unreachable!`` ends with ``!``.
_BANNED_PROOF_RE = re.compile(
    r"(?<![A-Za-z0-9_!])("
    + "|".join(re.escape(tok) for tok in _BANNED_PROOF_TOKENS)
    + r")(?![A-Za-z0-9_])"
)

# Lean comment forms. We strip them before placeholder matching so
# ``-- sorry`` or ``/- sorry -/`` aren't treated as banned (they are
# inert as far as elaboration is concerned), but a hostile model
# can't smuggle a real ``sorry`` past us by wrapping it in ``(...)``
# either, since `_BANNED_PROOF_RE` no longer relies on whitespace
# separators.
_LINE_COMMENT_RE = re.compile(r"--[^\n]*")
_BLOCK_COMMENT_RE = re.compile(r"/-[\s\S]*?-/")


def _prefilter_proof(body):
    """Cheap structural check on a candidate proof body.

    Returns ``True`` iff ``body`` looks structurally plausible enough to
    seed the few-shot pool. This is a *prefilter*, not a Lean check —
    a hallucination that survives this gate can still be wrong; this
    only filters the loudest failure modes (placeholders, mismatched
    delimiters, empty bodies).

    Why not full validation: a complete check would write the candidate
    into a per-problem ``JudgeProblem``-equivalent module and run
    ``lake env lean`` against it (the same path ``judge/verify.py`` uses).
    That costs 5-15 s per candidate and would consume a non-trivial slice
    of the marathon wall budget. The cheap prefilter handles the cases
    that a contestant probably wants caught (a hallucinated ``sorry`` is
    the canonical pool-poisoner) without paying the lean-startup tax.
    Forks that want full validation should replace this helper with one
    that spawns ``lake env lean``; see ``judge/verify.py`` for the
    artifact layout.
    """
    if not body:
        return False
    text = body.strip()
    if not text:
        return False
    # Strip Lean comments before placeholder matching. A bare ``-- sorry``
    # is harmless, so admitting it is fine; we just don't want a model
    # that prefixed a real ``sorry`` with whitespace inside a comment to
    # affect the check either way. (Comments don't affect elaboration.)
    decommented = _BLOCK_COMMENT_RE.sub(" ", text)
    decommented = _LINE_COMMENT_RE.sub(" ", decommented)
    # A body that decomments to whitespace is not a real proof — refuse.
    if not decommented.strip():
        return False
    if _BANNED_PROOF_RE.search(decommented):
        return False
    # Delimiter balance on the original text (comments can contain
    # unbalanced delimiters by design — they don't affect elaboration —
    # so we balance-check the decommented form too).
    stack = []
    closers = set(_PROOF_DELIMITERS.values())
    for c in decommented:
        if c in _PROOF_DELIMITERS:
            stack.append(_PROOF_DELIMITERS[c])
        elif c in closers:
            if not stack or stack.pop() != c:
                return False
    return not stack


def _extract_json(text):
    text = re.sub(r"<think>[\s\S]*?</think>", "", text or "").strip()
    text = re.sub(r"^```(?:json)?\s*\n?", "", text)
    text = re.sub(r"\n?```\s*$", "", text)
    try:
        return json.loads(text.strip())
    except Exception:
        pass
    m = re.search(r"\{[\s\S]*\}", text)
    if m:
        try:
            return json.loads(m.group())
        except Exception:
            pass
    return None


# \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 Triage scoring \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

def difficulty_score(prob):
    """Smaller is easier. Combine equation char length + distinct-var count."""
    eq1 = prob.get("equation1", "")
    eq2 = prob.get("equation2", "")
    var_count = len(set(re.findall(r"\b([a-z])\b", eq1 + " " + eq2)))
    return (len(eq1) + len(eq2)) + 5 * var_count


def _vars_of(prob):
    return set(re.findall(r"\b([a-z])\b",
                          prob.get("equation1", "") + " " + prob.get("equation2", "")))


def example_relevance(target, example):
    """Higher = more relevant. Used to rank cached wins for few-shot inclusion."""
    tgt_vars = _vars_of(target)
    ex_vars = _vars_of(example["prob"])
    var_overlap = len(tgt_vars & ex_vars)
    var_diff = abs(len(tgt_vars) - len(ex_vars))
    len_diff = abs(
        len(target.get("equation1", "")) + len(target.get("equation2", ""))
        - len(example["prob"].get("equation1", ""))
        - len(example["prob"].get("equation2", ""))
    )
    # Big positive for shared vars; small penalty for length / arity drift.
    return 10 * var_overlap - 3 * var_diff - len_diff / 50.0


# \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 Few-shot prompt builder \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

def _fill_base(template, prob):
    return (template
            .replace("{problem.equation1}", prob.get("equation1", ""))
            .replace("{problem.equation2}", prob.get("equation2", ""))
            .replace("{problem.equation1_id}", f"Equation{prob['eq1_id']}")
            .replace("{problem.equation2_id}", f"Equation{prob['eq2_id']}"))


def build_prompt(prob, fewshot_pool):
    """Top-k relevance ranking; returns plain prompt if pool is empty."""
    if not fewshot_pool:
        return _fill_base(PROMPT_BASE, prob)
    ranked = sorted(fewshot_pool,
                    key=lambda ex: example_relevance(prob, ex),
                    reverse=True)[:FEWSHOT_K]
    parts = [PROMPT_FEWSHOT_HEADER.replace("{n_examples}", str(len(ranked)))]
    for idx, ex in enumerate(ranked, 1):
        ep = ex["prob"]
        body = ex["proof_body"][:MAX_EXAMPLE_PROOF_CHARS]
        parts.append(PROMPT_FEWSHOT_EXAMPLE
                     .replace("{idx}", str(idx))
                     .replace("{ex_eq1_name}", f"Equation{ep['eq1_id']}")
                     .replace("{ex_eq2_name}", f"Equation{ep['eq2_id']}")
                     .replace("{ex_eq1}", ep.get("equation1", ""))
                     .replace("{ex_eq2}", ep.get("equation2", ""))
                     .replace("{ex_proof_json}", json.dumps(body)))
    parts.append(_fill_base(PROMPT_FEWSHOT_FOOTER, prob))
    return "".join(parts)


# \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 Marathon driver \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

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
    line = json.dumps(entry, ensure_ascii=False) + "\n"
    with open(output_path, "a", encoding="utf-8") as fh:
        fh.write(line)
        fh.flush()
        try:
            os.fsync(fh.fileno())
        except OSError:
            pass


def _persist_pattern(scratch_dir, prob, proof_body):
    """Append win to scratch for offline analysis. Best-effort."""
    try:
        path = Path(scratch_dir) / "proof_lib.jsonl"
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(json.dumps({
                "id": prob["id"],
                "eq1_id": prob.get("eq1_id"),
                "eq2_id": prob.get("eq2_id"),
                "equation1": prob.get("equation1"),
                "equation2": prob.get("equation2"),
                "proof_body": proof_body,
            }) + "\n")
    except OSError:
        pass


def run_marathon():
    try:
        from marathon_llm import call_llm, budget_remaining, tokens_used
    except ImportError:
        call_llm = None  # type: ignore[assignment]

        def budget_remaining():
            return 0

        def tokens_used():
            return 0

    manifest_path = os.environ["JUDGE_MARATHON_MANIFEST"]
    output_path = os.environ["JUDGE_MARATHON_OUTPUT"]
    scratch_dir = os.environ["JUDGE_MARATHON_SCRATCH_DIR"]
    budget_seconds = float(os.environ.get("JUDGE_MARATHON_BUDGET_SECONDS", "3600"))
    cap_tokens = int(os.environ.get("JUDGE_MARATHON_BUDGET_TOKENS", "0"))
    deadline = time.monotonic() + budget_seconds
    tail_margin = 15.0

    # max_output_tokens is intentionally moderate (8192). The helper refuses
    # any call where ``estimated_prompt + max_output_tokens > budget_tokens``,
    # so a marathon at compressed budget cannot afford 32k-output calls
    # everywhere. 8192 fits typical equational proofs comfortably; contestants
    # who run a non-compressed marathon can raise this safely.
    llm_config = {
        "model": os.environ.get("JUDGE_MARATHON_MODEL", "openai/gpt-oss-120b"),
        "provider": "deepinfra/bf16",
        "max_output_tokens": 8192,
        "temperature": 0.0,
        "reasoning_effort": "low",
        "use_seed": True,
        "seed": 0,
        "http_timeout_seconds": 600.0,
    }

    problems = _load_manifest(manifest_path)
    solved: set[str] = set()
    fewshot_pool: list[dict] = []  # In-run cache: [{"prob": {...}, "proof_body": "..."}]

    # \u2500\u2500 Pass A: brute-force counterexample on every problem (no tokens) \u2500\u2500
    for prob in problems:
        if time.monotonic() + tail_margin >= deadline:
            break
        try:
            n, table = search_counterexample(prob["equation1"], prob["equation2"],
                                             max_n=3, time_budget=4.0)
        except Exception:  # noqa: BLE001
            continue
        if n is None:
            continue
        _append_answer(output_path, {
            "id": prob["id"], "verdict": "false",
            "code": make_false_code(n, table),
        })
        solved.add(prob["id"])

    # \u2500\u2500 Pass B: LLM with growing few-shot pool, sorted by difficulty \u2500\u2500
    if call_llm is None:
        return
    remaining = [p for p in problems if p["id"] not in solved]
    remaining.sort(key=difficulty_score)

    for prob in remaining:
        if time.monotonic() + tail_margin >= deadline:
            break
        # Pre-check: refuse to issue a call if remaining budget is too thin
        # for even a minimal response. Helper will refuse anyway, but this
        # avoids a wasted round-trip.
        # cap_tokens semantics (mirrors marathon_llm._budget_cap): >0
        # finite, 0 deny-all, <0 unlimited. Only break on a thin finite
        # remainder; the helper handles the deny-all and unlimited paths.
        if cap_tokens > 0 and budget_remaining() < llm_config["max_output_tokens"] // 4:
            break

        prompt = build_prompt(prob, fewshot_pool)
        try:
            resp = call_llm(prompt, config=llm_config)
        except Exception:  # noqa: BLE001
            continue
        if "error" in resp:
            if "exhausted" in str(resp.get("error", "")):
                break
            continue
        obj = _extract_json(resp.get("response", ""))
        if not isinstance(obj, dict):
            continue
        verdict = obj.get("verdict")
        if verdict == "true":
            body = (obj.get("proof") or "").strip()
            if not body:
                continue
            _append_answer(output_path, {
                "id": prob["id"], "verdict": "true",
                "code": make_true_code(body),
            })
            # Grow the few-shot pool. The very next problem benefits.
            # Submission to disk happened above unconditionally; this
            # gate only governs whether the proof is allowed to seed
            # the pool. A failing prefilter still scores normally — the
            # judge runs after the solver exits, so a wrong proof we
            # admitted will just be marked ``incorrect`` at scoring.
            if FEWSHOT_VERIFY_BEFORE_CACHE and not _prefilter_proof(body):
                continue
            fewshot_pool.append({"prob": prob, "proof_body": body})
            _persist_pattern(scratch_dir, prob, body)
        elif verdict == "false":
            tbl = obj.get("counterexample_table")
            if isinstance(tbl, list) and tbl:
                _append_answer(output_path, {
                    "id": prob["id"], "verdict": "false",
                    "code": make_false_code(len(tbl), tbl),
                })


# \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 Stage-2 fallback (keeps the file dual-mode) \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

def _read_message():
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def _send_message(msg):
    print(json.dumps(msg), flush=True)


def run_stage2():
    """Brute-force-only Stage-2 path; not a competitive contender."""
    startup = _read_message()
    problem = startup["problem"]
    n, table = search_counterexample(problem["equation1"], problem["equation2"], max_n=3)
    if n is None:
        return
    _send_message({"call": "judge", "verdict": "false", "code": make_false_code(n, table)})
    _read_message()


def main():
    if "JUDGE_MARATHON_MANIFEST" in os.environ:
        run_marathon()
    else:
        run_stage2()


if __name__ == "__main__":
    main()
