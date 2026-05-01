"""
baseline — Solo-track reference solver.

Smallest realistic submission: one file, the stdin/stdout JSON
protocol, three escalating stages.

  1. Brute-force counterexample search on small finite magmas — no
     LLM needed; clears most `verdict: false` problems.
  2. Singleton proof pattern (try the trivial 1-element model) — no
     LLM needed; clears the handful of true-but-degenerate cases.
  3. LLM-assisted proof generation — only fires if (1) and (2) miss;
     retries with judge-error feedback in {history.attempts} until
     the wall-clock budget runs out.

Use this as the starting point for your own solver: copy the folder,
rename it, and replace one stage at a time. The `PROMPT` constant
below is the only LLM template — the proxy fills `{problem.*}` and
`{history.*}` placeholders before each call. See `examples/solo/TUTORIAL.md`
Walkthrough 2 for an annotated end-to-end run.
"""

PROMPT = """You are solving equational theory problems in Lean 4.

Does {problem.equation1_id} imply {problem.equation2_id}?
Hypothesis: {problem.equation1}
Goal: {problem.equation2}

If true, provide a proof body (tactics only, no imports or theorem statement).
If false, provide a counterexample table on Fin N.

Previous attempts:
{history.attempts}

Respond with ONLY JSON, no markdown:
{"verdict": "true", "proof": "<tactic body>"}
or
{"verdict": "false", "counterexample_table": [[0,1],[1,0]]}
"""


import json
import re
import sys
from itertools import product


# ── Protocol helpers ──

def read_message():
    """Read one JSON message from stdin."""
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def send_message(msg):
    """Write one JSON message to stdout."""
    print(json.dumps(msg), flush=True)


def call_judge(verdict, code):
    """Send a judge request and return the response."""
    send_message({"call": "judge", "verdict": verdict, "code": code})
    return read_message()


def call_llm(context):
    """Send an LLM request with solver context. Proxy fills the PROMPT template."""
    send_message({"call": "llm", "context": context})
    return read_message()


# ── Equation parsing & brute-force ──

def parse_equation(text):
    variables = []
    seen = set()
    for v in re.findall(r'\b([a-z])\b', text):
        if v not in seen:
            seen.add(v)
            variables.append(v)
    lhs_str, rhs_str = text.split('=', 1)

    def _to_expr(s):
        s = s.strip()
        while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
            depth = 0
            matched = True
            for i, c in enumerate(s):
                if c == '(':
                    depth += 1
                elif c == ')':
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
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            elif c == '\u25c7' and depth == 0:
                last_op = i
        if last_op >= 0:
            left = _to_expr(s[:last_op])
            right = _to_expr(s[last_op+1:])
            return lambda env, l=left, r=right: env['op'](l(env), r(env))
        s = s.strip()
        if len(s) == 1 and s in seen:
            return lambda env, v=s: env[v]
        raise ValueError(f"Cannot parse: {s}")

    return variables, _to_expr(lhs_str), _to_expr(rhs_str)


def search_counterexample(eq1_text, eq2_text, max_n=3):
    """Brute-force search for counterexample on Fin 2..max_n."""
    lhs_vars, lhs_l, lhs_r = parse_equation(eq1_text)
    rhs_vars, rhs_l, rhs_r = parse_equation(eq2_text)

    def check_eq(variables, lhs_fn, rhs_fn, n, op):
        for vals in product(range(n), repeat=len(variables)):
            env = {'op': op}
            for v, val in zip(variables, vals):
                env[v] = val
            if lhs_fn(env) != rhs_fn(env):
                return False
        return True

    for n in range(2, max_n + 1):
        total = n ** (n * n)
        for enc in range(total):
            table = [[(enc // (n ** (i * n + j))) % n for j in range(n)] for i in range(n)]
            op = lambda a, b, t=table: t[a][b]
            lhs_ok = check_eq(lhs_vars, lhs_l, lhs_r, n, op)
            rhs_ok = check_eq(rhs_vars, rhs_l, rhs_r, n, op)
            if lhs_ok and not rhs_ok:
                return n, table
    return None, None


# ── Lean code generation ──

def make_false_code(problem, n, table):
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


def make_true_code(problem, proof_body):
    lines = proof_body.strip().split("\n")
    indented = "\n".join("  " + l if l.strip() else "" for l in lines)
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{indented}\n"
    )


# Prompt is the top-level PROMPT constant above; the proxy fills placeholders.


# ── Extract JSON from LLM response ──

def extract_json(text):
    text = re.sub(r"<think>[\s\S]*?</think>", "", text).strip()
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


# ── Main solver logic ──

def main():
    # Read startup message from proxy
    startup = read_message()
    problem = startup["problem"]

    eq1_text = problem["equation1"]
    eq2_text = problem["equation2"]

    # Stage 1: Brute-force counterexample search
    n, table = search_counterexample(eq1_text, eq2_text, max_n=3)
    if n is not None:
        code = make_false_code(problem, n, table)
        result = call_judge("false", code)
        if result.get("status") == "accepted":
            return  # Done!

    # Stage 2: Singleton proof
    lhs_parts = eq1_text.split("=", 1)
    if len(lhs_parts) == 2 and lhs_parts[0].strip() == "x":
        rhs_of_lhs = set(re.findall(r'\b([a-z])\b', lhs_parts[1]))
        if "x" not in rhs_of_lhs:
            eq1_vars = []
            seen = set()
            for v in re.findall(r'\b([a-z])\b', eq1_text):
                if v not in seen:
                    seen.add(v)
                    eq1_vars.append(v)

            eq2_vars = []
            seen2 = set()
            for v in re.findall(r'\b([a-z])\b', eq2_text):
                if v not in seen2:
                    seen2.add(v)
                    eq2_vars.append(v)

            rhs_lhs, rhs_rhs = eq2_text.split("=", 1)
            filler = " ".join(["a"] * (len(eq1_vars) - 1))
            proof = (
                f"intro {' '.join(eq2_vars)}\n"
                f"have singleton : \u2200 (a b : G), a = b := "
                f"fun a b => (h a {filler}).trans (h b {filler}).symm\n"
                f"exact singleton ({rhs_lhs.strip()}) ({rhs_rhs.strip()})"
            )
            code = make_true_code(problem, proof)
            result = call_judge("true", code)
            if result.get("status") == "accepted":
                return  # Done!

    # Stage 3: LLM loop (solver sends context, proxy fills the PROMPT template).
    # No per-problem call cap — pacing is bounded by the wall-clock timeout.
    rnd = 0
    while True:
        context = {"round": str(rnd)}
        rnd += 1
        llm_result = call_llm(context)

        if "error" in llm_result:
            break  # Budget exceeded or API error

        response_text = llm_result.get("response", "")
        answer = extract_json(response_text)
        if answer is None:
            continue

        verdict = answer.get("verdict")
        if verdict not in ("true", "false"):
            continue

        if verdict == "true":
            proof_body = answer.get("proof", "")
            if not proof_body:
                continue
            # Clean proof
            if ":= by" in proof_body:
                proof_body = re.sub(r"^.*?:=\s*by\s*\n?", "", proof_body, count=1, flags=re.DOTALL)
            proof_body = re.sub(r"^\s*by\s+", "", proof_body)
            proof_body = re.sub(r"^\s*import\s+.*\n?", "", proof_body, flags=re.MULTILINE)
            proof_body = proof_body.strip()
            code = make_true_code(problem, proof_body)
        else:
            tbl = answer.get("counterexample_table")
            if not tbl or not isinstance(tbl, list):
                continue
            code = make_false_code(problem, len(tbl), tbl)

        result = call_judge(verdict, code)
        if result.get("status") == "accepted":
            return  # Done!
        # Judge error now automatically appears in {history.*} for next round


if __name__ == "__main__":
    main()
