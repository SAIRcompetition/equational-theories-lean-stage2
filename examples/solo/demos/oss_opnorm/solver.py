"""
oss_opnorm — flagship reference mining solver (Solo track).

Strategy: 16 deterministic proof strategies (counterexample search on
Fin 2-7, singleton detection, library lookup, constancy lemmas, BFS
near-miss search, several calc-chain variants) followed by a single
structural-context LLM call. The LLM receives constancy / near-miss
analysis from the deterministic stages, so it usually only needs one
attempt when called.

Also distils Lean errors into structured feedback (error type,
expected vs actual types, specific fix hints) for the next LLM round
when the first attempt is rejected, instead of dumping raw stderr.

Reference snapshot dated 2026-04-23. See `examples/solo/TUTORIAL.md`
Walkthrough 3 for an annotated end-to-end run.
"""

PROMPT = """You are a Lean 4 proof engineer. Output ONLY valid JSON with a calc chain proof.

## Problem

h ({problem.equation1_id}): ∀ vars, {solver.h_text}
Goal ({problem.equation2_id}): ∀ vars, {solver.goal_text}

{solver.analysis}
{solver.bfs_hints}
{solver.verdict_hint}

## Equation analysis

{solver.equation_analysis}

## RULES

1. Output ONLY valid JSON: {{"verdict":"true","proof":"intro ...\\ncalc ..."}}
2. "proof" field = tactic body only. NO `theorem submission`.
3. NEVER use `_` as a type in `have`. Always write the full type.
4. NEVER use: sorry, admit, aesop, omega, decide, tauto, linarith, simp (any form)
5. Use ONLY: intro, exact, calc, have, congr_arg, .symm, .trans
6. MAGMA OPERATOR IS `◇` (U+25C7), NOT `*`. Write every operator as `◇`. If you see `*` anywhere in the problem statement, treat it as `◇` — the equations are equivalent, it is only a display convention. Proofs containing `*` will FAIL to compile with `failed to synthesize HMul`.

## The MATCH-COLLAPSE proof method

Almost all these proofs follow a 2-step pattern:

### Step 1: MATCH — use h with compound args to match goal's outer structure

h: {problem.equation1}

To match the goal, substitute COMPOUND terms into h's non-free variables so the resulting equation's structure aligns with the goal.

Example: If goal has `(x ◇ y) ◇ something` on RHS, and h's RHS has `y_var ◇ something`, set `y_var = (x ◇ y)`.

### Step 2: COLLAPSE — use constancy to simplify inner junk

After Step 1, h produces `goal_outer ◇ (junk)`. You need `junk = goal_inner`.

Use the constancy lemma: since free variables can take any value, `h(x, free1, free2)` = `h(x, free1', free2')`, which means you can freely adjust the junk.

Specifically: `(h a b c).symm.trans (h a d e)` proves the junk with args (b,c) equals the junk with args (d,e).

Use `congr_arg (outer ◇ ·) <proof>` to apply this inside the outer structure.

{solver.match_collapse_hints}

## Key h instantiations

{solver.h_instantiations}

## Worked example

h: x ◇ x = y ◇ ((y ◇ x) ◇ z)  (z free on RHS only)
Goal: x ◇ x = (x ◇ y) ◇ (z ◇ z)

Step 1 (MATCH): Goal RHS starts with `(x ◇ y) ◇ ...`. h RHS is `y ◇ ((y ◇ x) ◇ z)`. Set y := (x ◇ y):
  h x (x ◇ y) free_z gives: x ◇ x = (x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ free_z)

Step 2 (COLLAPSE): Need `(((x ◇ y) ◇ x) ◇ free_z) = z ◇ z`. Use h with x := z:
  h z a z gives: z ◇ z = a ◇ ((a ◇ z) ◇ z)
  Set a := (x ◇ y) ◇ x: z ◇ z = ((x◇y)◇x) ◇ ((((x◇y)◇x) ◇ z) ◇ z)
  .symm: ((x◇y)◇x) ◇ ((((x◇y)◇x) ◇ z) ◇ z) = z ◇ z

So set free_z := (((x◇y)◇x) ◇ z) ◇ z in Step 1.

```lean
intro x y z
calc
  x ◇ x = (x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ ((((x ◇ y) ◇ x) ◇ z) ◇ z)) := h x (x ◇ y) ((((x ◇ y) ◇ x) ◇ z) ◇ z)
  _ = (x ◇ y) ◇ (z ◇ z) := congr_arg ((x ◇ y) ◇ ·) (h z ((x ◇ y) ◇ x) z).symm
```

## Previous attempts

{history.attempts}

## Your response (JSON only):
"""


import json
import random
import re
import sys
from itertools import product, combinations


# ── Operator normalisation ──────────────────────────────────────
# HF problem text uses `*`; Lean Magma uses `◇`. The LLM reliably imitates
# whatever the prompt shows, so normalise equation text into the prompt and
# re-normalise the LLM's proof before it reaches Lean.
def normalize_op_to_diamond(text):
    if not isinstance(text, str):
        return text
    return text.replace('*', '◇')


# ── Protocol ─────────────────────────────────────────────────────

def read_message():
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def send_message(msg):
    print(json.dumps(msg), flush=True)


def call_judge(verdict, code):
    send_message({"call": "judge", "verdict": verdict, "code": code})
    return read_message()


def call_llm(context, overrides=None):
    msg = {"call": "llm", "context": context}
    if overrides:
        msg["overrides"] = overrides
    send_message(msg)
    return read_message()


# ── Equation parsing ─────────────────────────────────────────────

def parse_variables(text):
    seen = set()
    variables = []
    for v in re.findall(r'\b([a-z])\b', text):
        if v not in seen:
            seen.add(v)
            variables.append(v)
    return variables


def parse_equation(text):
    variables = parse_variables(text)
    var_set = set(variables)
    lhs_str, rhs_str = text.split('=', 1)

    def _to_expr(s):
        s = s.strip()
        while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
            depth = 0; matched = True
            for i, c in enumerate(s):
                if c == '(': depth += 1
                elif c == ')': depth -= 1
                if depth == 0 and i < len(s) - 1: matched = False; break
            if matched: s = s[1:-1].strip()
            else: break
        depth = 0; last_op = -1
        for i, c in enumerate(s):
            if c == '(': depth += 1
            elif c == ')': depth -= 1
            elif (c == '\u25c7' or c == '*') and depth == 0: last_op = i
        if last_op >= 0:
            left = _to_expr(s[:last_op])
            right = _to_expr(s[last_op + 1:])
            return lambda env, l=left, r=right: env['op'](l(env), r(env))
        s = s.strip()
        if len(s) == 1 and s in var_set:
            return lambda env, v=s: env[v]
        raise ValueError(f"Cannot parse: {s}")

    return variables, _to_expr(lhs_str), _to_expr(rhs_str)


def check_equation(variables, lhs_fn, rhs_fn, n, op):
    for vals in product(range(n), repeat=len(variables)):
        env = {'op': op}
        for v, val in zip(variables, vals):
            env[v] = val
        if lhs_fn(env) != rhs_fn(env):
            return False
    return True


# ── Counterexample search ────────────────────────────────────────

def _structured_tables(n):
    for c in range(n):
        yield [[c] * n for _ in range(n)]
    yield [[i] * n for i in range(n)]
    yield [list(range(n)) for _ in range(n)]
    yield [[(i + j) % n for j in range(n)] for i in range(n)]
    yield [[(i - j) % n for j in range(n)] for i in range(n)]
    yield [[max(i, j) for j in range(n)] for i in range(n)]
    yield [[min(i, j) for j in range(n)] for i in range(n)]
    yield [[i if i != 0 else j for j in range(n)] for i in range(n)]
    yield [[j if j != 0 else i for j in range(n)] for i in range(n)]
    for k in range(1, n):
        yield [[(i + k) % n] * n for i in range(n)]
        yield [[(j + k) % n for j in range(n)] for _ in range(n)]
    if n > 1:
        yield [[(i * j) % n for j in range(n)] for i in range(n)]
    if n in (2, 4):
        yield [[(i ^ j) % n for j in range(n)] for i in range(n)]
    for c in range(n):
        for thresh in range(1, n):
            yield [[i if i < thresh else c for _ in range(n)] for i in range(n)]
            yield [[j if j < thresh else c for j in range(n)] for _ in range(n)]
    yield [[i if i >= j else j for j in range(n)] for i in range(n)]
    yield [[i if i <= j else j for j in range(n)] for i in range(n)]
    # Left-zero and right-zero semigroups
    yield [[i for _ in range(n)] for i in range(n)]  # left projection
    yield [[j for j in range(n)] for _ in range(n)]  # right projection
    # Nilpotent-like: a◇b = 0 except identity
    if n >= 2:
        yield [[0 if i != j else i for j in range(n)] for i in range(n)]
        yield [[(i + j + 1) % n for j in range(n)] for i in range(n)]
    # Band-like: a◇a = a, a◇b = first/second
    if n >= 3:
        yield [[i if i == j else (i + j) % n for j in range(n)] for i in range(n)]
        yield [[i if i == j else 0 for j in range(n)] for i in range(n)]
        yield [[i if i == j else n - 1 for j in range(n)] for i in range(n)]
    # Permutation tables (right-multiply by various permutations)
    if n <= 4:
        import itertools as _it
        for perm in _it.permutations(range(n)):
            yield [[perm[j] for j in range(n)] for _ in range(n)]
            yield [[perm[i] for _ in range(n)] for i in range(n)]
    # Rectangular band: a◇b = (a_left, b_right) decompositions
    if n >= 4:
        for d in range(2, n):
            if n % d == 0:
                m = n // d
                yield [[(i // m) * m + (j % m) for j in range(n)] for i in range(n)]
                yield [[(i % d) + (j // d) * d for j in range(n)] for i in range(n)]
    # Semilattice variants
    yield [[max(i, j) for j in range(n)] for i in range(n)]
    yield [[min(i, j) for j in range(n)] for i in range(n)]
    # Selective: a◇b ∈ {a, b}
    if n <= 5:
        for chooser in range(2 ** (n * n)):
            table = [[0] * n for _ in range(n)]
            valid = True
            for i in range(n):
                for j in range(n):
                    bit = (chooser >> (i * n + j)) & 1
                    table[i][j] = i if bit else j
                    if i == j and table[i][j] != i:
                        valid = False
                        break
                if not valid:
                    break
            if valid:
                yield table
            if chooser > 1024:  # Cap to avoid explosion
                break
    # Constant rows/columns with identity on diagonal
    for c in range(n):
        t = [[c] * n for _ in range(n)]
        for i in range(n):
            t[i][i] = i
        yield t
    # "Flip" tables: a◇b = (n-1-a), a◇b = (n-1-b), etc
    if n >= 2:
        yield [[(n - 1 - i) for _ in range(n)] for i in range(n)]
        yield [[(n - 1 - j) for j in range(n)] for _ in range(n)]
        yield [[(n - 1 - i + j) % n for j in range(n)] for i in range(n)]
        yield [[(i + n - 1 - j) % n for j in range(n)] for i in range(n)]
    # Polynomial tables: (a*x + b*y) mod n for various a, b
    for a in range(n):
        for b in range(n):
            if a == 0 and b == 0:
                continue  # constant zero, already covered
            if a == 1 and b == 1:
                continue  # x+y mod n, already covered
            yield [[(a * i + b * j) % n for j in range(n)] for i in range(n)]
    # Polynomial tables: (a*x + b*y + c) mod n
    for a in range(1, min(n, 4)):
        for b in range(1, min(n, 4)):
            for c in range(1, min(n, 3)):
                yield [[(a * i + b * j + c) % n for j in range(n)] for i in range(n)]


def verify_table(eq_text, n, table):
    """Check if a table satisfies an equation. Returns True if it does."""
    variables, lhs_fn, rhs_fn = parse_equation(eq_text)
    op = lambda a, b, t=table: t[a][b]
    return check_equation(variables, lhs_fn, rhs_fn, n, op)


def verify_counterexample(eq1_text, eq2_text, n, table):
    """Check if table satisfies eq1 AND violates eq2. Returns (sat_eq1, sat_eq2)."""
    sat1 = verify_table(eq1_text, n, table)
    sat2 = verify_table(eq2_text, n, table)
    return sat1, sat2


def exhaustive_counterexample(eq1_text, eq2_text, max_n=3):
    v1, l1, r1 = parse_equation(eq1_text)
    v2, l2, r2 = parse_equation(eq2_text)
    for n in range(2, max_n + 1):
        for enc in range(n ** (n * n)):
            table = [[(enc // (n ** (i * n + j))) % n for j in range(n)] for i in range(n)]
            op = lambda a, b, t=table: t[a][b]
            if check_equation(v1, l1, r1, n, op) and not check_equation(v2, l2, r2, n, op):
                return n, table
    return None, None


def _product_tables(n):
    """Generate tables from direct products Z_p × Z_q for n = p*q."""
    # For each factorization of n
    for p in range(2, n):
        if n % p != 0:
            continue
        q = n // p
        # Element (a,b) maps to a*q + b. Try various ops on the product.
        for a1 in range(p):
            for b1 in range(q):
                for a2 in range(p):
                    for b2 in range(q):
                        # op((r,s),(t,u)) = (a1*r+a2*t mod p, b1*s+b2*u mod q)
                        if a1 == 0 and a2 == 0 and b1 == 0 and b2 == 0:
                            continue
                        table = [[0]*n for _ in range(n)]
                        for i in range(n):
                            for j in range(n):
                                r, s = i // q, i % q
                                t, u = j // q, j % q
                                res_a = (a1 * r + a2 * t) % p
                                res_b = (b1 * s + b2 * u) % q
                                table[i][j] = res_a * q + res_b
                        yield table


def extended_counterexample(eq1_text, eq2_text, max_n=7, random_attempts=10000):
    v1, l1, r1 = parse_equation(eq1_text)
    v2, l2, r2 = parse_equation(eq2_text)
    for sz in range(2, min(max_n + 1, 8)):
        for table in _structured_tables(sz):
            op = lambda a, b, t=table: t[a][b]
            if check_equation(v1, l1, r1, sz, op) and not check_equation(v2, l2, r2, sz, op):
                return sz, table
    # Also try product tables on Fin 4-9
    for sz in range(4, 10):
        for table in _product_tables(sz):
            op = lambda a, b, t=table: t[a][b]
            if check_equation(v1, l1, r1, sz, op) and not check_equation(v2, l2, r2, sz, op):
                return sz, table
    for sz in (4, 5, 6, 7):
        for _ in range(random_attempts):
            table = [[random.randint(0, sz - 1) for _ in range(sz)] for _ in range(sz)]
            op = lambda a, b, t=table: t[a][b]
            if check_equation(v1, l1, r1, sz, op) and not check_equation(v2, l2, r2, sz, op):
                return sz, table
    return None, None


_KNOWN_CE_CACHE = None

def known_counterexample(eq1_id, eq2_id):
    """Look up a known counterexample table from the equational_theories database.
    Returns (n, table) or (None, None)."""
    global _KNOWN_CE_CACHE
    if _KNOWN_CE_CACHE is None:
        import os
        db_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'known_counterexamples.json')
        if os.path.exists(db_path):
            with open(db_path) as f:
                _KNOWN_CE_CACHE = json.load(f)
        else:
            _KNOWN_CE_CACHE = {}
    # Support both int IDs (new HF format) and string names (legacy cache keys)
    eq1_name = f"Equation{eq1_id}" if isinstance(eq1_id, int) else eq1_id
    eq2_name = f"Equation{eq2_id}" if isinstance(eq2_id, int) else eq2_id
    key = f"{eq1_name}->{eq2_name}"
    entry = _KNOWN_CE_CACHE.get(key)
    if entry:
        return entry['n'], entry['table']
    return None, None


def backtrack_counterexample(eq1_text, eq2_text, sizes=(4, 5), time_limit=10):
    """Backtracking search with constraint propagation for counterexample tables.
    Much more effective than random search for equations with few valid tables.
    Returns (n, table) or (None, None)."""
    v1, l1, r1 = parse_equation(eq1_text)
    v2, l2, r2 = parse_equation(eq2_text)

    import time as _time
    t_start = _time.time()

    for n in sizes:
        if _time.time() - t_start > time_limit:
            break
        cells = [(i, j) for i in range(n) for j in range(n)]
        nc = n * n
        table = [[None] * n for _ in range(n)]
        values = [0] * nc
        cell_idx = 0

        while 0 <= cell_idx < nc:
            if _time.time() - t_start > time_limit:
                break

            i, j = cells[cell_idx]
            val = values[cell_idx]

            if val >= n:
                table[i][j] = None
                values[cell_idx] = 0
                cell_idx -= 1
                if cell_idx >= 0:
                    ci, cj = cells[cell_idx]
                    table[ci][cj] = None
                    values[cell_idx] += 1
                continue

            table[i][j] = val

            # Check eq1 partial constraint
            op = lambda a, b, t=table: t[a][b] if t[a][b] is not None else None
            eq1_ok = True
            for vals_iter in product(range(n), repeat=len(v1)):
                env = {'op': op}
                for v, vl in zip(v1, vals_iter):
                    env[v] = vl
                try:
                    lv = l1(env)
                    rv = r1(env)
                except TypeError:
                    continue
                if lv is not None and rv is not None and lv != rv:
                    eq1_ok = False
                    break

            if eq1_ok:
                if cell_idx == nc - 1:
                    # Complete table — check eq2 violated
                    eq2_ok = check_equation(v2, l2, r2, n, lambda a, b, t=table: t[a][b])
                    if not eq2_ok:
                        return n, [row[:] for row in table]
                    values[cell_idx] += 1
                    table[i][j] = None
                else:
                    cell_idx += 1
            else:
                table[i][j] = None
                values[cell_idx] += 1

    return None, None


# ── Singleton collapse ───────────────────────────────────────────

def try_singleton(problem, eq1_text, eq2_text):
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    if len(eq1_vars) < 2:
        return False
    parts = eq1_text.split("=", 1)
    if len(parts) != 2: return False
    lhs_var = parts[0].strip()
    rhs_expr = parts[1].strip()
    if len(lhs_var) != 1 or lhs_var not in eq1_vars: return False
    goal_parts = eq2_text.split("=", 1)
    if len(goal_parts) != 2: return False
    if lhs_var in set(re.findall(r'\b([a-z])\b', rhs_expr)):
        return False
    filler = " ".join(["a"] * (len(eq1_vars) - 1))
    proof = (
        f"intro {' '.join(eq2_vars)}\n"
        f"have singleton : \u2200 (a b : G), a = b := "
        f"fun a b => (h a {filler}).trans (h b {filler}).symm\n"
        f"exact singleton ({goal_parts[0].strip()}) ({goal_parts[1].strip()})"
    )
    code = make_true_code(problem, proof)
    result = call_judge("true", code)
    return result.get("status") == "accepted"


# ── Lean code generation ─────────────────────────────────────────

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
    # Normalize: strip common leading whitespace, then re-indent with 2 spaces
    non_empty = [l for l in lines if l.strip()]
    if non_empty:
        min_indent = min(len(l) - len(l.lstrip()) for l in non_empty)
        lines = [l[min_indent:] if len(l) > min_indent else l for l in lines]
    indented = "\n".join("  " + l if l.strip() else "" for l in lines)
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{indented}\n"
    )


# ── JSON extraction ──────────────────────────────────────────────

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


def clean_proof(proof_body):
    # If the proof starts with a full theorem header like "theorem ... := by\n...",
    # strip everything up to and including ":= by". But ONLY match the theorem
    # header pattern at the start, NOT ":= by" that appears inside calc chains.
    m = re.match(r'^(?:\s*theorem\s+.*?:=\s*by\s*\n)', proof_body, flags=re.DOTALL)
    if m:
        proof_body = proof_body[m.end():]
    # Strip leading "by" keyword (may appear if LLM includes it)
    proof_body = re.sub(r"^\s*by\s*\n", "", proof_body)
    proof_body = re.sub(r"^\s*by\s+", "", proof_body)
    proof_body = re.sub(r"^\s*import\s+.*\n?", "", proof_body, flags=re.MULTILINE)
    proof_body = re.sub(r"^\s*theorem\s+.*\n?", "", proof_body, flags=re.MULTILINE)
    # Normalize indentation: find minimum indent and strip it from all lines
    # Use split BEFORE strip to preserve relative indentation
    lines = proof_body.split('\n')
    # Remove leading/trailing empty lines
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    if lines:
        min_indent = float('inf')
        for line in lines:
            if line.strip():
                indent = len(line) - len(line.lstrip())
                min_indent = min(min_indent, indent)
        if min_indent > 0 and min_indent < float('inf'):
            lines = [line[min_indent:] if len(line) >= min_indent else line for line in lines]
    return '\n'.join(lines).strip()


def extract_calc_intermediates(proof_body):
    """Extract intermediate expressions from a calc chain in a proof.
    Returns a list of expression strings found between calc steps."""
    intermediates = []
    # Match explicit calc intermediate: _ = <expr> :=
    for m in re.finditer(r'_\s*=\s*(.+?)\s*:=', proof_body):
        expr = m.group(1).strip()
        # Skip if it's just _ (wildcard)
        if expr == '_':
            continue
        # Normalize: remove outer parens, clean whitespace
        expr = expr.strip('()')
        if expr and '◇' in expr:
            intermediates.append(expr)
    # Also match have lemma conclusions: have foo : expr1 = expr2
    for m in re.finditer(r'have\s+\w+\s*:\s*(?:∀[^,]+,\s*)?(.+?)\s*:=', proof_body):
        type_expr = m.group(1).strip()
        if '=' in type_expr and '◇' in type_expr:
            parts = type_expr.split('=', 1)
            for p in parts:
                p = p.strip().strip('()')
                if p and '◇' in p:
                    intermediates.append(p)
    return list(set(intermediates))


def try_symm_repair(proof_body, error_msg):
    """Try to fix a proof by flipping .symm on expressions that have wrong direction.
    Returns the repaired proof or None if no repair was attempted."""
    # Look for pattern: "has type X = Y but expected Y = X"
    # This means we need to flip .symm
    import re as _re

    # Find the line/expression causing the error
    # Try to find which specific h application has wrong direction
    # Strategy: toggle .symm on h applications one at a time
    lines = proof_body.split('\n')
    candidates = []

    for i, line in enumerate(lines):
        # Find all h applications in this line
        # Pattern: (h <args>).symm or h <args> (without .symm)
        # Try toggling .symm
        if '.symm' in line:
            # Try removing .symm
            new_line = line.replace('.symm', '', 1)
            new_proof = '\n'.join(lines[:i] + [new_line] + lines[i+1:])
            if new_proof != proof_body:
                candidates.append(new_proof)
        # Look for `h ` that could get .symm added
        # Match patterns like `exact h ...` or `:= h ...` or `by exact h ...`
        for m in _re.finditer(r'(\bh\s+[\w\s◇()]+?)(\)|\s*$)', line):
            # Try adding .symm after the h application
            start, end = m.span(1)
            new_line = line[:start] + '(' + m.group(1) + ').symm' + line[end:]
            new_proof = '\n'.join(lines[:i] + [new_line] + lines[i+1:])
            if new_proof != proof_body:
                candidates.append(new_proof)

    # Return the first candidate (simple heuristic — just try one repair)
    return candidates[0] if candidates else None


def preflight_proof(proof_body):
    """Pre-flight validation of LLM proof before sending to judge.
    Returns (cleaned_proof, error_info_or_None).
    If error_info is not None, the proof has a fixable/rejectable issue."""
    issues = []

    # 1. Check for sorry/admit ANYWHERE in the proof (these are always banned)
    if re.search(r'\bsorry\b', proof_body):
        return None, {
            "type": "preflight_banned",
            "detail": "Proof contains `sorry` which is BANNED. Provide a complete proof.",
        }
    if re.search(r'\badmit\b', proof_body):
        return None, {
            "type": "preflight_banned",
            "detail": "Proof contains `admit` which is BANNED. Provide a complete proof.",
        }

    # 2. Check for placeholder type in have: `∀ ... _ := by`
    if re.search(r'∀\s*\([^)]*\)\s*,\s*_\s*:=', proof_body):
        return None, {
            "type": "preflight_placeholder_type",
            "detail": "have statement uses `_ :=` (underscore type). Lean cannot synthesize the type. "
                      "You MUST write the explicit type, e.g., `have lem : ∀ (x y : G), expr1 = expr2 := ...`",
        }

    # 3. Check for nonexistent library references
    lib_ref = re.search(r'Equation\d+_implies_Equation\d+', proof_body)
    if lib_ref:
        return None, {
            "type": "preflight_nonexistent_lib",
            "detail": f"`{lib_ref.group()}` does not exist. You must write the proof yourself from scratch using `h`.",
        }

    # 4. Check for banned automation tactics (at tactic position: start of line)
    # Note: 'simp only [...]' is ALLOWED — only bare 'simp' without 'only' is banned
    BANNED_AUTO = [
        'aesop', 'omega', 'norm_num', 'ring', 'field_simp',
        'decide', 'tauto', 'linarith', 'positivity', 'polyrith', 'nlinarith',
    ]
    found_banned = []
    fixed = proof_body
    # Check for bare simp (without 'only') separately
    bare_simp_pat = re.compile(r'^\s*simp\b(?!\s+only\b).*$', re.MULTILINE)
    if bare_simp_pat.search(fixed):
        found_banned.append('simp (use simp only [...] instead)')
        fixed = bare_simp_pat.sub('', fixed)
    for tac in BANNED_AUTO:
        pat = re.compile(r'^\s*' + re.escape(tac) + r'\b.*$', re.MULTILINE)
        if pat.search(fixed):
            found_banned.append(tac)
            fixed = pat.sub('', fixed)

    if found_banned:
        # Check if removing them leaves a useful proof
        remaining = '\n'.join(l for l in fixed.split('\n') if l.strip())
        if not remaining.strip():
            return None, {
                "type": "preflight_banned",
                "detail": f"Proof relies entirely on banned tactic(s): {', '.join(found_banned)}. "
                          "Rewrite using ONLY: intro, exact, have, calc, rw, conv, congr_arg, apply, constructor.",
            }
        return None, {
            "type": "preflight_banned",
            "detail": f"Proof uses banned tactic(s): {', '.join(found_banned)}. "
                      "Replace these lines with explicit proof steps using exact, have, calc, congr_arg.",
        }

    # 5. Check for `congr_arg` used as tactic (should be a term)
    if re.search(r'^\s*congr_arg\s', fixed, re.MULTILINE):
        fixed = re.sub(r'^(\s*)congr_arg\s', r'\1exact congr_arg ', fixed, flags=re.MULTILINE)
        issues.append("congr_arg_as_tactic")

    if issues:
        return fixed, None

    return proof_body, None


# ── Error analysis ───────────────────────────────────────────────

def parse_lean_error(stderr_text):
    """Extract structured error info from Lean stderr."""
    if not stderr_text:
        return {"type": "unknown", "detail": ""}

    lines = stderr_text.strip().split('\n')
    error_type = "unknown"
    detail = ""
    expected = ""
    got = ""

    # Check for decideFin!/decide failure — means the table doesn't satisfy the equation
    if "application type mismatch" in stderr_text and "of_decide_eq_true" in stderr_text:
        # Extract which equation failed
        eq_match = re.search(r'decide \((\w+) \(Fin (\d+)\)\)', stderr_text)
        if eq_match:
            eq_name = eq_match.group(1)
            fin_size = eq_match.group(2)
            return {
                "type": "table_wrong",
                "detail": f"Table on Fin {fin_size} does not satisfy {eq_name}",
                "equation": eq_name,
                "fin_size": fin_size,
                "expected": "",
                "got": "",
                "raw": stderr_text[:400] if len(stderr_text) > 400 else stderr_text,
            }

    for i, line in enumerate(lines):
        if "type mismatch" in line:
            error_type = "type_mismatch"
            for j in range(i, min(i + 6, len(lines))):
                if "has type" in lines[j] and "expected" not in lines[j]:
                    got = lines[j].split("has type")[-1].strip()
                    if not got and j + 1 < len(lines):
                        got = lines[j + 1].strip()
                if "expected to have type" in lines[j]:
                    expected = lines[j+1].strip() if j+1 < len(lines) else ""
        elif "unknown identifier" in line:
            error_type = "unknown_identifier"
            m = re.search(r"unknown identifier '([^']*)'", line)
            detail = m.group(1) if m else line
        elif "unknown tactic" in line:
            error_type = "unknown_tactic"
            m = re.search(r"unknown tactic '([^']*)'", line)
            detail = m.group(1) if m else line
        elif "unsolved goals" in line:
            error_type = "unsolved_goals"
            if i + 1 < len(lines):
                detail = lines[i+1].strip()
        elif "application type mismatch" in line:
            error_type = "app_type_mismatch"
            detail = line
        elif "function expected" in line:
            error_type = "function_expected"
            detail = line

    return {
        "type": error_type,
        "detail": detail,
        "expected": expected,
        "got": got,
        "raw": stderr_text[:400] if len(stderr_text) > 400 else stderr_text,
    }


# ── Equation analysis ────────────────────────────────────────────

def symbolic_specialize(eq_text, eq_vars):
    """Generate useful specializations of the hypothesis equation."""
    if len(eq_vars) < 2:
        return []

    specs = []
    parts = eq_text.split('=', 1)
    if len(parts) != 2:
        return []

    lhs = parts[0].strip()
    rhs = parts[1].strip()

    # All same variable
    unified = rhs
    for v in eq_vars:
        unified = re.sub(r'\b' + v + r'\b', 'x', unified)
    specs.append(f"h({', '.join(['x']*len(eq_vars))}): {lhs.replace(eq_vars[0], 'x')} = {unified}")

    # Set pairs equal
    if len(eq_vars) >= 2:
        for i in range(len(eq_vars)):
            for j in range(i+1, len(eq_vars)):
                result = rhs
                result = re.sub(r'\b' + eq_vars[j] + r'\b', eq_vars[i], result)
                sub = [eq_vars[k] if k != j else eq_vars[i] for k in range(len(eq_vars))]
                specs.append(f"h({', '.join(sub)}): {lhs} = {result}")

    # Set one var to be a term
    if len(eq_vars) >= 3:
        # Set first free var to LHS var
        target = eq_vars[0]
        for i in range(1, len(eq_vars)):
            result = rhs
            result = re.sub(r'\b' + eq_vars[i] + r'\b', target, result)
            sub = [eq_vars[k] if k != i else target for k in range(len(eq_vars))]
            specs.append(f"h({', '.join(sub)}): {lhs} = {result}")

    return specs[:8]  # Cap at 8


# ── Tree utilities for proof search ──────────────────────────────

def parse_op_tree(s):
    """Parse a magma expression string into a tree: ('op', left, right) or ('var', name)."""
    s = s.strip()
    while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
        d = 0; matched = True
        for i, c in enumerate(s):
            if c == '(': d += 1
            elif c == ')': d -= 1
            if d == 0 and i < len(s) - 1: matched = False; break
        if matched: s = s[1:-1].strip()
        else: break
    d = 0; last_op = -1
    for i, c in enumerate(s):
        if c == '(': d += 1
        elif c == ')': d -= 1
        elif (c == '\u25c7' or c == '*') and d == 0: last_op = i
    if last_op >= 0:
        return ('op', parse_op_tree(s[:last_op]), parse_op_tree(s[last_op+1:]))
    return ('var', s.strip())


def tree_to_str(t):
    """Convert a tree back to a string."""
    if t[0] == 'var': return t[1]
    return f"({tree_to_str(t[1])} \u25c7 {tree_to_str(t[2])})"


def unify_tree(template, target, tvars, subst=None):
    """Unify template tree with target tree, binding tvars. Returns subst dict or None."""
    if subst is None:
        subst = {}
    if template[0] == 'var' and template[1] in tvars:
        v = template[1]
        tgt_str = tree_to_str(target)
        if v in subst:
            return subst if subst[v] == tgt_str else None
        subst[v] = tgt_str
        return subst
    if template[0] == 'var' and target[0] == 'var':
        return subst if template[1] == target[1] else None
    if template[0] == 'op' and target[0] == 'op':
        s = unify_tree(template[1], target[1], tvars, subst)
        if s is None:
            return None
        return unify_tree(template[2], target[2], tvars, s)
    return None


def get_subtree(tree, path):
    """Get subtree at path (string of 'L'/'R')."""
    if not path:
        return tree
    if tree[0] != 'op':
        return tree
    return get_subtree(tree[1] if path[0] == 'L' else tree[2], path[1:])


def apply_rewrite_at(tree, path, new_subtree):
    """Replace subtree at path with new_subtree."""
    if not path:
        return new_subtree
    d = path[0]
    rest = path[1:]
    if tree[0] != 'op':
        return tree
    if d == 'L':
        return ('op', apply_rewrite_at(tree[1], rest, new_subtree), tree[2])
    else:
        return ('op', tree[1], apply_rewrite_at(tree[2], rest, new_subtree))


def wrap_congr_arg(tree, path, inner_proof):
    """Wrap inner_proof with congr_arg chains for the given path."""
    if not path:
        return inner_proof
    d = path[0]
    rest = path[1:]
    if tree[0] != 'op':
        return inner_proof
    if d == 'L':
        sub = wrap_congr_arg(tree[1], rest, inner_proof)
        shared = tree_to_str(tree[2])
        return f"congr_arg (\u00b7 \u25c7 {shared}) ({sub})"
    else:
        sub = wrap_congr_arg(tree[2], rest, inner_proof)
        shared = tree_to_str(tree[1])
        return f"congr_arg ({shared} \u25c7 \u00b7) ({sub})"


def try_constancy_at(subtree_a, subtree_b, ci, default_fill):
    """Try to prove subtree_a = subtree_b using constancy info ci.
    Returns the Lean args string for hconst, or None."""
    lhs_tree = parse_op_tree(ci['lhs_template'])
    rhs_tree = parse_op_tree(ci['rhs_template'])
    tvars = ci['tvars']
    subst = unify_tree(lhs_tree, subtree_a, tvars)
    if subst is not None:
        subst2 = unify_tree(rhs_tree, subtree_b, tvars, dict(subst))
        if subst2 is not None:
            for v in ci['quant_vars']:
                if v not in subst2:
                    subst2[v] = default_fill
            return ' '.join(subst2[v] for v in ci['quant_vars'])
    subst = unify_tree(rhs_tree, subtree_a, tvars)
    if subst is not None:
        subst2 = unify_tree(lhs_tree, subtree_b, tvars, dict(subst))
        if subst2 is not None:
            for v in ci['quant_vars']:
                if v not in subst2:
                    subst2[v] = default_fill
            args = ' '.join(subst2[v] for v in ci['quant_vars'])
            return args + "|symm"
    return None


def find_constancy_step(tree_a, tree_b, ci_list, default_fill, path_prefix=""):
    """Find a single constancy step at any subtree of tree_a vs tree_b.
    Returns (path, args, symm, ci_idx) or None."""
    if tree_a == tree_b:
        return None
    for ci_idx, ci in enumerate(ci_list):
        result = try_constancy_at(tree_a, tree_b, ci, default_fill)
        if result is not None:
            symm = result.endswith("|symm")
            args = result.replace("|symm", "")
            return (path_prefix, args, symm, ci_idx)
    if tree_a[0] == 'op' and tree_b[0] == 'op':
        if tree_a[1] != tree_b[1]:
            r = find_constancy_step(tree_a[1], tree_b[1], ci_list, default_fill, path_prefix + "L")
            if r is not None:
                return r
        if tree_a[2] != tree_b[2]:
            r = find_constancy_step(tree_a[2], tree_b[2], ci_list, default_fill, path_prefix + "R")
            if r is not None:
                return r
    return None


def find_constancy_steps(start_tree, goal_tree, ci_list, default_fill, max_steps=4):
    """Find a sequence of constancy steps from start_tree to goal_tree.
    Returns list of (path, args, symm, ci_idx) or empty list if not possible."""
    steps = []
    current = start_tree
    for _ in range(max_steps):
        if current == goal_tree:
            break
        step = find_constancy_step(current, goal_tree, ci_list, default_fill)
        if step is None:
            return []
        steps.append(step)
        path = step[0]
        target_sub = get_subtree(goal_tree, path)
        current = apply_rewrite_at(current, path, target_sub)
    if current != goal_tree:
        return []
    return steps


def build_constancy_proof(intro, eq2_lhs, eq2_rhs, gl_tree, gr_tree,
                          proof_steps, constancy_info, hconst_prefix="hconst"):
    """Build a Lean proof from constancy steps."""
    ci_used = {}
    have_lines = []
    next_name_idx = 1
    for _, _, _, ci_idx in proof_steps:
        if ci_idx not in ci_used:
            name = hconst_prefix if next_name_idx == 1 else f"{hconst_prefix}{next_name_idx}"
            ci_info = constancy_info[ci_idx]
            line = ci_info['have_line']
            if next_name_idx > 1 or hconst_prefix != "hconst":
                line = line.replace('hconst', name, 1)
            have_lines.append(line)
            ci_used[ci_idx] = name
            next_name_idx += 1

    if len(proof_steps) == 1:
        path, args, symm, ci_idx = proof_steps[0]
        hname = ci_used[ci_idx]
        inner = f"({hname} {args})" if not symm else f"({hname} {args}).symm"
        full_proof = wrap_congr_arg(gl_tree, path, inner)
        return f"{intro}\n" + "\n".join(have_lines) + f"\nexact {full_proof}"
    else:
        calc_lines = [f"calc {eq2_lhs}"]
        current_tree = gl_tree
        for i, (path, args, symm, ci_idx) in enumerate(proof_steps):
            hname = ci_used[ci_idx]
            inner = f"({hname} {args})" if not symm else f"({hname} {args}).symm"
            step_proof = wrap_congr_arg(current_tree, path, inner)
            target_sub = get_subtree(gr_tree, path)
            current_tree = apply_rewrite_at(current_tree, path, target_sub)
            current_str = tree_to_str(current_tree)
            if i < len(proof_steps) - 1:
                calc_lines.append(f"  _ = {current_str} := {step_proof}")
            else:
                calc_lines.append(f"  _ = {eq2_rhs} := {step_proof}")
        return f"{intro}\n" + "\n".join(have_lines) + "\n" + "\n".join(calc_lines)


def build_constancy_info(eq1_text, eq1_vars, eq2_vars):
    """Build constancy lemma info from free variables in the hypothesis.
    Returns (constancy_info_list, lhs_only_set, rhs_only_set)."""
    parts1 = eq1_text.split('=', 1)
    if len(parts1) != 2:
        return [], set(), set()
    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    lhs_vars = set(re.findall(r'\b([a-z])\b', eq1_lhs))
    rhs_vars = set(re.findall(r'\b([a-z])\b', eq1_rhs))
    lhs_only = lhs_vars - rhs_vars
    rhs_only = rhs_vars - lhs_vars

    constancy_info = []

    for fvar in sorted(rhs_only):
        pos = eq1_vars.index(fvar) if fvar in eq1_vars else -1
        if pos < 0:
            continue
        used = set(eq1_vars) | set(eq2_vars)
        fresh = []
        for c in 'abcdefghijklmnopqrstuvwxyz':
            if c not in used:
                fresh.append(c)
            if len(fresh) >= 2:
                break
        if len(fresh) < 2:
            continue
        fa, fb = fresh[0], fresh[1]
        args_a = list(eq1_vars)
        args_b = list(eq1_vars)
        args_a[pos] = fa
        args_b[pos] = fb
        rhs_a = re.sub(r'\b' + fvar + r'\b', fa, eq1_rhs)
        rhs_b = re.sub(r'\b' + fvar + r'\b', fb, eq1_rhs)
        other_vars = [v for i, v in enumerate(eq1_vars) if i != pos]
        quant_vars = other_vars + [fa, fb]
        lemma_proof = f"(h {' '.join(args_a)}).symm.trans (h {' '.join(args_b)})"
        have_line = (
            f"have hconst : \u2200 ({' '.join(quant_vars)} : G), "
            f"{rhs_a} = {rhs_b} := "
            f"fun {' '.join(quant_vars)} => {lemma_proof}"
        )
        constancy_info.append({
            'have_line': have_line,
            'lhs_template': rhs_a,
            'rhs_template': rhs_b,
            'tvars': set(quant_vars),
            'quant_vars': quant_vars,
        })

    for fvar in sorted(lhs_only):
        pos = eq1_vars.index(fvar) if fvar in eq1_vars else -1
        if pos < 0:
            continue
        used = set(eq1_vars) | set(eq2_vars)
        fresh = []
        for c in 'abcdefghijklmnopqrstuvwxyz':
            if c not in used:
                fresh.append(c)
            if len(fresh) >= 2:
                break
        if len(fresh) < 2:
            continue
        fa, fb = fresh[0], fresh[1]
        args_a = list(eq1_vars)
        args_b = list(eq1_vars)
        args_a[pos] = fa
        args_b[pos] = fb
        lhs_a = re.sub(r'\b' + fvar + r'\b', fa, eq1_lhs)
        lhs_b = re.sub(r'\b' + fvar + r'\b', fb, eq1_lhs)
        other_vars = [v for i, v in enumerate(eq1_vars) if i != pos]
        quant_vars = other_vars + [fa, fb]
        lemma_proof = f"(h {' '.join(args_a)}).trans (h {' '.join(args_b)}).symm"
        have_line = (
            f"have hconst : \u2200 ({' '.join(quant_vars)} : G), "
            f"{lhs_a} = {lhs_b} := "
            f"fun {' '.join(quant_vars)} => {lemma_proof}"
        )
        constancy_info.append({
            'have_line': have_line,
            'lhs_template': lhs_a,
            'rhs_template': lhs_b,
            'tvars': set(quant_vars),
            'quant_vars': quant_vars,
        })

    return constancy_info, lhs_only, rhs_only


def simultaneous_subst(text, var_list, combo):
    """Simultaneous substitution avoiding variable collision.
    First replaces all vars with unique placeholders, then replaces placeholders with targets."""
    result = text
    placeholders = []
    for i, v in enumerate(var_list):
        ph = f"__PH{i}__"
        placeholders.append(ph)
        result = re.sub(r'\b' + v + r'\b', ph, result)
    for ph, replacement in zip(placeholders, combo):
        result = result.replace(ph, replacement)
    return result


def compute_h_instantiations(eq1_text, eq1_vars, eq2_vars):
    """Compute concrete results of calling h with various substitutions.
    Returns list of strings like 'h x y : x = y ◇ (y ◇ x)'"""
    parts = eq1_text.split('=', 1)
    if len(parts) != 2:
        return []
    lhs = parts[0].strip()
    rhs = parts[1].strip()
    results = []
    seen = set()

    # Generate substitutions using eq2_vars
    target_vars = eq2_vars if eq2_vars else ['x', 'y']
    all_combos = list(product(target_vars, repeat=len(eq1_vars)))
    # Prioritize: all-same, pairs, then others
    priority = []
    for combo in all_combos:
        unique = len(set(combo))
        priority.append((unique, combo))
    priority.sort()

    for _, combo in priority[:12]:
        new_lhs = simultaneous_subst(lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(rhs, eq1_vars, combo)
        if new_lhs.replace(' ', '') == new_rhs.replace(' ', ''):
            continue
        key = (new_lhs.replace(' ', ''), new_rhs.replace(' ', ''))
        if key in seen:
            continue
        seen.add(key)
        args = ' '.join(combo)
        results.append(f"h {args} : {new_lhs} = {new_rhs}")

    return results


def analyze_equation_structure(eq1_text, eq2_text):
    """Analyze structural relationship between hypothesis and goal."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    notes = []

    # Check if goal is a specialization of hypothesis
    if len(eq2_vars) <= len(eq1_vars):
        notes.append(f"Goal has {len(eq2_vars)} vars, hypothesis has {len(eq1_vars)} vars - might be a direct substitution")

    # Check LHS structure
    eq1_parts = eq1_text.split('=', 1)
    eq2_parts = eq2_text.split('=', 1)

    if eq1_parts[0].strip() == eq2_parts[0].strip():
        notes.append("Both sides have same LHS - focus on transforming the RHS")

    # Check for shared subterms
    eq1_rhs = eq1_parts[1].strip() if len(eq1_parts) == 2 else ""
    eq2_rhs = eq2_parts[1].strip() if len(eq2_parts) == 2 else ""
    eq2_lhs = eq2_parts[0].strip()

    # Free variable analysis
    lhs_var = eq1_parts[0].strip()
    if len(lhs_var) == 1:
        rhs_free = set(re.findall(r'\b([a-z])\b', eq1_rhs))
        if lhs_var not in rhs_free:
            notes.append(f"Hypothesis has '{lhs_var}' only on LHS - forces singleton (all elements equal)")
        else:
            free_in_rhs_not_lhs = rhs_free - {lhs_var}
            notes.append(f"Free variables in hypothesis RHS: {rhs_free}")
            if free_in_rhs_not_lhs:
                notes.append(f"Variables only in RHS (universally quantified): {free_in_rhs_not_lhs}")

    return notes


def deep_proof_analysis(eq1_text, eq2_text):
    """Deeper analysis for hard true-implication problems.
    Returns structured hints about proof strategy."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    eq1_parts = eq1_text.split('=', 1)
    eq2_parts = eq2_text.split('=', 1)
    if len(eq1_parts) != 2 or len(eq2_parts) != 2:
        return []

    eq1_lhs = eq1_parts[0].strip()
    eq1_rhs = eq1_parts[1].strip()
    eq2_lhs = eq2_parts[0].strip()
    eq2_rhs = eq2_parts[1].strip()

    hints = []
    eq1_lhs_vars = set(re.findall(r'\b([a-z])\b', eq1_lhs))
    eq1_rhs_vars = set(re.findall(r'\b([a-z])\b', eq1_rhs))
    eq2_lhs_vars = set(re.findall(r'\b([a-z])\b', eq2_lhs))
    eq2_rhs_vars = set(re.findall(r'\b([a-z])\b', eq2_rhs))

    # Free variable analysis: variables that appear on only one side of h
    lhs_only = eq1_lhs_vars - eq1_rhs_vars
    rhs_only = eq1_rhs_vars - eq1_lhs_vars

    both_sides = eq1_lhs_vars & eq1_rhs_vars

    if rhs_only:
        if both_sides:
            hints.append(
                f"CONSTANCY: Variables {rhs_only} appear ONLY on the RHS of h. "
                f"For FIXED {both_sides}, the RHS is constant regardless of {rhs_only}. "
                f"So h(same_x, y1, z1) and h(same_x, y2, z2) give the same LHS. "
                f"WARNING: The RHS still DEPENDS on {both_sides} — different {both_sides} values "
                f"give DIFFERENT results. Do NOT claim all elements are equal unless you can prove it."
            )
        else:
            hints.append(
                f"CONSTANCY: Variables {rhs_only} appear ONLY on the RHS of h. "
                f"The RHS is a GLOBAL CONSTANT (same for ALL inputs). "
                f"So `{eq1_lhs}` has the same value for every choice of {rhs_only}."
            )
        for v in rhs_only:
            hints.append(
                f"  Proof technique: h ... {v}=a ... and h ... {v}=b ... give the same LHS, "
                f"so you can set {v} to any value."
            )
    if lhs_only:
        if both_sides:
            hints.append(
                f"CONSTANCY: Variables {lhs_only} appear ONLY on the LHS. "
                f"For FIXED {both_sides}, the LHS is constant regardless of {lhs_only}. "
                f"WARNING: The LHS still DEPENDS on {both_sides}."
            )
        else:
            hints.append(
                f"CONSTANCY: Variables {lhs_only} appear ONLY on the LHS. "
                f"The LHS is a GLOBAL CONSTANT."
        )

    # Check if goal can be obtained by direct substitution
    for combo in product(eq2_vars, repeat=len(eq1_vars)):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        if (new_lhs.replace(' ', '') == eq2_lhs.replace(' ', '') and
                new_rhs.replace(' ', '') == eq2_rhs.replace(' ', '')):
            args = ' '.join(combo)
            hints.insert(0,
                f"DIRECT PROOF FOUND: h {args} gives exactly the goal! "
                f"Proof: intro {' '.join(eq2_vars)}; exact h {args}"
            )
            return hints
        if (new_lhs.replace(' ', '') == eq2_rhs.replace(' ', '') and
                new_rhs.replace(' ', '') == eq2_lhs.replace(' ', '')):
            args = ' '.join(combo)
            hints.insert(0,
                f"DIRECT PROOF FOUND: (h {args}).symm gives exactly the goal! "
                f"Proof: intro {' '.join(eq2_vars)}; exact (h {args}).symm"
            )
            return hints

    # Build all instantiations for chain search
    all_insts = {}  # (lhs_norm, rhs_norm) -> args_string
    for combo in product(eq2_vars, repeat=len(eq1_vars)):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        if new_lhs.replace(' ', '') == new_rhs.replace(' ', ''):
            continue
        key = (new_lhs.replace(' ', ''), new_rhs.replace(' ', ''))
        if key not in all_insts:
            all_insts[key] = ' '.join(combo)

    # Try two-step calc chain: goal_lhs = mid (by h sub1) = goal_rhs (by h sub2)
    # or: goal_lhs = h1_rhs (by h sub1, if h1_lhs == goal_lhs)
    #     h1_rhs = goal_rhs (by h sub2, if h2 connects them)
    two_step_found = False
    g_lhs = eq2_lhs.replace(' ', '')
    g_rhs = eq2_rhs.replace(' ', '')

    # Find all h instantiations where LHS matches goal LHS
    step1_candidates = {}  # rhs_norm -> args
    for (l, r), args in all_insts.items():
        if l == g_lhs:
            if r not in step1_candidates:
                step1_candidates[r] = args
        # Also try symmetric
        if r == g_lhs:
            if l not in step1_candidates:
                step1_candidates[l] = f"({args}).symm → "

    # For each step1 result, see if another h instantiation can reach goal RHS
    for mid, args1 in step1_candidates.items():
        for (l, r), args2 in all_insts.items():
            if l == mid and r == g_rhs:
                hints.append(
                    f"TWO-STEP PROOF: calc {eq2_lhs}\n"
                    f"  _ = [mid] := by exact h {args1}\n"
                    f"  _ = {eq2_rhs} := by exact h {args2}"
                )
                two_step_found = True
                break
            if r == mid and l == g_rhs:
                hints.append(
                    f"TWO-STEP PROOF: calc {eq2_lhs}\n"
                    f"  _ = [mid] := by exact h {args1}\n"
                    f"  _ = {eq2_rhs} := by exact (h {args2}).symm"
                )
                two_step_found = True
                break
        if two_step_found:
            break

    if not two_step_found:
        hints.append(
            "PROOF STRATEGY: Use a calc chain or transitivity. "
            "Apply h with specific args to rewrite, then apply h again with different args."
        )

    # Show best matching instantiations
    best_matches = []
    for (l, r), args in all_insts.items():
        score = string_overlap(l + "=" + r, g_lhs + "=" + g_rhs)
        best_matches.append((score, args, l, r))
    best_matches.sort(reverse=True)
    shown = set()
    for score, args, nlhs, nrhs in best_matches[:6]:
        key = (nlhs, nrhs)
        if key not in shown:
            shown.add(key)
            hints.append(f"  Useful: h {args} : {nlhs} = {nrhs}")

    return hints


def compute_proof_skeleton(eq1_text, eq2_text, eq1_vars, eq2_vars):
    """Generate a proof skeleton with specific guidance for the LLM.
    Analyzes structural similarities between h and goal to suggest approaches."""
    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return ""

    h_lhs = parts1[0].strip()
    h_rhs = parts1[1].strip()
    g_lhs = parts2[0].strip()
    g_rhs = parts2[1].strip()

    hints = []

    # Detect shared right/left operand in goal: (A ◇ B) = (C ◇ B) → need A = C
    g_lhs_tree = parse_op_tree(g_lhs)
    g_rhs_tree = parse_op_tree(g_rhs)

    if g_lhs_tree[0] == 'op' and g_rhs_tree[0] == 'op':
        l_left, l_right = g_lhs_tree[1], g_lhs_tree[2]
        r_left, r_right = g_rhs_tree[1], g_rhs_tree[2]
        l_right_s = tree_to_str(l_right).replace(' ', '')
        r_right_s = tree_to_str(r_right).replace(' ', '')
        l_left_s = tree_to_str(l_left).replace(' ', '')
        r_left_s = tree_to_str(r_left).replace(' ', '')

        if l_right_s == r_right_s:
            shared = tree_to_str(l_right)
            need_a = tree_to_str(l_left)
            need_b = tree_to_str(r_left)
            hints.append(
                f"STRUCTURAL: Goal has form (A ◇ {shared}) = (B ◇ {shared}). "
                f"If you can prove {need_a} = {need_b}, then use congr_arg (· ◇ {shared}) <proof>."
            )
        elif l_left_s == r_left_s:
            shared = tree_to_str(l_left)
            need_a = tree_to_str(l_right)
            need_b = tree_to_str(r_right)
            hints.append(
                f"STRUCTURAL: Goal has form ({shared} ◇ A) = ({shared} ◇ B). "
                f"If you can prove {need_a} = {need_b}, then use congr_arg ({shared} ◇ ·) <proof>."
            )

    # Detect if goal is structurally similar to h (same shape, different variables)
    h_lhs_n = h_lhs.replace(' ', '')
    h_rhs_n = h_rhs.replace(' ', '')
    g_lhs_n = g_lhs.replace(' ', '')
    g_rhs_n = g_rhs.replace(' ', '')

    # Check if h and goal have the same operator tree shape
    def tree_shape(t):
        if t[0] == 'var': return 'v'
        return f'({tree_shape(t[1])}◇{tree_shape(t[2])})'

    h_lhs_shape = tree_shape(parse_op_tree(h_lhs))
    h_rhs_shape = tree_shape(parse_op_tree(h_rhs))
    g_lhs_shape = tree_shape(parse_op_tree(g_lhs))
    g_rhs_shape = tree_shape(parse_op_tree(g_rhs))

    if h_lhs_shape == g_lhs_shape and h_rhs_shape == g_rhs_shape:
        hints.append(
            f"SHAPE MATCH: Goal has identical tree shape to h. "
            f"A direct substitution should work if you find the right variable mapping."
        )
    elif h_lhs_shape == g_rhs_shape and h_rhs_shape == g_lhs_shape:
        hints.append(
            f"SHAPE MATCH (symm): Goal reversed has identical tree shape to h. "
            f"Try (h args).symm."
        )

    # Detect: h says x = f(x,...) where x appears on both sides
    h_lhs_vars = set(re.findall(r'\b([a-z])\b', h_lhs))
    h_rhs_vars = set(re.findall(r'\b([a-z])\b', h_rhs))
    self_ref_vars = h_lhs_vars & h_rhs_vars
    rhs_only_vars = h_rhs_vars - h_lhs_vars

    if self_ref_vars and rhs_only_vars:
        hints.append(
            f"RECURSIVE STRUCTURE: h says {h_lhs} = {h_rhs}. "
            f"Variable(s) {self_ref_vars} appear on both sides. "
            f"You can substitute h into itself: "
            f"first apply h to get {h_lhs} = ..., then apply h again to a sub-expression to rewrite further. "
            f"Since {rhs_only_vars} are free, you can set them to goal-relevant values at each step."
        )

    return "\n".join(hints) if hints else ""


def compute_match_collapse_hints(eq1_text, eq2_text):
    """Generate MATCH-COLLAPSE proof strategy hints for the LLM.
    Analyzes how to:
    1. MATCH: substitute compound terms into h to match the goal's outer structure
    2. COLLAPSE: use constancy to simplify the inner part
    """
    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return ""

    h_lhs = parts1[0].strip()
    h_rhs = parts1[1].strip()
    g_lhs = parts2[0].strip()
    g_rhs = parts2[1].strip()

    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    # Identify free variables (appear only on one side of h)
    h_lhs_vars = set(re.findall(r'\b([a-z])\b', h_lhs.replace('◇', '')))
    h_rhs_vars = set(re.findall(r'\b([a-z])\b', h_rhs.replace('◇', '')))
    rhs_free = h_rhs_vars - h_lhs_vars
    lhs_free = h_lhs_vars - h_rhs_vars
    anchored = h_lhs_vars & h_rhs_vars  # appear on both sides

    hints = []

    # Describe h structure
    hints.append(f"h structure: {h_lhs} = {h_rhs}")
    if rhs_free:
        hints.append(f"  Free vars (RHS only): {', '.join(sorted(rhs_free))}")
        hints.append(f"  Anchored vars (both sides): {', '.join(sorted(anchored))}")
        hints.append(f"  Constancy: for fixed {', '.join(sorted(anchored))}, "
                     f"changing {', '.join(sorted(rhs_free))} doesn't change {h_lhs}")
        # Generate the constancy lemma template
        anchor_args = ' '.join(sorted(anchored))
        free_args_a = ' '.join(f'{v}1' for v in sorted(rhs_free))
        free_args_b = ' '.join(f'{v}2' for v in sorted(rhs_free))
        hints.append(f"  Constancy proof: (h {anchor_args} {free_args_a}).symm.trans (h {anchor_args} {free_args_b})")
    if lhs_free:
        hints.append(f"  Free vars (LHS only): {', '.join(sorted(lhs_free))}")
        hints.append(f"  Constancy: for fixed {', '.join(sorted(anchored))}, "
                     f"changing {', '.join(sorted(lhs_free))} doesn't change {h_rhs}")

    # MATCH analysis: what compound substitutions would align h-RHS with goal structure
    hints.append("")
    hints.append("MATCH analysis:")

    # Parse goal into tree structure
    g_lhs_tree = parse_op_tree(g_lhs)
    g_rhs_tree = parse_op_tree(g_rhs)
    h_rhs_tree = parse_op_tree(h_rhs)

    # If goal is x = ... and h is x = RHS(x, free_vars),
    # then goal requires proving x = goal_RHS, and h gives x = h_RHS(x, free)
    # So we need h_RHS(x, free) = goal_RHS for some choice of free vars
    if h_lhs == g_lhs == 'x':
        hints.append(f"  Both h and goal have LHS = x")
        hints.append(f"  Need: {h_rhs} (with free vars chosen) = {g_rhs}")
        hints.append(f"  Strategy: Apply h x free1 free2 to get x = {h_rhs}")
        hints.append(f"  Then show {h_rhs}[free:=...] = {g_rhs} using constancy")
        # Compare RHS structures at the top level
        h_rhs_tree = parse_op_tree(h_rhs)
        g_rhs_tree = parse_op_tree(g_rhs)
        if isinstance(h_rhs_tree, tuple) and isinstance(g_rhs_tree, tuple):
            h_left_str = tree_to_str(h_rhs_tree[1])
            h_right_str = tree_to_str(h_rhs_tree[2])
            g_left_str = tree_to_str(g_rhs_tree[1])
            g_right_str = tree_to_str(g_rhs_tree[2])
            hints.append(f"  h RHS top-level: ({h_left_str}) ◇ ({h_right_str})")
            hints.append(f"  goal RHS top-level: ({g_left_str}) ◇ ({g_right_str})")
            # If h RHS top-left matches goal RHS top-left, we just need inner match
            if h_left_str.replace(' ', '') == g_left_str.replace(' ', ''):
                hints.append(f"  GOOD: h and goal have same outer-left structure!")
                hints.append(f"  Just need inner: {h_right_str} [free:=...] = {g_right_str}")
                hints.append(f"  This means: find values for {', '.join(sorted(rhs_free))} such that")
                hints.append(f"    {h_right_str} = {g_right_str}")
            else:
                # Check if setting a free var could make them match
                for v in rhs_free:
                    # Try setting v to goal_left
                    test_left = h_left_str.replace(v, f'({g_left_str})')
                    hints.append(f"  If {v} := {g_left_str}, h outer-left becomes: {test_left}")
                hints.append(f"  Use congr_arg ({g_left_str} ◇ ·) <proof> to handle inner part")

    elif h_lhs.replace(' ', '') == g_lhs.replace(' ', ''):
        # h and goal have matching LHS (e.g., x ◇ x = ...)
        hints.append(f"  h and goal have the SAME LHS: {h_lhs}")
        hints.append(f"  Need: {h_rhs} (with free vars chosen) = {g_rhs}")
        hints.append(f"  Strategy: Apply h with specific args, then use constancy")
        # Compare RHS structures
        h_rhs_tree_local = parse_op_tree(h_rhs)
        g_rhs_tree_local = parse_op_tree(g_rhs)
        if isinstance(h_rhs_tree_local, tuple) and isinstance(g_rhs_tree_local, tuple):
            h_left = tree_to_str(h_rhs_tree_local[1])
            h_right = tree_to_str(h_rhs_tree_local[2])
            g_left_s = tree_to_str(g_rhs_tree_local[1])
            g_right_s = tree_to_str(g_rhs_tree_local[2])
            hints.append(f"  h RHS: ({h_left}) ◇ ({h_right})")
            hints.append(f"  goal RHS: ({g_left_s}) ◇ ({g_right_s})")
            # Check if setting a free var makes outer-left match
            for v in rhs_free:
                test = h_left.replace(v, f'({g_left_s})')
                if test.replace(' ', '') == g_left_s.replace(' ', ''):
                    hints.append(f"  KEY: Set {v} := {g_left_s} makes h outer-left = goal outer-left!")
                    hints.append(f"    Then h RHS inner becomes: {h_right.replace(v, '(' + g_left_s + ')')}")
                    hints.append(f"    Use constancy to show inner = {g_right_s}")
                else:
                    hints.append(f"  If {v} := {g_left_s}, h outer-left becomes: {test}")
    elif h_lhs == 'x' and g_lhs != 'x':
        # Goal LHS is more complex, e.g., (x ◇ y) ◇ z
        hints.append(f"  h gives x = {h_rhs}. Goal LHS is {g_lhs}.")
        hints.append(f"  Apply h to get {g_lhs} = {h_rhs}[x:={g_lhs}]")
        hints.append(f"  Then simplify to reach {g_rhs}")
        # Also: apply h to parts of g_lhs
        g_lhs_sub = re.findall(r'[a-z]', g_lhs.replace('◇', ''))
        for v in set(g_lhs_sub):
            hints.append(f"  Or: apply h to {v} inside {g_lhs} with suitable free vars")

    # For goals like A ◇ B = C ◇ D where h is x = something
    if '◇' in g_lhs and '◇' in g_rhs and h_lhs == 'x':
        hints.append(f"  Goal has binary structure on both sides.")
        hints.append(f"  MATCH step: set h args so that {h_rhs} starts with the goal's outer operator")

        # If h_rhs is of form A ◇ B:
        if isinstance(h_rhs_tree, tuple) and len(h_rhs_tree) == 3:
            _op, h_outer_left, h_outer_right = h_rhs_tree
            left_str = tree_to_str(h_outer_left)
            right_str = tree_to_str(h_outer_right)

            # Identify which h-var controls the outer left part
            left_vars = set(re.findall(r'\b([a-z])\b', left_str.replace('◇', '')))
            right_vars = set(re.findall(r'\b([a-z])\b', right_str.replace('◇', '')))

            non_free_in_left = left_vars - rhs_free
            non_free_in_right = right_vars - rhs_free

            if non_free_in_left:
                anchor_var = sorted(non_free_in_left)[0]
                # If goal RHS is (E1) ◇ (E2), suggest setting anchor_var to E1
                if isinstance(g_rhs_tree, tuple) and len(g_rhs_tree) == 3:
                    g_outer_left_str = tree_to_str(g_rhs_tree[1])
                    g_outer_right_str = tree_to_str(g_rhs_tree[2])
                    hints.append(f"  Suggestion: set {anchor_var} := {g_outer_left_str} in h")
                    hints.append(f"    This makes h's RHS start with {left_str}[{anchor_var}:={g_outer_left_str}]")
                    hints.append(f"    Then use constancy to make the rest equal {g_outer_right_str}")

    # COLLAPSE analysis
    hints.append("")
    hints.append("COLLAPSE analysis:")
    if rhs_free:
        hints.append(f"  Since {', '.join(sorted(rhs_free))} are free, after MATCH step you get:")
        hints.append(f"    goal_outer ◇ (junk_involving_free_vars)")
        hints.append(f"  Use congr_arg (goal_outer ◇ ·) <constancy_proof> to simplify junk to goal_inner")
        hints.append(f"  The constancy proof: (h a {' '.join(['b']*len(rhs_free))}).symm.trans (h a {' '.join(['c']*len(rhs_free))})")
    elif lhs_free:
        hints.append(f"  Since {', '.join(sorted(lhs_free))} are free, the LHS side has constancy.")
        hints.append(f"  Use (h {' '.join(['a']*len(lhs_free))} b).trans (h {' '.join(['c']*len(lhs_free))} b).symm")
    else:
        hints.append(f"  No free variables — use compound instantiation of h to bridge gap.")

    return "\n".join(hints)


def compute_equation_analysis(eq1_text, eq2_text):
    """Generate detailed equation analysis for the LLM prompt."""
    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return ""

    h_lhs = parts1[0].strip()
    h_rhs = parts1[1].strip()
    g_lhs = parts2[0].strip()
    g_rhs = parts2[1].strip()

    eq1_vars = parse_variables(eq1_text)

    # Free variable analysis
    h_lhs_vars = set(re.findall(r'\b([a-z])\b', h_lhs.replace('◇', '')))
    h_rhs_vars = set(re.findall(r'\b([a-z])\b', h_rhs.replace('◇', '')))
    rhs_free = sorted(h_rhs_vars - h_lhs_vars)
    lhs_free = sorted(h_lhs_vars - h_rhs_vars)
    anchored = sorted(h_lhs_vars & h_rhs_vars)

    lines = []
    lines.append(f"h: {h_lhs} = {h_rhs}")
    lines.append(f"  Variables: {', '.join(eq1_vars)}")
    lines.append(f"  Anchored (both sides): {', '.join(anchored) if anchored else 'none'}")
    lines.append(f"  Free on RHS only: {', '.join(rhs_free) if rhs_free else 'none'}")
    lines.append(f"  Free on LHS only: {', '.join(lhs_free) if lhs_free else 'none'}")

    # Constancy lemma
    if rhs_free:
        anchor_str = ' '.join(anchored)
        free_a = ' '.join(f'a{i}' for i in range(len(rhs_free)))
        free_b = ' '.join(f'b{i}' for i in range(len(rhs_free)))
        lines.append(f"  Constancy: (h {anchor_str} {free_a}).symm.trans (h {anchor_str} {free_b})")
        lines.append(f"    This proves: {h_rhs}[{','.join(rhs_free)}:=a...] = {h_rhs}[{','.join(rhs_free)}:=b...]")
    if lhs_free:
        anchor_str = ' '.join(anchored)
        free_a = ' '.join(f'a{i}' for i in range(len(lhs_free)))
        free_b = ' '.join(f'b{i}' for i in range(len(lhs_free)))
        lines.append(f"  Constancy: (h {free_a} {anchor_str}).trans (h {free_b} {anchor_str}).symm")
        lines.append(f"    This proves: {h_lhs}[{','.join(lhs_free)}:=a...] = {h_lhs}[{','.join(lhs_free)}:=b...]")

    lines.append("")
    lines.append(f"Goal: {g_lhs} = {g_rhs}")

    return "\n".join(lines)


def generate_lean_constancy_lemma(eq1_text):
    """Generate the exact Lean 'have hc' statement for the constancy lemma from h.
    Returns (lean_code, description) or (None, None) if no free vars."""
    parts = eq1_text.split('=', 1)
    if len(parts) != 2:
        return None, None

    h_lhs = parts[0].strip()
    h_rhs = parts[1].strip()
    eq_vars = parse_variables(eq1_text)

    h_lhs_vars = set(re.findall(r'\b([a-z])\b', h_lhs.replace('◇', '')))
    h_rhs_vars = set(re.findall(r'\b([a-z])\b', h_rhs.replace('◇', '')))
    rhs_free = sorted(h_rhs_vars - h_lhs_vars)
    lhs_free = sorted(h_lhs_vars - h_rhs_vars)
    anchored = sorted(h_lhs_vars & h_rhs_vars)

    if not rhs_free and not lhs_free:
        return None, None

    if rhs_free:
        # Build hc type: for all args, RHS[free:=a...] = RHS[free:=b...]
        # We need to generate the universally quantified statement
        # The constancy lemma is: (h anchored free_a...).symm.trans (h anchored free_b...)
        all_vars = list(eq_vars)
        # Map: variable name -> position in h args
        # h takes args in order of eq_vars

        # Generate fresh variable names for the universally quantified version
        # Use letters that don't conflict
        used_names = set(eq_vars)
        fresh = []
        for c in 'abcdefghijklmnopqrstuvwxyz':
            if c not in used_names:
                fresh.append(c)
            if len(fresh) >= len(anchored) + 2 * len(rhs_free):
                break

        anchor_names = fresh[:len(anchored)]
        free_a_names = fresh[len(anchored):len(anchored) + len(rhs_free)]
        free_b_names = fresh[len(anchored) + len(rhs_free):len(anchored) + 2 * len(rhs_free)]

        if len(anchor_names) < len(anchored) or len(free_b_names) < len(rhs_free):
            return None, None

        # Build the RHS expression with substitution
        def subst_expr(expr, mapping):
            result = expr
            for old, new in mapping.items():
                result = re.sub(r'\b' + old + r'\b', new, result)
            return result

        map_a = {}
        map_b = {}
        for i, v in enumerate(anchored):
            map_a[v] = anchor_names[i]
            map_b[v] = anchor_names[i]
        for i, v in enumerate(rhs_free):
            map_a[v] = free_a_names[i]
            map_b[v] = free_b_names[i]

        rhs_a = subst_expr(h_rhs, map_a)
        rhs_b = subst_expr(h_rhs, map_b)

        # Build h arg order for the .symm.trans proof term
        def build_h_args(mapping):
            return ' '.join(mapping.get(v, v) for v in eq_vars)

        h_args_a = build_h_args(map_a)
        h_args_b = build_h_args(map_b)

        all_quant = ' '.join(anchor_names + free_a_names + free_b_names)
        quant_types = ' '.join(f'({v} : G)' for v in anchor_names + free_a_names + free_b_names)

        lean_code = (
            f"  have hc : ∀ {quant_types}, "
            f"{rhs_a} = {rhs_b} := "
            f"fun {all_quant} => (h {h_args_a}).symm.trans (h {h_args_b})"
        )

        desc = (f"hc lets you replace {', '.join(rhs_free)} in h's RHS with ANY values, "
                f"keeping {', '.join(anchored)} fixed")
        return lean_code, desc

    if lhs_free:
        used_names = set(eq_vars)
        fresh = []
        for c in 'abcdefghijklmnopqrstuvwxyz':
            if c not in used_names:
                fresh.append(c)
            if len(fresh) >= len(anchored) + 2 * len(lhs_free):
                break

        anchor_names = fresh[:len(anchored)]
        free_a_names = fresh[len(anchored):len(anchored) + len(lhs_free)]
        free_b_names = fresh[len(anchored) + len(lhs_free):len(anchored) + 2 * len(lhs_free)]

        if len(anchor_names) < len(anchored) or len(free_b_names) < len(lhs_free):
            return None, None

        def subst_expr(expr, mapping):
            result = expr
            for old, new in mapping.items():
                result = re.sub(r'\b' + old + r'\b', new, result)
            return result

        map_a = {}
        map_b = {}
        for i, v in enumerate(anchored):
            map_a[v] = anchor_names[i]
            map_b[v] = anchor_names[i]
        for i, v in enumerate(lhs_free):
            map_a[v] = free_a_names[i]
            map_b[v] = free_b_names[i]

        lhs_a = subst_expr(h_lhs, map_a)
        lhs_b = subst_expr(h_lhs, map_b)

        def build_h_args(mapping):
            return ' '.join(mapping.get(v, v) for v in eq_vars)

        h_args_a = build_h_args(map_a)
        h_args_b = build_h_args(map_b)

        all_quant = ' '.join(anchor_names + free_a_names + free_b_names)
        quant_types = ' '.join(f'({v} : G)' for v in anchor_names + free_a_names + free_b_names)

        lean_code = (
            f"  have hc : ∀ {quant_types}, "
            f"{lhs_a} = {lhs_b} := "
            f"fun {all_quant} => (h {h_args_a}).trans (h {h_args_b}).symm"
        )

        desc = (f"hc lets you replace {', '.join(lhs_free)} in h's LHS with ANY values, "
                f"keeping {', '.join(anchored)} fixed")
        return lean_code, desc

    return None, None


def analyze_goal_common_factor(eq2_text):
    """Detect common structure between LHS and RHS of the goal.
    Returns description of factoring opportunities."""
    parts = eq2_text.split('=', 1)
    if len(parts) != 2:
        return ""

    g_lhs = parts[0].strip()
    g_rhs = parts[1].strip()
    g_lhs_tree = parse_op_tree(g_lhs)
    g_rhs_tree = parse_op_tree(g_rhs)

    hints = []

    # Check if both sides are binary ops
    if isinstance(g_lhs_tree, tuple) and g_lhs_tree[0] == 'op' and \
       isinstance(g_rhs_tree, tuple) and g_rhs_tree[0] == 'op':
        l_left = tree_to_str(g_lhs_tree[1])
        l_right = tree_to_str(g_lhs_tree[2])
        r_left = tree_to_str(g_rhs_tree[1])
        r_right = tree_to_str(g_rhs_tree[2])

        # Check right factor: A ◇ C = B ◇ C => congr_arg (· ◇ C) proof_of_A=B
        if l_right.replace(' ', '') == r_right.replace(' ', ''):
            hints.append(f"COMMON RIGHT FACTOR: Both sides end with ◇ {l_right}")
            hints.append(f"  Reduce to showing: {l_left} = {r_left}")
            hints.append(f"  Use: congr_arg (· ◇ {l_right}) <proof that {l_left} = {r_left}>")
            hints.append(f"  The calc chain should prove {l_left} = {r_left}, then wrap each step with congr_arg (· ◇ {l_right})")

        # Check left factor: C ◇ A = C ◇ B => congr_arg (C ◇ ·) proof_of_A=B
        if l_left.replace(' ', '') == r_left.replace(' ', ''):
            hints.append(f"COMMON LEFT FACTOR: Both sides start with {l_left} ◇")
            hints.append(f"  Reduce to showing: {l_right} = {r_right}")
            hints.append(f"  Use: congr_arg ({l_left} ◇ ·) <proof that {l_right} = {r_right}>")
            hints.append(f"  The calc chain should prove {l_right} = {r_right}, then wrap each step with congr_arg ({l_left} ◇ ·)")

        # Check if LHS or RHS is a repeated variable (x ◇ x pattern)
        if l_left.replace(' ', '') == l_right.replace(' ', ''):
            hints.append(f"LHS is self-op: {l_left} ◇ {l_left}")
        if r_left.replace(' ', '') == r_right.replace(' ', ''):
            hints.append(f"RHS is self-op: {r_left} ◇ {r_left}")

    return "\n".join(hints)


def compute_goal_reduction(eq1_text, eq2_text):
    """Compute a reduced proof goal by factoring out common parts.
    Returns (reduced_lhs, reduced_rhs, wrapper_template, description) or None."""
    parts2 = eq2_text.split('=', 1)
    if len(parts2) != 2:
        return None

    g_lhs = parts2[0].strip()
    g_rhs = parts2[1].strip()
    g_lhs_tree = parse_op_tree(g_lhs)
    g_rhs_tree = parse_op_tree(g_rhs)

    if not (isinstance(g_lhs_tree, tuple) and g_lhs_tree[0] == 'op' and
            isinstance(g_rhs_tree, tuple) and g_rhs_tree[0] == 'op'):
        return None

    l_left = tree_to_str(g_lhs_tree[1])
    l_right = tree_to_str(g_lhs_tree[2])
    r_left = tree_to_str(g_rhs_tree[1])
    r_right = tree_to_str(g_rhs_tree[2])

    if l_right.replace(' ', '') == r_right.replace(' ', ''):
        return (l_left, r_left, f"congr_arg (· ◇ {l_right})",
                f"Show {l_left} = {r_left}, then wrap with congr_arg (· ◇ {l_right})")

    if l_left.replace(' ', '') == r_left.replace(' ', ''):
        return (l_right, r_right, f"congr_arg ({l_left} ◇ ·)",
                f"Show {l_right} = {r_right}, then wrap with congr_arg ({l_left} ◇ ·)")

    return None


def generate_proof_template(eq1_text, eq2_text):
    """Generate a concrete proof template for the LLM to fill in.
    Returns a string with the template, or empty string."""
    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return ""

    h_lhs = parts1[0].strip()
    h_rhs = parts1[1].strip()
    g_lhs = parts2[0].strip()
    g_rhs = parts2[1].strip()

    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    h_lhs_vars = set(re.findall(r'\b([a-z])\b', h_lhs.replace('◇', '')))
    h_rhs_vars = set(re.findall(r'\b([a-z])\b', h_rhs.replace('◇', '')))
    rhs_free = sorted(h_rhs_vars - h_lhs_vars)
    lhs_free = sorted(h_lhs_vars - h_rhs_vars)
    anchored = sorted(h_lhs_vars & h_rhs_vars)

    if not rhs_free and not lhs_free:
        return ""

    lines = []

    # Get the constancy lemma
    lean_hc, hc_desc = generate_lean_constancy_lemma(eq1_text)
    if not lean_hc:
        return ""

    # Check for common factor reduction
    reduction = compute_goal_reduction(eq1_text, eq2_text)

    intro_vars = ' '.join(eq2_vars)

    # Helper to compute h_rhs with specific substitutions
    def subst_expr(expr, mapping):
        result = expr
        for old, new in sorted(mapping.items(), key=lambda x: -len(x[0])):
            result = re.sub(r'\b' + re.escape(old) + r'\b', '(%s)' % new, result)
        return result

    lines.append("## Pre-computed constancy lemma (paste this directly)")
    lines.append("")
    lines.append(lean_hc)
    lines.append("")
    lines.append("Meaning: %s" % hc_desc)
    lines.append("")

    if reduction:
        red_lhs, red_rhs, wrapper, desc = reduction
        lines.append("## Goal reduction")
        lines.append("Goal: %s = %s" % (g_lhs, g_rhs))
        lines.append("Both sides share a common factor. %s" % desc)
        lines.append("So you only need to prove: %s = %s" % (red_lhs, red_rhs))
        lines.append("")
        lines.append("## Proof pattern (expand → switch → collapse)")
        lines.append("```lean")
        lines.append("intro %s" % intro_vars)
        lines.append(lean_hc)
        lines.append("calc")
        lines.append("  %s = <h_expanded(%s)> ◇ ... := %s (h %s F1 F2)" % (
            g_lhs, red_lhs, wrapper, red_lhs))
        lines.append("  _ = <h_expanded(%s)> ◇ ... := %s (hc ...)" % (
            red_rhs, wrapper))
        lines.append("  _ = %s := %s (h %s F1 F2).symm" % (
            g_rhs, wrapper, red_rhs))
        lines.append("```")
        lines.append("")
        lines.append("The key steps:")
        lines.append("1. Apply `h %s F1 F2` to expand %s into h's RHS form" % (red_lhs, red_lhs))
        lines.append("2. Apply `hc` to change inner expressions (free vars can take any value)")
        lines.append("3. Apply `(h %s F1 F2).symm` to collapse back to %s" % (red_rhs, red_rhs))
        lines.append("4. Wrap each step with `%s`" % wrapper)
        lines.append("")
        lines.append("For steps 1 and 3, use the SAME free variable values F1,F2.")
        lines.append("For step 2, hc proves the middle transition because it keeps the anchored")
        lines.append("variable fixed while changing the free variables.")
    else:
        # No common factor — different patterns
        if h_lhs == 'x' and g_lhs == 'x':
            lines.append("## Proof pattern (direct h + constancy)")
            lines.append("h and goal both have LHS = x.")
            lines.append("Need to transform h's RHS into goal's RHS using constancy.")
            lines.append("")

            # Check if hc can directly bridge the gap
            # h_rhs has free vars — can we set them to get goal_rhs?
            lines.append("h gives: x = %s" % h_rhs)
            lines.append("Goal needs: x = %s" % g_rhs)
            lines.append("")

            # Check if goal_rhs has the same structure as h_rhs (differs only in free vars)
            h_rhs_template = h_rhs
            g_rhs_check = g_rhs
            for v in rhs_free:
                h_rhs_template = re.sub(r'\b' + v + r'\b', '★', h_rhs_template)
            # Anchored vars in goal should stay the same
            match_ok = True
            for v in anchored:
                if v not in re.findall(r'\b([a-z])\b', g_rhs.replace('◇', '')):
                    match_ok = False

            lines.append("```lean")
            lines.append("intro %s" % intro_vars)
            lines.append(lean_hc)
            lines.append("calc")
            lines.append("  x = %s := h x F1 F2 ..." % h_rhs)
            lines.append("  _ = %s := hc x F1 F2 ... goal_F1 goal_F2 ..." % g_rhs)
            lines.append("```")
            lines.append("")
            lines.append("Choose F1,F2 for the first h, and goal_F1,goal_F2 for the target.")
            lines.append("hc bridges between any two free-variable instantiations.")
            lines.append("BUT: if the goal RHS has a DIFFERENT structure from h's RHS")
            lines.append("(not just different free vars), you may need a multi-step approach.")

        elif h_lhs.replace(' ', '') == g_lhs.replace(' ', ''):
            lines.append("## Proof pattern (same LHS)")
            lines.append("```lean")
            lines.append("intro %s" % intro_vars)
            lines.append(lean_hc)
            lines.append("calc")
            lines.append("  %s = %s := h ..." % (h_lhs, h_rhs))
            lines.append("  _ = %s := hc ..." % g_rhs)
            lines.append("```")
        else:
            # h has x = something, goal has complex_LHS = complex_RHS
            lines.append("## Proof pattern (expand-switch-collapse)")
            lines.append("Goal LHS is %s, but h gives x = %s" % (g_lhs, h_rhs))
            lines.append("Apply h to EACH side of the goal, then use hc to bridge.")
            lines.append("")
            lines.append("```lean")
            lines.append("intro %s" % intro_vars)
            lines.append(lean_hc)
            lines.append("calc")
            lines.append("  %s = <h_expanded> := h %s F1 F2 ..." % (g_lhs, g_lhs))
            lines.append("  _ = <h_expanded_rhs> := hc ...")
            lines.append("  _ = %s := (h %s F1 F2 ...).symm" % (g_rhs, g_rhs))
            lines.append("```")

    return "\n".join(lines)


def string_overlap(a, b):
    """Count common characters (rough structural similarity)."""
    from collections import Counter
    a = a.replace(' ', '')
    b = b.replace(' ', '')
    ca = Counter(a)
    cb = Counter(b)
    return sum(min(ca[c], cb[c]) for c in ca)


def compute_bfs_near_miss(eq1_text, eq2_text, eq1_vars, eq2_vars, max_states=5000, max_depth=3):
    """Run a quick BFS to find near-miss intermediate expressions.
    Returns a string with hints about partial chains found, or empty string."""
    import time
    from itertools import product as _prod

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return ""

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()

    h_lhs_tree = parse_op_tree(eq1_lhs)
    h_rhs_tree = parse_op_tree(eq1_rhs)
    gl_tree = parse_op_tree(eq2_lhs)
    gr_tree = parse_op_tree(eq2_rhs)
    h_vars_set = set(eq1_vars)

    def tree_norm(t):
        return tree_to_str(t).replace(' ', '')

    def _tree_size(t):
        if t[0] == 'var': return 1
        return 1 + _tree_size(t[1]) + _tree_size(t[2])

    def _subst_tree(tree, subst):
        if tree[0] == 'var':
            return parse_op_tree(subst[tree[1]]) if tree[1] in subst else tree
        return ('op', _subst_tree(tree[1], subst), _subst_tree(tree[2], subst))

    # Build fill terms
    fill = list(eq2_vars)
    for a in eq2_vars:
        for b in eq2_vars:
            t = f'{a} ◇ {b}'
            if t not in fill and len(fill) < 8:
                fill.append(t)

    MAX_SIZE = 15  # Keep small for speed

    def _all_completions(s):
        free = [v for v in eq1_vars if v not in s]
        if not free:
            return [dict(s)]
        if len(free) > 2:
            return []
        pool = eq2_vars if len(free) >= 2 else fill
        return [dict(s, **{v: val for v, val in zip(free, combo)})
                for combo in _prod(pool, repeat=len(free))]

    def _gen_rewrites(tree):
        results = []
        for pattern, repl, is_fwd in [(h_lhs_tree, h_rhs_tree, True),
                                       (h_rhs_tree, h_lhs_tree, False)]:
            s = unify_tree(pattern, tree, h_vars_set)
            if s is not None:
                for full_s in _all_completions(s):
                    r = _subst_tree(repl, full_s)
                    if _tree_size(r) <= MAX_SIZE:
                        args = ' '.join(full_s.get(v, '?') for v in eq1_vars)
                        results.append((r, args, is_fwd))
        if tree[0] == 'op':
            for sub_r, a, f in _gen_rewrites(tree[1]):
                full = ('op', sub_r, tree[2])
                if _tree_size(full) <= MAX_SIZE:
                    results.append((full, a, f))
            for sub_r, a, f in _gen_rewrites(tree[2]):
                full = ('op', tree[1], sub_r)
                if _tree_size(full) <= MAX_SIZE:
                    results.append((full, a, f))
        return results

    # BFS from both sides
    fwd_start = tree_norm(gl_tree)
    bwd_start = tree_norm(gr_tree)

    if fwd_start == bwd_start:
        return ""

    fwd_visited = {fwd_start: (None, None, None, 0)}  # norm -> (prev, args, is_fwd, depth)
    bwd_visited = {bwd_start: (None, None, None, 0)}
    fwd_frontier = [(gl_tree, fwd_start)]
    bwd_frontier = [(gr_tree, bwd_start)]

    t0 = time.time()
    total_states = 2

    for depth in range(max_depth):
        if time.time() - t0 > 2.0 or total_states > max_states:
            break

        # Expand forward
        fwd_next = []
        for tree, tnorm in fwd_frontier:
            if time.time() - t0 > 2.0:
                break
            for new_tree, args, is_fwd in _gen_rewrites(tree):
                nn = tree_norm(new_tree)
                if nn in fwd_visited:
                    continue
                fwd_visited[nn] = (tnorm, args, is_fwd, depth + 1)
                fwd_next.append((new_tree, nn))
                total_states += 1
                if nn in bwd_visited:
                    return ""  # Found! The main BFS should handle this
            if total_states > max_states:
                break
        fwd_frontier = fwd_next

        # Expand backward
        bwd_next = []
        for tree, tnorm in bwd_frontier:
            if time.time() - t0 > 2.0:
                break
            for new_tree, args, is_fwd in _gen_rewrites(tree):
                nn = tree_norm(new_tree)
                if nn in bwd_visited:
                    continue
                bwd_visited[nn] = (tnorm, args, is_fwd, depth + 1)
                bwd_next.append((new_tree, nn))
                total_states += 1
                if nn in fwd_visited:
                    return ""  # Found! The main BFS should handle this
            if total_states > max_states:
                break
        bwd_frontier = bwd_next

    # No direct path found. Report near-misses: expressions in fwd closest to bwd
    hints = []

    # Find fwd expressions closest to the goal RHS
    fwd_exprs = list(fwd_visited.keys())
    bwd_exprs = list(bwd_visited.keys())

    # Score by string overlap with the opposite target
    best_fwd = []
    for expr in fwd_exprs[:200]:
        score = string_overlap(expr, bwd_start)
        best_fwd.append((score, expr))
    best_fwd.sort(reverse=True)

    best_bwd = []
    for expr in bwd_exprs[:200]:
        score = string_overlap(expr, fwd_start)
        best_bwd.append((score, expr))
    best_bwd.sort(reverse=True)

    if best_fwd and best_fwd[0][0] > len(bwd_start) * 0.6:
        hints.append(f"From goal LHS, BFS reached expressions close to goal RHS:")
        for score, expr in best_fwd[:3]:
            # Reconstruct the chain
            chain = []
            cur = expr
            while fwd_visited[cur][0] is not None:
                prev, args, is_fwd, d = fwd_visited[cur]
                direction = "h" if is_fwd else "(h).symm"
                chain.append(f"  step: {direction} {args}")
                cur = prev
            chain.reverse()
            norm_expr = expr.replace('◇', ' ◇ ')
            hints.append(f"  Near-miss: {norm_expr}")
            for step in chain:
                hints.append(step)

    if best_bwd and best_bwd[0][0] > len(fwd_start) * 0.6:
        hints.append(f"From goal RHS, BFS reached expressions close to goal LHS:")
        for score, expr in best_bwd[:3]:
            chain = []
            cur = expr
            while bwd_visited[cur][0] is not None:
                prev, args, is_fwd, d = bwd_visited[cur]
                direction = "h" if is_fwd else "(h).symm"
                chain.append(f"  step: {direction} {args}")
                cur = prev
            chain.reverse()
            norm_expr = expr.replace('◇', ' ◇ ')
            hints.append(f"  Near-miss: {norm_expr}")
            for step in chain:
                hints.append(step)

    hints.append(f"BFS explored {len(fwd_visited)} forward + {len(bwd_visited)} backward states up to depth {max_depth}")
    return "\n".join(hints)


def try_direct_proof(problem, eq1_text, eq2_text):
    """Try to find and verify a direct proof via substitution search.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    hints = deep_proof_analysis(eq1_text, eq2_text)
    direct = [h for h in hints if "DIRECT PROOF FOUND" in h]
    eq2_vars = parse_variables(eq2_text)

    for hint in direct:
        # Extract proof from hint
        proof_match = re.search(r'exact (?:\(h .+?\)\.symm|h .+?)(?:\)|$)', hint)
        if not proof_match:
            continue
        proof_text = f"intro {' '.join(eq2_vars)}\n{proof_match.group(0)}"
        code = make_true_code(problem, proof_text)
        result = call_judge("true", code)
        if result.get("status") == "accepted":
            return True

    return False


def try_library_proof(problem):
    """Stage 2 judge is self-contained — the equational_theories library that
    backed this shortcut is no longer linked. Return False so the caller
    falls through to the LLM path without paying a guaranteed-failing Lean
    round-trip."""
    return False


# ── Transitive library proof ────────────────────────────────────

_IMPLICATION_GRAPH = None
_IMPORT_MAP = None

def _load_implication_graph():
    """Load the pre-computed implication graph and import map from data files."""
    global _IMPLICATION_GRAPH, _IMPORT_MAP
    if _IMPLICATION_GRAPH is not None:
        return
    import os
    base = os.path.dirname(os.path.abspath(__file__))
    # Prefer validated graph files (edges verified to exist in Lean library)
    graph_path = os.path.join(base, "implication_graph_validated.json")
    imports_path = os.path.join(base, "implication_imports_validated.json")
    if not os.path.exists(graph_path):
        graph_path = os.path.join(base, "implication_graph.json")
        imports_path = os.path.join(base, "implication_imports.json")
    try:
        with open(graph_path) as f:
            _IMPLICATION_GRAPH = json.load(f)
        with open(imports_path) as f:
            _IMPORT_MAP = json.load(f)
    except FileNotFoundError:
        _IMPLICATION_GRAPH = {}
        _IMPORT_MAP = {}


def _find_transitive_path(src_num, tgt_num, max_depth=6):
    """BFS to find shortest implication path from src_num to tgt_num.
    Returns list of equation numbers [src, ..., tgt] or None."""
    _load_implication_graph()
    graph = _IMPLICATION_GRAPH
    src_s = str(src_num)
    tgt_s = str(tgt_num)

    # Direct check
    if src_s in graph and tgt_num in graph[src_s]:
        return [src_num, tgt_num]

    from collections import deque
    queue = deque([(src_s, [src_num])])
    visited = {src_s}

    while queue:
        node, path = queue.popleft()
        if len(path) > max_depth:
            break
        for neighbor in graph.get(node, []):
            n_s = str(neighbor)
            if neighbor == tgt_num:
                return path + [tgt_num]
            if n_s not in visited:
                visited.add(n_s)
                queue.append((n_s, path + [neighbor]))
    return None


def try_transitive_library_proof(problem, max_judge_calls=2):
    """Stage 2 judge is self-contained — the equational_theories library the
    transitive chain composes against is no longer linked. Skip the whole
    path; no point constructing a proof whose `import` lines cannot resolve."""
    return False
    # Dead code below kept for reference; the early return above disables it.
    _load_implication_graph()
    src_num = problem['eq1_id']
    tgt_num = problem['eq2_id']

    path = _find_transitive_path(src_num, tgt_num)
    if not path or len(path) < 3:
        # Direct or no path — skip (direct already handled by try_library_proof)
        return False

    # Build the Lean proof: compose the intermediate implications
    imports = set()
    imports.add("equational_theories.Equations.All")

    # Collect import paths for each edge
    for i in range(len(path) - 1):
        key = f"{path[i]}_{path[i+1]}"
        imp = _IMPORT_MAP.get(key)
        if imp:
            imports.add(imp)

    # Build proof body
    # For a chain [A, B, C, D]: exact D_implies_E G (C_implies_D G (B_implies_C G (A_implies_B G h)))
    # Build inside-out
    proof_expr = "h"
    for i in range(len(path) - 1):
        theorem = f"Equation{path[i]}_implies_Equation{path[i+1]}"
        proof_expr = f"{theorem} G ({proof_expr})"

    import_lines = "\n".join(f"import {imp}" for imp in sorted(imports))
    code = (
        f"{import_lines}\n\n"
        f"theorem submission (G : Type*) [Magma G] "
        f"(h : {eq1_id} G) : {eq2_id} G := by\n"
        f"  exact {proof_expr}\n"
    )

    result = call_judge("true", code)
    if result.get("status") == "accepted":
        return True

    # If the exact approach fails (maybe wrong parenthesization), try with function application
    if max_judge_calls > 1 and len(path) <= 6:
        # Try alternative: use intermediate have steps
        lines = ["  intro x y z w u v".split()[:1+max(2, len(parse_variables(problem.get('equation2', ''))))]]
        have_steps = []
        for i in range(len(path) - 1):
            theorem = f"Equation{path[i]}_implies_Equation{path[i+1]}"
            if i == 0:
                have_steps.append(f"  have h{i+1} : Equation{path[i+1]} G := {theorem} G h")
            else:
                have_steps.append(f"  have h{i+1} : Equation{path[i+1]} G := {theorem} G h{i}")

        last_step = f"  exact h{len(path)-1}"

        code2 = (
            f"{import_lines}\n\n"
            f"theorem submission (G : Type*) [Magma G] "
            f"(h : {eq1_id} G) : {eq2_id} G := by\n"
            + "\n".join(have_steps) + "\n"
            + last_step + "\n"
        )
        result2 = call_judge("true", code2)
        if result2.get("status") == "accepted":
            return True

    return False


# ── Advanced proof strategies ───────────────────────────────────

def _detect_free_positions(eq_text, eq_vars):
    """Detect which variable positions in the hypothesis are 'free' — i.e.,
    the output is independent of that variable's value.
    Returns list of (position_index, variable_name) that are free on LHS or RHS."""
    parts = eq_text.split('=', 1)
    if len(parts) != 2:
        return [], []

    lhs = parts[0].strip()
    rhs = parts[1].strip()
    lhs_vars = set(re.findall(r'\b([a-z])\b', lhs))
    rhs_vars = set(re.findall(r'\b([a-z])\b', rhs))

    # Variables in RHS but not LHS → LHS is independent of them
    # Variables in LHS but not RHS → RHS is independent of them
    rhs_only = [(i, v) for i, v in enumerate(eq_vars) if v in rhs_vars and v not in lhs_vars]
    lhs_only = [(i, v) for i, v in enumerate(eq_vars) if v in lhs_vars and v not in rhs_vars]
    return lhs_only, rhs_only


def _build_independence_lemma(eq_text, eq_vars, free_pos_idx, free_var):
    """Given a free variable position, build a proof that the operation is
    independent of that argument position.

    If free_var is in RHS only, then varying it doesn't change LHS.
    So: h(x,...,a,...) and h(x,...,b,...) give same LHS,
    therefore the two RHS expressions are equal.

    Returns (lean_proof, lemma_statement) or None."""
    parts = eq_text.split('=', 1)
    if len(parts) != 2:
        return None
    lhs = parts[0].strip()
    rhs = parts[1].strip()

    # Build two instantiations differing only in the free position
    args_a = list(eq_vars)
    args_b = list(eq_vars)
    # Use 'a' and 'b' as the differing values, rename other vars if conflict
    used_vars = set(eq_vars)
    fresh = []
    for candidate in 'abcdefghijklmnopqrstuvwxyz':
        if candidate not in used_vars:
            fresh.append(candidate)
        if len(fresh) >= 2:
            break
    if len(fresh) < 2:
        return None

    args_a[free_pos_idx] = fresh[0]
    args_b[free_pos_idx] = fresh[1]

    # The lemma: (h args_a).symm.trans (h args_b) gives:
    # rhs[free_var → a] = rhs[free_var → b]
    rhs_a = re.sub(r'\b' + free_var + r'\b', fresh[0], rhs)
    rhs_b = re.sub(r'\b' + free_var + r'\b', fresh[1], rhs)

    return {
        'args_a': args_a,
        'args_b': args_b,
        'free_var': free_var,
        'free_pos': free_pos_idx,
        'fresh': fresh,
        'rhs_a': rhs_a,
        'rhs_b': rhs_b,
    }


def try_calc_chain_proof(problem, eq1_text, eq2_text, max_depth=5):
    """Try to find a calc-chain proof by BFS over rewriting steps.
    Each step applies h with some substitution, using the whole equation as a rewrite.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()
    g_lhs = eq2_lhs.replace(' ', '')
    g_rhs = eq2_rhs.replace(' ', '')

    # Pre-compute all useful h instantiations (with goal variables)
    all_insts = {}  # (lhs_norm, rhs_norm) -> args_string
    for combo in product(eq2_vars, repeat=len(eq1_vars)):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        nl = new_lhs.replace(' ', '')
        nr = new_rhs.replace(' ', '')
        if nl == nr:
            continue
        if nl not in all_insts:
            all_insts[nl] = {}
        all_insts[nl][nr] = ' '.join(combo)
        # Also store reverse direction
        if nr not in all_insts:
            all_insts[nr] = {}
        if nl not in all_insts[nr]:
            all_insts[nr][nl] = '(' + ' '.join(combo) + ').symm'

    # BFS from goal LHS to goal RHS
    # State: current normalized expression
    # Transition: apply any h-instantiation that matches current expression on LHS side
    visited = {g_lhs: (None, None)}  # expr -> (prev_expr, args_to_get_here)
    frontier = [g_lhs]

    for depth in range(max_depth):
        next_frontier = []
        for expr in frontier:
            if expr not in all_insts:
                continue
            for target, args in all_insts[expr].items():
                if target in visited:
                    continue
                visited[target] = (expr, args)
                if target == g_rhs:
                    # Found a path! Reconstruct it
                    path = []
                    cur = g_rhs
                    while visited[cur][0] is not None:
                        prev, a = visited[cur]
                        path.append((prev, cur, a))
                        cur = prev
                    path.reverse()

                    # Build calc proof
                    intro = f"intro {' '.join(eq2_vars)}"
                    calc_lines = [intro, "calc"]
                    for i, (frm, to, a) in enumerate(path):
                        # Recover the non-normalized form for the first line
                        if i == 0:
                            calc_lines.append(f"  _ = _ := by exact h {a}")
                        else:
                            if a.startswith('(') and a.endswith(').symm'):
                                real_args = a[1:-6]
                                calc_lines.append(f"  _ = _ := by exact (h {real_args}).symm")
                            else:
                                calc_lines.append(f"  _ = _ := by exact h {a}")

                    proof = '\n'.join(calc_lines)
                    code = make_true_code(problem, proof)
                    result = call_judge("true", code)
                    if result.get("status") == "accepted":
                        return True

                    # If the _ = _ style doesn't work, try with explicit terms
                    # (Lean may need help inferring the intermediate terms)
                    # Skip for now — will be handled by LLM if this fails

                next_frontier.append(target)
        frontier = next_frontier
        if not frontier:
            break

    return False


def try_compound_calc_proof(problem, eq1_text, eq2_text, max_judge_calls=3):
    """Try a calc-chain proof where h-arguments can be compound terms (e.g., x ◇ y).
    This extends try_calc_chain_proof by considering substitutions with terms
    built from goal variables, not just bare variables.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()
    g_lhs = eq2_lhs.replace(' ', '')
    g_rhs = eq2_rhs.replace(' ', '')

    # Generate compound terms from goal variables: bare vars + all pairwise (a ◇ b)
    bare_terms = list(eq2_vars)
    compound_only = []
    for a in eq2_vars:
        for b in eq2_vars:
            compound_only.append(f"({a} ◇ {b})")

    n_h = len(eq1_vars)  # number of h-arguments
    n_b = len(bare_terms)
    n_c = len(compound_only)

    # Build instantiations by iterating combos ordered by number of compound terms.
    # k=0: all bare (already handled by try_calc_chain_proof, skip)
    # k=1: exactly one compound argument position — n_h * n_c * n_b^(n_h-1)
    # k=2: exactly two compound positions — C(n_h,2) * n_c^2 * n_b^(n_h-2)
    all_insts = {}

    def _add_combo(combo):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        nl = new_lhs.replace(' ', '')
        nr = new_rhs.replace(' ', '')
        if nl == nr:
            return
        if nl not in all_insts:
            all_insts[nl] = {}
        all_insts[nl][nr] = ' '.join(combo)
        if nr not in all_insts:
            all_insts[nr] = {}
        if nl not in all_insts[nr]:
            all_insts[nr][nl] = '(' + ' '.join(combo) + ').symm'

    # k=1: one compound position, rest bare
    k1_count = n_h * n_c * (n_b ** max(n_h - 1, 0))
    if k1_count <= 200000:
        for pos in range(n_h):
            for ct in compound_only:
                for bare_combo in product(bare_terms, repeat=n_h - 1):
                    combo = list(bare_combo[:pos]) + [ct] + list(bare_combo[pos:])
                    _add_combo(combo)

    # k=2: two compound positions, rest bare (if h has >= 2 args)
    if n_h >= 2:
        k2_count = len(list(combinations(range(n_h), 2))) * (n_c ** 2) * (n_b ** max(n_h - 2, 0))
        if k2_count <= 200000:
            for pos1, pos2 in combinations(range(n_h), 2):
                for ct1 in compound_only:
                    for ct2 in compound_only:
                        for bare_combo in product(bare_terms, repeat=n_h - 2):
                            combo = list(bare_combo)
                            combo.insert(pos1, ct1)
                            combo.insert(pos2, ct2)
                            _add_combo(combo)

    # BFS from goal LHS to goal RHS (3-step max)
    visited = {g_lhs: (None, None)}
    frontier = [g_lhs]
    calls_used = 0

    for depth in range(3):
        next_frontier = []
        for expr in frontier:
            if expr not in all_insts:
                continue
            for target, args in all_insts[expr].items():
                if target in visited:
                    continue
                visited[target] = (expr, args)
                if target == g_rhs:
                    path = []
                    cur = g_rhs
                    while visited[cur][0] is not None:
                        prev, a = visited[cur]
                        path.append((prev, cur, a))
                        cur = prev
                    path.reverse()

                    intro = f"intro {' '.join(eq2_vars)}"
                    calc_lines = [intro, "calc"]
                    for i, (frm, to, a) in enumerate(path):
                        if a.startswith('(') and a.endswith(').symm'):
                            real_args = a[1:-6]
                            calc_lines.append(f"  _ = _ := by exact (h {real_args}).symm")
                        else:
                            calc_lines.append(f"  _ = _ := by exact h {a}")

                    proof = '\n'.join(calc_lines)
                    code = make_true_code(problem, proof)
                    result = call_judge("true", code)
                    calls_used += 1
                    if result.get("status") == "accepted":
                        return True
                    if calls_used >= max_judge_calls:
                        return False

                next_frontier.append(target)
        frontier = next_frontier
        if not frontier:
            break

    return False


def try_rw_chain_proof(problem, eq1_text, eq2_text, max_judge_calls=6):
    """Try a proof using rw tactics instead of calc chains.
    Sometimes Lean's unifier works better with rw [h args] patterns.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    intro = f"intro {' '.join(eq2_vars)}"

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()

    # Collect candidate combos — prioritize by structural relevance
    scored_combos = []
    for combo in product(eq2_vars, repeat=len(eq1_vars)):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        nl = new_lhs.replace(' ', '')
        nr = new_rhs.replace(' ', '')
        if nl == nr:
            continue
        # Score: how many characters overlap with the goal equation
        score = (string_overlap(nl, eq2_lhs.replace(' ', '')) +
                 string_overlap(nr, eq2_rhs.replace(' ', '')))
        scored_combos.append((score, combo))
    scored_combos.sort(reverse=True)

    # Strategy 1: Single rw step with best combos (uses 2 judge calls max)
    proofs_to_try = []
    seen = set()
    for _, combo in scored_combos[:3]:
        args = ' '.join(combo)
        p1 = f"{intro}\nrw [h {args}]"
        p2 = f"{intro}\nrw [← h {args}]"
        if p1 not in seen:
            proofs_to_try.append(p1)
            seen.add(p1)
        if p2 not in seen:
            proofs_to_try.append(p2)
            seen.add(p2)

    # Strategy 2: Two rw steps with the top 4 combos (limited)
    top_combos = [c for _, c in scored_combos[:4]]
    for i, c1 in enumerate(top_combos):
        for c2 in top_combos:
            a1 = ' '.join(c1)
            a2 = ' '.join(c2)
            for p in [
                f"{intro}\nrw [h {a1}]\nrw [h {a2}]",
                f"{intro}\nrw [← h {a1}]\nrw [h {a2}]",
                f"{intro}\nrw [h {a1}]\nrw [← h {a2}]",
            ]:
                if p not in seen:
                    proofs_to_try.append(p)
                    seen.add(p)

    # Submit limited candidates
    calls = 0
    for proof in proofs_to_try:
        if calls >= max_judge_calls:
            break
        code = make_true_code(problem, proof)
        result = call_judge("true", code)
        calls += 1
        if result.get("status") == "accepted":
            return True

    return False


def try_congr_arg_proof(problem, eq1_text, eq2_text, max_judge_calls=3):
    """Try proofs using congr_arg to apply an equation to sub-expressions.

    Pattern 1 (iterated): If eq1 is single-variable `a ◇ a = f(a)` and eq2 is
    the iterated version `a ◇ a = f(f(a))`, prove by chaining h(x) with congr_arg.

    Pattern 2 (constant bridge): From eq1 derive that (a◇a)◇b is constant in b,
    and (c◇a)◇c = f(a) for all c; bridge through c = x◇x to show f is constant.

    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    intro = f"intro {' '.join(eq2_vars)}"
    calls = 0

    # ── Pattern 1: Single-variable iterated congr_arg ──
    if len(eq1_vars) == 1 and len(eq2_vars) == 1:
        v = eq2_vars[0]
        # Try: exact (h x).trans (congr_arg (· ◇ x) (h x))
        proof = f"{intro}\nexact (h {v}).trans (congr_arg (\u00b7 \u25c7 {v}) (h {v}))"
        code = make_true_code(problem, proof)
        result = call_judge("true", code)
        calls += 1
        if result.get("status") == "accepted":
            return True
        if calls >= max_judge_calls:
            return False

        # Try simp-based rewriting
        for direction in ["\u2190 ", ""]:
            proof = f"{intro}\nsimp only [{direction}h {v}]"
            code = make_true_code(problem, proof)
            result = call_judge("true", code)
            calls += 1
            if result.get("status") == "accepted":
                return True
            if calls >= max_judge_calls:
                return False

    # ── Pattern 2: Constant bridge (3-var hypothesis → 3 or 4-var goal) ──
    if len(eq1_vars) == 3 and len(eq2_vars) in (3, 4):
        gv = eq2_vars
        proofs = _build_bridge_proofs(eq1_vars, gv, intro)
        for proof in proofs:
            if calls >= max_judge_calls:
                break
            code = make_true_code(problem, proof)
            result = call_judge("true", code)
            calls += 1
            if result.get("status") == "accepted":
                return True

    return False


def _build_bridge_proofs(eq1_vars, goal_vars, intro):
    """Generate constant-bridge proof candidates for 3-var hypothesis."""
    proofs = []
    v = eq1_vars

    # For 3-var hypothesis with structure (a◇a)◇b = (c◇a)◇c:
    # hconst = h a b a  (3rd arg = 1st)  → constancy
    # hcomm  = (h a a c).symm  (2nd arg = 1st) → pivot
    # Bridge: step through c = x◇x

    # Try the canonical permutation (matching the structure of Equation4616)
    const_args = "a b a"
    comm_args = "a a c"

    if len(goal_vars) == 4:
        gx, gy, gz, gw = goal_vars
        proof = (
            f"{intro}\n"
            f"have hconst : \u2200 (a b : G), (a \u25c7 a) \u25c7 b = (a \u25c7 a) \u25c7 a := "
            f"fun a b => h {const_args}\n"
            f"have hcomm : \u2200 (a c : G), (c \u25c7 a) \u25c7 c = (a \u25c7 a) \u25c7 a := "
            f"fun a c => (h {comm_args}).symm\n"
            f"have step1 := hcomm {gx} ({gx} \u25c7 {gx})\n"
            f"have step2 := hcomm {gz} ({gx} \u25c7 {gx})\n"
            f"have step3 := congr_arg (\u00b7 \u25c7 ({gx} \u25c7 {gx})) (hconst {gx} {gz})\n"
            f"calc ({gx} \u25c7 {gx}) \u25c7 {gy}\n"
            f"    = ({gx} \u25c7 {gx}) \u25c7 {gx} := hconst {gx} {gy}\n"
            f"  _ = (({gx} \u25c7 {gx}) \u25c7 {gx}) \u25c7 ({gx} \u25c7 {gx}) := step1.symm\n"
            f"  _ = (({gx} \u25c7 {gx}) \u25c7 {gz}) \u25c7 ({gx} \u25c7 {gx}) := step3.symm\n"
            f"  _ = ({gz} \u25c7 {gz}) \u25c7 {gz} := step2\n"
            f"  _ = ({gz} \u25c7 {gz}) \u25c7 {gw} := (hconst {gz} {gw}).symm"
        )
        proofs.append(proof)

    if len(goal_vars) == 3:
        gx, gy, gz = goal_vars
        proof = (
            f"{intro}\n"
            f"have hconst : \u2200 (a b : G), (a \u25c7 a) \u25c7 b = (a \u25c7 a) \u25c7 a := "
            f"fun a b => h {const_args}\n"
            f"have hcomm : \u2200 (a c : G), (c \u25c7 a) \u25c7 c = (a \u25c7 a) \u25c7 a := "
            f"fun a c => (h {comm_args}).symm\n"
            f"have step1 := hcomm {gx} ({gx} \u25c7 {gx})\n"
            f"have step2 := hcomm {gz} ({gx} \u25c7 {gx})\n"
            f"have step3 := congr_arg (\u00b7 \u25c7 ({gx} \u25c7 {gx})) (hconst {gx} {gz})\n"
            f"calc ({gx} \u25c7 {gx}) \u25c7 {gy}\n"
            f"    = ({gx} \u25c7 {gx}) \u25c7 {gx} := hconst {gx} {gy}\n"
            f"  _ = (({gx} \u25c7 {gx}) \u25c7 {gx}) \u25c7 ({gx} \u25c7 {gx}) := step1.symm\n"
            f"  _ = (({gx} \u25c7 {gx}) \u25c7 {gz}) \u25c7 ({gx} \u25c7 {gx}) := step3.symm\n"
            f"  _ = ({gz} \u25c7 {gz}) \u25c7 {gz} := step2\n"
            f"  _ = ({gz} \u25c7 {gz}) \u25c7 {gy} := (hconst {gz} {gy}).symm"
        )
        proofs.append(proof)

    return proofs


def try_simp_proof(problem, eq1_text, eq2_text, max_judge_calls=2):
    """Try proofs using simp only [h] and simp only [← h].
    This is a powerful general strategy — Lean's simplifier can often
    close goals that involve repeated application of the hypothesis.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq2_vars = parse_variables(eq2_text)
    intro = f"intro {' '.join(eq2_vars)}"
    calls = 0

    for direction in ["", "← "]:
        if calls >= max_judge_calls:
            break
        proof = f"{intro}\nsimp only [{direction}h]"
        code = make_true_code(problem, proof)
        result = call_judge("true", code)
        calls += 1
        if result.get("status") == "accepted":
            return True

    return False


def try_simp_with_constancy(problem, eq1_text, eq2_text, max_judge_calls=2):
    """Try simp only [h, hconst, ...] after deriving constancy lemmas.
    The simplifier can handle deeper rewriting chains when given both
    the hypothesis and derived constancy lemmas.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    constancy_info, lhs_only, rhs_only = build_constancy_info(eq1_text, eq1_vars, eq2_vars)
    if not constancy_info:
        return False

    intro = f"intro {' '.join(eq2_vars)}"
    calls = 0

    # Build have lines for all constancy lemmas
    ci_have_lines = []
    ci_names = []
    for i, ci in enumerate(constancy_info):
        name = "hconst" if i == 0 else f"hconst{i+1}"
        line = ci['have_line']
        if i > 0:
            line = line.replace('hconst', name, 1)
        ci_have_lines.append(line)
        ci_names.append(name)

    have_block = "\n".join(ci_have_lines)
    simp_names = ", ".join(ci_names)

    # Try various simp combinations
    simp_variants = [
        f"simp only [h, {simp_names}]",
        f"simp only [\u2190 h, {simp_names}]",
        f"simp only [{simp_names}, h]",
        f"simp only [{simp_names}, \u2190 h]",
    ]

    for simp_tactic in simp_variants:
        if calls >= max_judge_calls:
            break
        proof = f"{intro}\n{have_block}\n{simp_tactic}"
        code = make_true_code(problem, proof)
        result = call_judge("true", code)
        calls += 1
        if result.get("status") == "accepted":
            return True

    return False


def try_rw_simp_proof(problem, eq1_text, eq2_text, max_judge_calls=2):
    """Try rw [h args] followed by simp only [h] or simp only [← h].
    One strategic rewrite can transform the goal into something simp can close.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    intro = f"intro {' '.join(eq2_vars)}"

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()

    # Find combos where h-instantiation touches the goal
    scored_combos = []
    for combo in product(eq2_vars, repeat=len(eq1_vars)):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        nl = new_lhs.replace(' ', '')
        nr = new_rhs.replace(' ', '')
        if nl == nr:
            continue
        g_lhs = eq2_lhs.replace(' ', '')
        g_rhs = eq2_rhs.replace(' ', '')
        score = (string_overlap(nl, g_lhs) + string_overlap(nr, g_rhs) +
                 string_overlap(nl, g_rhs) + string_overlap(nr, g_lhs))
        scored_combos.append((score, combo))
    scored_combos.sort(reverse=True)

    calls = 0
    tried = set()
    for _, combo in scored_combos[:4]:
        args = ' '.join(combo)
        for rw_dir in ["", "\u2190 "]:
            for simp_dir in ["", "\u2190 "]:
                proof = f"{intro}\nrw [{rw_dir}h {args}]\nsimp only [{simp_dir}h]"
                if proof in tried:
                    continue
                tried.add(proof)
                if calls >= max_judge_calls:
                    return False
                code = make_true_code(problem, proof)
                result = call_judge("true", code)
                calls += 1
                if result.get("status") == "accepted":
                    return True

    return False


def try_specialized_simp(problem, eq1_text, eq2_text, max_judge_calls=2):
    """Try simp with a specialized version of the hypothesis.
    When the hypothesis LHS is a single variable x, derive h_spec by
    substituting all other variables to x: x = f(x, x, ..., x).
    Then simp only [h_spec] can handle goals by repeated rewriting.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    if len(parts1) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()

    # Only handle single-variable LHS
    if not re.match(r'^[a-z]$', eq1_lhs):
        return False

    lhs_var = eq1_lhs
    lhs_vars = set(re.findall(r'\b([a-z])\b', eq1_lhs))
    rhs_vars = set(re.findall(r'\b([a-z])\b', eq1_rhs))

    # Need at least one free variable
    if not (rhs_vars - lhs_vars):
        return False

    # Build h_spec args: map all vars to the LHS variable
    spec_args = ' '.join([lhs_var] * len(eq1_vars))
    # Build the specialized RHS
    spec_rhs = eq1_rhs
    for v in eq1_vars:
        if v != lhs_var:
            spec_rhs = re.sub(r'\b' + v + r'\b', lhs_var, spec_rhs)

    # Skip if specialized RHS is trivially the same as LHS
    if spec_rhs.replace(' ', '') == lhs_var:
        return False

    intro = f"intro {' '.join(eq2_vars)}"
    have_line = (
        f"have h_spec : \u2200 ({lhs_var} : G), "
        f"{lhs_var} = {spec_rhs} := fun {lhs_var} => h {spec_args}"
    )

    calls = 0
    for direction in ["", "\u2190 "]:
        if calls >= max_judge_calls:
            break
        proof = f"{intro}\n{have_line}\nsimp only [{direction}h_spec]"
        code = make_true_code(problem, proof)
        result = call_judge("true", code)
        calls += 1
        if result.get("status") == "accepted":
            return True

    return False


def try_have_chain_proof(problem, eq1_text, eq2_text, max_judge_calls=3):
    """Try proofs using `have` lemmas with independence/constancy arguments.

    When a hypothesis has free variables (appearing on only one side),
    we can derive constancy lemmas and use them to close the goal.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    intro = f"intro {' '.join(eq2_vars)}"
    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()

    lhs_only, rhs_only = _detect_free_positions(eq1_text, eq1_vars)
    if not lhs_only and not rhs_only:
        return False

    calls = 0

    # If there are variables only on RHS of hypothesis:
    # Then LHS is constant w.r.t. those variables.
    # This means: for any instantiation of non-free vars, the LHS value is fixed
    # regardless of the free variable.
    # Proof technique: (h args_a).symm.trans (h args_b) gives rhs_a = rhs_b
    for pos, fvar in rhs_only:
        info = _build_independence_lemma(eq1_text, eq1_vars, pos, fvar)
        if not info:
            continue

        # Build a constancy have-lemma
        fresh_a, fresh_b = info['fresh']
        other_vars = [v for i, v in enumerate(eq1_vars) if i != pos]
        quant_vars = other_vars + [fresh_a, fresh_b]

        args_a_str = ' '.join(info['args_a'])
        args_b_str = ' '.join(info['args_b'])

        # have hconst : ∀ (other_vars a b : G), rhs_a = rhs_b
        lemma_proof = f"(h {args_a_str}).symm.trans (h {args_b_str})"
        have_line = (
            f"have hconst : ∀ ({' '.join(quant_vars)} : G), "
            f"{info['rhs_a']} = {info['rhs_b']} := "
            f"fun {' '.join(quant_vars)} => {lemma_proof}"
        )

        # Try: intro; have hconst; exact hconst args
        # The args to hconst should match the goal variables
        for combo in product(eq2_vars, repeat=len(quant_vars)):
            if calls >= max_judge_calls:
                return False
            args = ' '.join(combo)
            proof = f"{intro}\n{have_line}\nexact hconst {args}"
            code = make_true_code(problem, proof)
            result = call_judge("true", code)
            calls += 1
            if result.get("status") == "accepted":
                return True
            break  # Only try the most natural combo

    # Similarly for variables only on LHS
    for pos, fvar in lhs_only:
        info = _build_independence_lemma(eq1_text, eq1_vars, pos, fvar)
        if not info:
            continue

        fresh_a, fresh_b = info['fresh']
        other_vars = [v for i, v in enumerate(eq1_vars) if i != pos]
        quant_vars = other_vars + [fresh_a, fresh_b]

        args_a_str = ' '.join(info['args_a'])
        args_b_str = ' '.join(info['args_b'])

        # When fvar is LHS-only: varying it doesn't change RHS
        # So h(args_a) gives lhs_a = rhs, h(args_b) gives lhs_b = rhs
        # Therefore (h args_a).trans (h args_b).symm gives lhs_a = lhs_b
        lhs_a = re.sub(r'\b' + fvar + r'\b', fresh_a, eq1_lhs)
        lhs_b = re.sub(r'\b' + fvar + r'\b', fresh_b, eq1_lhs)

        lemma_proof = f"(h {args_a_str}).trans (h {args_b_str}).symm"
        have_line = (
            f"have hconst : ∀ ({' '.join(quant_vars)} : G), "
            f"{lhs_a} = {lhs_b} := "
            f"fun {' '.join(quant_vars)} => {lemma_proof}"
        )

        for combo in product(eq2_vars, repeat=len(quant_vars)):
            if calls >= max_judge_calls:
                return False
            args = ' '.join(combo)
            proof = f"{intro}\n{have_line}\nexact hconst {args}"
            code = make_true_code(problem, proof)
            result = call_judge("true", code)
            calls += 1
            if result.get("status") == "accepted":
                return True
            break

    return False


def try_constant_proof(problem, eq1_text, eq2_text, max_judge_calls=4):
    """Try proofs for equations where the hypothesis makes some terms constant.

    When some variables appear only on one side of the hypothesis, the other
    side is constant w.r.t. those variables. We can use this to find
    2-step trans proofs through the constant value using compound arguments.

    Example: x ◇ y = (z ◇ z) ◇ z → both x◇y and (z◇z)◇z equal a constant.
    Any expression built from ◇ can be plugged in for x,y,z.

    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()

    lhs_vars = set(re.findall(r'\b([a-z])\b', eq1_lhs))
    rhs_vars = set(re.findall(r'\b([a-z])\b', eq1_rhs))

    intro = f"intro {' '.join(eq2_vars)}"
    calls = 0

    lhs_only = lhs_vars - rhs_vars
    rhs_only = rhs_vars - lhs_vars

    if not lhs_only and not rhs_only:
        return False

    # Build compound terms from goal variables (depth 0, 1, 2)
    terms = list(eq2_vars)
    for a in eq2_vars:
        for b in eq2_vars:
            terms.append(f"({a} \u25c7 {b})")
    if len(eq2_vars) <= 5:
        for a in eq2_vars:
            for b in eq2_vars:
                for c in eq2_vars:
                    terms.append(f"(({a} \u25c7 {b}) \u25c7 {c})")
                    terms.append(f"({a} \u25c7 ({b} \u25c7 {c}))")

    g_lhs = eq2_lhs.replace(' ', '')
    g_rhs = eq2_rhs.replace(' ', '')

    # Find h-instantiations matching each side of eq2 via unification
    def _unify_expr(template_str, target_str, tvars):
        """Try to find a substitution of tvars that makes template match target.
        Returns dict mapping var -> Lean expression, or None."""
        # Parse both into tree form
        def _parse(s):
            s = s.strip()
            while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
                depth = 0; matched = True
                for i, c in enumerate(s):
                    if c == '(': depth += 1
                    elif c == ')': depth -= 1
                    if depth == 0 and i < len(s) - 1: matched = False; break
                if matched: s = s[1:-1].strip()
                else: break
            # Find outermost ◇
            depth = 0; last_op = -1
            for i, c in enumerate(s):
                if c == '(': depth += 1
                elif c == ')': depth -= 1
                elif (c == '\u25c7' or c == '*') and depth == 0: last_op = i
            if last_op >= 0:
                return ('op', _parse(s[:last_op]), _parse(s[last_op+1:]))
            return ('var', s.strip())

        def _match(tpl, tgt, subst):
            if tpl[0] == 'var' and tpl[1] in tvars:
                v = tpl[1]
                # Reconstruct target as string
                tgt_str = _tree_to_str(tgt)
                if v in subst:
                    return subst[v] == tgt_str
                subst[v] = tgt_str
                return True
            if tpl[0] == 'var' and tgt[0] == 'var':
                return tpl[1] == tgt[1]
            if tpl[0] == 'op' and tgt[0] == 'op':
                s = dict(subst)
                if _match(tpl[1], tgt[1], s) and _match(tpl[2], tgt[2], s):
                    subst.update(s)
                    return True
            return False

        def _tree_to_str(t):
            if t[0] == 'var':
                return t[1]
            return f"({_tree_to_str(t[1])} \u25c7 {_tree_to_str(t[2])})"

        tpl_tree = _parse(template_str)
        tgt_tree = _parse(target_str)
        subst = {}
        if _match(tpl_tree, tgt_tree, subst):
            return subst
        return None

    tvar_set = set(eq1_vars)

    def _unify_and_format(template, target):
        """Unify template with target and return Lean args string, or None.
        For free variables not in the template, fill with the first goal var."""
        subst = _unify_expr(template, target, tvar_set)
        if subst is None:
            return None
        # Fill unbound vars (free variables) with the first available goal var
        default_fill = eq2_vars[0] if eq2_vars else 'x'
        for v in eq1_vars:
            if v not in subst:
                subst[v] = default_fill
        return ' '.join(subst[v] for v in eq1_vars)

    lhs_match_gl = _unify_and_format(eq1_lhs, eq2_lhs)
    lhs_match_gr = _unify_and_format(eq1_lhs, eq2_rhs)
    rhs_match_gl = _unify_and_format(eq1_rhs, eq2_lhs)
    rhs_match_gr = _unify_and_format(eq1_rhs, eq2_rhs)

    # Try various 2-step chains through the constant
    candidates = []
    # h(a1) : gl = rhs_const, h(a2) : gr = rhs_const → gl = rhs_const = gr
    if lhs_match_gl and lhs_match_gr:
        candidates.append(f"{intro}\nexact (h {lhs_match_gl}).trans (h {lhs_match_gr}).symm")
    # (h a1).symm : lhs_const = gl, (h a2).symm : lhs_const = gr
    if rhs_match_gl and rhs_match_gr:
        candidates.append(f"{intro}\nexact (h {rhs_match_gl}).symm.trans (h {rhs_match_gr}).symm")
    # h(a1) : gl = rhs_c, (h a2) : lhs_c = gr, need rhs_c = lhs_c
    if lhs_match_gl and rhs_match_gr:
        candidates.append(f"{intro}\nexact (h {lhs_match_gl}).trans (h {rhs_match_gr})")
    if rhs_match_gl and lhs_match_gr:
        candidates.append(f"{intro}\nexact (h {rhs_match_gl}).symm.trans (h {lhs_match_gr}).symm")

    for proof in candidates:
        if calls >= max_judge_calls:
            break
        code = make_true_code(problem, proof)
        result = call_judge("true", code)
        calls += 1
        if result.get("status") == "accepted":
            return True

    # Try congruence-based approach:
    # If goal is f(a) = f(b) for some common structure f, prove a = b first
    # using the constant-value property, then apply congr_arg.
    if calls < max_judge_calls:
        # Check if goal sides share common outer structure
        def _parse_tree(s):
            s = s.strip()
            while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
                depth = 0; matched = True
                for i, c in enumerate(s):
                    if c == '(': depth += 1
                    elif c == ')': depth -= 1
                    if depth == 0 and i < len(s) - 1: matched = False; break
                if matched: s = s[1:-1].strip()
                else: break
            depth = 0; last_op = -1
            for i, c in enumerate(s):
                if c == '(': depth += 1
                elif c == ')': depth -= 1
                elif (c == '\u25c7' or c == '*') and depth == 0: last_op = i
            if last_op >= 0:
                return ('op', _parse_tree(s[:last_op]), _parse_tree(s[last_op+1:]))
            return ('var', s.strip())

        def _tree_str(t):
            if t[0] == 'var': return t[1]
            return f"({_tree_str(t[1])} \u25c7 {_tree_str(t[2])})"

        gl = _parse_tree(eq2_lhs)
        gr = _parse_tree(eq2_rhs)

        # Check: both are op and share left or right subtree
        if gl[0] == 'op' and gr[0] == 'op':
            gl_left, gl_right = _tree_str(gl[1]), _tree_str(gl[2])
            gr_left, gr_right = _tree_str(gr[1]), _tree_str(gr[2])

            # Same left side: x ◇ a = x ◇ b → need a = b
            if gl_left == gr_left and gl_right != gr_right:
                inner_a = gl_right
                inner_b = gr_right
                # Try to prove inner_a = inner_b via h trans
                inner_lhs_a = _unify_and_format(eq1_lhs, inner_a)
                inner_lhs_b = _unify_and_format(eq1_lhs, inner_b)
                if inner_lhs_a and inner_lhs_b:
                    proof = (
                        f"{intro}\n"
                        f"exact congr_arg ({gl_left} \u25c7 \u00b7) ((h {inner_lhs_a}).trans (h {inner_lhs_b}).symm)"
                    )
                    if calls < max_judge_calls:
                        code = make_true_code(problem, proof)
                        result = call_judge("true", code)
                        calls += 1
                        if result.get("status") == "accepted":
                            return True

                inner_rhs_a = _unify_and_format(eq1_rhs, inner_a)
                inner_rhs_b = _unify_and_format(eq1_rhs, inner_b)
                if inner_rhs_a and inner_rhs_b:
                    proof = (
                        f"{intro}\n"
                        f"exact congr_arg ({gl_left} \u25c7 \u00b7) ((h {inner_rhs_a}).symm.trans (h {inner_rhs_b}).symm)"
                    )
                    if calls < max_judge_calls:
                        code = make_true_code(problem, proof)
                        result = call_judge("true", code)
                        calls += 1
                        if result.get("status") == "accepted":
                            return True

            # Same right side: a ◇ x = b ◇ x → need a = b
            if gl_right == gr_right and gl_left != gr_left:
                inner_a = gl_left
                inner_b = gr_left
                inner_lhs_a = _unify_and_format(eq1_lhs, inner_a)
                inner_lhs_b = _unify_and_format(eq1_lhs, inner_b)
                if inner_lhs_a and inner_lhs_b:
                    proof = (
                        f"{intro}\n"
                        f"exact congr_arg (\u00b7 \u25c7 {gl_right}) ((h {inner_lhs_a}).trans (h {inner_lhs_b}).symm)"
                    )
                    if calls < max_judge_calls:
                        code = make_true_code(problem, proof)
                        result = call_judge("true", code)
                        calls += 1
                        if result.get("status") == "accepted":
                            return True

                inner_rhs_a = _unify_and_format(eq1_rhs, inner_a)
                inner_rhs_b = _unify_and_format(eq1_rhs, inner_b)
                if inner_rhs_a and inner_rhs_b:
                    proof = (
                        f"{intro}\n"
                        f"exact congr_arg (\u00b7 \u25c7 {gl_right}) ((h {inner_rhs_a}).symm.trans (h {inner_rhs_b}).symm)"
                    )
                    if calls < max_judge_calls:
                        code = make_true_code(problem, proof)
                        result = call_judge("true", code)
                        calls += 1
                        if result.get("status") == "accepted":
                            return True

    return False


def try_deep_constancy_proof(problem, eq1_text, eq2_text, max_judge_calls=3):
    """Try proofs by deriving reduction lemmas via h(compound) + rw [(h ...).symm].

    For hypotheses of the form x = f(x, y_free, z_free), this:
    1. Applies h to compound subterms along the spine of the RHS
    2. Uses rw [(h args).symm] to simplify inner occurrences
    3. Derives a reduction lemma, then uses it + constancy to close the goal

    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    intro = f"intro {' '.join(eq2_vars)}"
    calls = 0

    # Only works when LHS is a single variable (x = f(x, y, z) form)
    if not re.match(r'^[a-z]$', eq1_lhs):
        return False

    lhs_var = eq1_lhs
    rhs_vars = set(re.findall(r'\b([a-z])\b', eq1_rhs))
    free_vars = sorted(rhs_vars - {lhs_var})
    if not free_vars:
        return False

    rhs_tree = parse_op_tree(eq1_rhs)
    if rhs_tree[0] != 'op':
        return False

    # Find the spine: path from root to the first occurrence of lhs_var
    def find_spine(tree, var, prefix=''):
        if tree[0] == 'var':
            return [(prefix, tree)] if tree[1] == var else None
        if tree[0] != 'op':
            return None
        lp = find_spine(tree[1], var, prefix + 'L')
        if lp is not None:
            return [(prefix, tree)] + lp
        rp = find_spine(tree[2], var, prefix + 'R')
        if rp is not None:
            return [(prefix, tree)] + rp
        return None

    spine = find_spine(rhs_tree, lhs_var)
    if not spine or len(spine) < 3:
        return False

    # spine[0] = (root, full_rhs_tree), spine[-1] = (leaf_path, var_node)
    # Intermediate nodes spine[1...-1] are compound subterms containing lhs_var

    # Strategy: for each intermediate spine node, try:
    # have lem1 := h <spine_node> <free_args>  -- gives spine_node = f(spine_node, ...)
    # Then rw [(h <args>).symm] at lem1  -- simplifies inner f(...) to x
    # This produces a "reduction lemma" that simplifies the spine node.
    # Then use this + constancy to build a deeper constancy, closing the goal.

    # Build free-var argument lists for h calls
    h_arity = len(eq1_vars)
    bound_pos = eq1_vars.index(lhs_var) if lhs_var in eq1_vars else 0

    # For each spine subtree (skip leaf x and full RHS):
    for si in range(1, len(spine) - 1):
        _, subtree = spine[si]
        st_str = tree_to_str(subtree)

        # Build h(<subtree>, free_args):
        # Replace lhs_var with st_str, keep free vars as fresh names
        h_args = []
        for vi, v in enumerate(eq1_vars):
            if v == lhs_var:
                h_args.append(f"({st_str})")
            else:
                h_args.append(v)
        h_compound = ' '.join(h_args)

        # Build (h <original_vars>).symm for the inner rw
        h_inner = ' '.join(eq1_vars)

        # Proof template: derive lem1 via h(compound) + rw [h.symm], then use lem1
        # Pattern: have lem1 := ...; then try various closures
        lem1_have = (
            f"have lem1 : ∀ ({' '.join(eq1_vars)} : G), _ := by\n"
            f"    intro {' '.join(eq1_vars)}\n"
            f"    have h1 := h {h_compound}\n"
            f"    rw [(h {h_inner}).symm] at h1\n"
            f"    exact h1"
        )

        # Try: intro vars; lem1; then derive deeper constancy and close
        # Build constancy from lem1 + h
        constancy_info, _, rhs_only = build_constancy_info(eq1_text, eq1_vars, eq2_vars)
        ci_block = ""
        ci_names = []
        if constancy_info:
            for i, ci in enumerate(constancy_info):
                name = "hconst" if i == 0 else f"hconst{i+1}"
                line = ci['have_line']
                if i > 0:
                    line = line.replace('hconst', name, 1)
                ci_block += line + "\n"
                ci_names.append(name)

        # Try several closure strategies with lem1 + constancy
        proofs = []

        # Closure 1: lem1 + constancy + simp
        if ci_names:
            simp_args = ", ".join(ci_names)
            proofs.append(
                f"{intro}\n{ci_block}{lem1_have}\n"
                f"simp only [lem1, h, {simp_args}]"
            )
            proofs.append(
                f"{intro}\n{ci_block}{lem1_have}\n"
                f"simp only [← lem1, h, {simp_args}]"
            )

        # Closure 2: just lem1 + h with simp
        proofs.append(
            f"{intro}\n{lem1_have}\n"
            f"simp only [lem1, h]"
        )
        proofs.append(
            f"{intro}\n{lem1_have}\n"
            f"simp only [← lem1, ← h]"
        )

        for proof in proofs:
            if calls >= max_judge_calls:
                return False
            code = make_true_code(problem, proof)
            result = call_judge("true", code)
            calls += 1
            if result.get("status") == "accepted":
                return True

    return False


def try_simp_rewrite_proof(problem, eq1_text, eq2_text, max_judge_calls=8):
    """Try proofs using Lean's simp tactic with derived rewrite lemmas.

    For self-referential hypotheses (x = F(x, free_vars)), derives:
    1. hconst: constancy lemma(s) for each free variable
    2. h.symm as backward rewrite: F(x,y,z) → x (collapsing)
    3. Compound constancy: h applied to compound terms + constancy

    Key insight: ← h (backward) collapses pattern matches. h (forward) expands
    but diverges since LHS matches everything. So we use:
    - ← h for normalization (shrinking)
    - hconst for equating different free var instantiations
    - Specific rw steps for targeted expansions

    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()

    lhs_vars = set(re.findall(r'\b([a-z])\b', eq1_lhs))
    rhs_vars = set(re.findall(r'\b([a-z])\b', eq1_rhs))
    rhs_only = sorted(rhs_vars - lhs_vars)
    lhs_only = sorted(lhs_vars - rhs_vars)

    if not rhs_only and not lhs_only:
        return False  # No free vars, constancy doesn't apply

    intro = f"intro {' '.join(eq2_vars)}"
    calls = 0

    # Build constancy lemmas
    constancy_info, _, _ = build_constancy_info(eq1_text, eq1_vars, eq2_vars)
    ci_block = ""
    ci_names = []
    for i, ci in enumerate(constancy_info):
        name = "hc" if i == 0 else f"hc{i+1}"
        line = ci['have_line']
        if i > 0:
            line = line.replace('hconst', name, 1)
        else:
            line = line.replace('hconst', name, 1)
        ci_block += line + "\n"
        ci_names.append(name)

    if not ci_names:
        return False

    proofs = []

    # Strategy 1: simp [← h, hc] — backward collapse + constancy
    # ← h: F(x,y,z) → x (collapse pattern to core var)
    # hc: equate different free var instantiations
    simp_bwd = ", ".join(["← h"] + ci_names)
    proofs.append(f"{intro}\n{ci_block}simp only [{simp_bwd}]")

    # Strategy 2: conv on LHS with rw [h], then simp [← h, hc]
    # Expand goal_lhs once, then normalize backward
    for v in eq2_vars:
        args = ' '.join(eq1_vars)
        proofs.append(
            f"{intro}\n{ci_block}"
            f"conv_lhs => rw [show {eq2_vars[0]} = _ from h {' '.join(eq2_vars[:len(eq1_vars)])}]\n"
            f"simp only [← h, {', '.join(ci_names)}]"
        )
        break  # Only try once

    # Strategy 3: conv on RHS with rw [h], then simp [← h, hc]
    proofs.append(
        f"{intro}\n{ci_block}"
        f"conv_rhs => rw [show {eq2_vars[0]} = _ from h {' '.join(eq2_vars[:len(eq1_vars)])}]\n"
        f"simp only [← h, {', '.join(ci_names)}]"
    )

    # Strategy 4: rw [h] on specific subterm then simp
    # For each goal var, try: rw [show <var> = ... from h <args>]
    for target_var in eq2_vars[:3]:
        args_list = [target_var if v == eq1_vars[0] else eq2_vars[0] for v in eq1_vars]
        args_str = ' '.join(args_list)
        rhs_inst = simultaneous_subst(eq1_rhs, eq1_vars, args_list)
        proofs.append(
            f"{intro}\n{ci_block}"
            f"rw [show {target_var} = {rhs_inst} from h {args_str}]\n"
            f"simp only [← h, {', '.join(ci_names)}]"
        )

    # Strategy 5: Multiple rw steps expanding different vars, then simp backward
    if len(eq2_vars) >= 2:
        v1, v2 = eq2_vars[0], eq2_vars[1]
        args1 = [v1 if v == eq1_vars[0] else v1 for v in eq1_vars]
        args2 = [v2 if v == eq1_vars[0] else v1 for v in eq1_vars]
        rhs1 = simultaneous_subst(eq1_rhs, eq1_vars, args1)
        rhs2 = simultaneous_subst(eq1_rhs, eq1_vars, args2)
        proofs.append(
            f"{intro}\n{ci_block}"
            f"rw [show {v1} = {rhs1} from h {' '.join(args1)}, "
            f"show {v2} = {rhs2} from h {' '.join(args2)}]\n"
            f"simp only [← h, {', '.join(ci_names)}]"
        )

    # Strategy 6: Derive that all values of form x ◇ x are equal
    # have hsq : ∀ (a b : G), a ◇ a = b ◇ b (if derivable)
    # This is a 2-step derivation using constancy
    if len(eq1_vars) >= 2 and rhs_only:
        # Try: have hsq := by ... and then simp with it
        proofs.append(
            f"{intro}\n{ci_block}"
            f"simp only [← h, {', '.join(ci_names)}]"
        )

    for proof in proofs:
        if calls >= max_judge_calls:
            return False
        code = make_true_code(problem, proof)
        result = call_judge("true", code)
        calls += 1
        if result.get("status") == "accepted":
            return True

    return False


def try_subexpr_bfs_proof(problem, eq1_text, eq2_text, max_judge_calls=3, max_depth=5, time_limit=30, seed_terms=None):
    """Bidirectional BFS over expression trees with h-pattern matching.

    Searches from both goal_lhs and goal_rhs simultaneously, meeting in the middle.
    Uses unify_tree to match h's LHS/RHS patterns against any subexpression,
    allowing compound variable bindings.

    If seed_terms is provided, these expressions are added as pre-seeded nodes
    connected to the start (as if they were reached in 0 steps), allowing the BFS
    to explore from LLM-suggested intermediates.

    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    import time
    from itertools import product as _prod
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()

    h_lhs_tree = parse_op_tree(eq1_lhs)
    h_rhs_tree = parse_op_tree(eq1_rhs)
    gl_tree = parse_op_tree(eq2_lhs)
    gr_tree = parse_op_tree(eq2_rhs)

    # Build pool of terms to substitute for free variables
    fill_terms = list(eq2_vars)
    for a in eq2_vars:
        for b in eq2_vars:
            fill_terms.append(f'{a} ◇ {b}')
            if len(fill_terms) > 10:
                break
        if len(fill_terms) > 10:
            break

    # Add LLM-suggested seed terms to the fill pool
    if seed_terms:
        for t in seed_terms:
            t = t.strip()
            if t and t not in fill_terms:
                fill_terms.append(t)

    h_vars_set = set(eq1_vars)

    # Compute constancy info: which h-vars are "free" (only on one side)?
    h_lhs_vars = set(re.findall(r'\b([a-z])\b', eq1_lhs))
    h_rhs_vars = set(re.findall(r'\b([a-z])\b', eq1_rhs))
    rhs_only_vars = sorted(h_rhs_vars - h_lhs_vars)  # free vars on RHS
    lhs_only_vars = sorted(h_lhs_vars - h_rhs_vars)  # free vars on LHS

    # For constancy rewrites, we also need a pool of substitution targets
    # These are the values we substitute for free vars
    const_fill = list(eq2_vars)  # keep small to avoid explosion

    def _all_completions(s):
        free = [v for v in eq1_vars if v not in s]
        if not free:
            return [dict(s)]
        if len(free) > 3:
            return []  # too many combos, skip
        # For 3 free vars, use only goal variables (no compounds) to limit explosion
        pool = eq2_vars if len(free) >= 3 else fill_terms
        return [dict(s, **{v: val for v, val in zip(free, combo)})
                for combo in _prod(pool, repeat=len(free))]

    def _format_args(full_s):
        parts = []
        for v in eq1_vars:
            val = full_s.get(v, eq2_vars[0] if eq2_vars else 'x')
            if '◇' in val:
                parts.append(f'({val})')
            else:
                parts.append(val)
        return ' '.join(parts)

    def _subst_tree(tree, subst):
        if tree[0] == 'var':
            return parse_op_tree(subst[tree[1]]) if tree[1] in subst else tree
        return ('op', _subst_tree(tree[1], subst), _subst_tree(tree[2], subst))

    def _tree_size(t):
        if t[0] == 'var': return 1
        return 1 + _tree_size(t[1]) + _tree_size(t[2])

    MAX_SIZE = 20

    def _gen_rewrites(tree, path=''):
        results = []
        for pattern, repl, is_sym in [(h_lhs_tree, h_rhs_tree, False),
                                       (h_rhs_tree, h_lhs_tree, True)]:
            s = unify_tree(pattern, tree, h_vars_set)
            if s is not None:
                for full_s in _all_completions(s):
                    r = _subst_tree(repl, full_s)
                    if _tree_size(r) <= MAX_SIZE:
                        results.append((path, r, _format_args(full_s), is_sym))

        # Constancy rewrites: match h_rhs pattern, change free vars
        # If h: x = f(x,y,z) where y,z are rhs_only, then
        # f(x,y1,z1) = f(x,y2,z2) via (h x y1 z1).symm.trans (h x y2 z2)
        if rhs_only_vars:
            s = unify_tree(h_rhs_tree, tree, h_vars_set)
            if s is not None:
                for full_s_orig in _all_completions(s):
                    orig_args = _format_args(full_s_orig)
                    # Try changing each combination of free vars
                    free_positions = [eq1_vars.index(v) for v in rhs_only_vars if v in eq1_vars]
                    for new_vals in _prod(const_fill, repeat=len(free_positions)):
                        full_s_new = dict(full_s_orig)
                        changed = False
                        for pos_idx, new_val in zip(free_positions, new_vals):
                            old_val = full_s_orig.get(eq1_vars[pos_idx], '')
                            if old_val != new_val:
                                full_s_new[eq1_vars[pos_idx]] = new_val
                                changed = True
                        if not changed:
                            continue
                        r = _subst_tree(h_rhs_tree, full_s_new)
                        if _tree_size(r) <= MAX_SIZE:
                            new_args = _format_args(full_s_new)
                            # Encode constancy step: CONST|orig_args|new_args
                            results.append((path, r, f"CONST|{orig_args}|{new_args}", False))

        # Similarly for lhs_only constancy: match h_lhs, change free vars on LHS
        if lhs_only_vars:
            s = unify_tree(h_lhs_tree, tree, h_vars_set)
            if s is not None:
                for full_s_orig in _all_completions(s):
                    orig_args = _format_args(full_s_orig)
                    free_positions = [eq1_vars.index(v) for v in lhs_only_vars if v in eq1_vars]
                    for new_vals in _prod(const_fill, repeat=len(free_positions)):
                        full_s_new = dict(full_s_orig)
                        changed = False
                        for pos_idx, new_val in zip(free_positions, new_vals):
                            old_val = full_s_orig.get(eq1_vars[pos_idx], '')
                            if old_val != new_val:
                                full_s_new[eq1_vars[pos_idx]] = new_val
                                changed = True
                        if not changed:
                            continue
                        r = _subst_tree(h_lhs_tree, full_s_new)
                        if _tree_size(r) <= MAX_SIZE:
                            new_args = _format_args(full_s_new)
                            # LHS constancy: (h orig).trans (h new).symm
                            results.append((path, r, f"LCONST|{orig_args}|{new_args}", False))

        if tree[0] == 'op':
            for p, sub_r, a, sym in _gen_rewrites(tree[1], path + 'L'):
                full = ('op', sub_r, tree[2])
                if _tree_size(full) <= MAX_SIZE:
                    results.append((p, full, a, sym))
            for p, sub_r, a, sym in _gen_rewrites(tree[2], path + 'R'):
                full = ('op', tree[1], sub_r)
                if _tree_size(full) <= MAX_SIZE:
                    results.append((p, full, a, sym))
        return results

    def tree_norm(tree):
        return tree_to_str(tree).replace(' ', '')

    def _extract_chain(visited, target_norm):
        chain = []
        cur = target_norm
        while visited[cur] is not None:
            pn, rpath, rargs, rsymm, ptree, rtree = visited[cur]
            chain.append((rpath, rargs, rsymm, ptree, rtree))
            cur = pn
        chain.reverse()
        return chain

    # Bidirectional BFS: forward from goal_lhs, backward from goal_rhs
    fwd_start = tree_norm(gl_tree)
    bwd_start = tree_norm(gr_tree)

    if fwd_start == bwd_start:
        # goal_lhs = goal_rhs trivially
        proof = f"intro {' '.join(eq2_vars)}\nrfl"
        code = make_true_code(problem, proof)
        result = call_judge("true", code)
        return result.get("status") == "accepted"

    # norm -> (prev_norm, path, args, is_symm, prev_tree, result_tree) or None for start
    fwd_visited = {fwd_start: None}
    bwd_visited = {bwd_start: None}
    fwd_frontier = [(gl_tree, fwd_start)]
    bwd_frontier = [(gr_tree, bwd_start)]
    fwd_trees = {fwd_start: gl_tree}  # norm -> tree
    bwd_trees = {bwd_start: gr_tree}
    calls = 0
    t0 = time.time()
    STATE_LIMIT = 120000

    for depth in range(max_depth):
        if time.time() - t0 > time_limit:
            break

        # Expand forward frontier
        fwd_next = []
        for tree, tnorm in fwd_frontier:
            if time.time() - t0 > time_limit:
                break
            for path, new_tree, args, is_symm in _gen_rewrites(tree):
                nn = tree_norm(new_tree)
                if nn in fwd_visited:
                    continue
                fwd_visited[nn] = (tnorm, path, args, is_symm, tree, new_tree)
                fwd_trees[nn] = new_tree
                fwd_next.append((new_tree, nn))
                # Check if meets backward
                if nn in bwd_visited:
                    fwd_chain = _extract_chain(fwd_visited, nn)
                    bwd_chain_raw = _extract_chain(bwd_visited, nn)
                    # Reverse backward chain: each step goes from child to parent
                    # Flip is_symm, swap prev_tree and result_tree
                    bwd_chain = []
                    for rp, ra, rs, pt, rt in reversed(bwd_chain_raw):
                        bwd_chain.append((rp, ra, not rs, rt, pt))
                    chain = fwd_chain + bwd_chain
                    proof = _build_tree_bfs_proof(eq2_vars, eq2_lhs, eq2_rhs, chain)
                    code = make_true_code(problem, proof)
                    result = call_judge("true", code)
                    calls += 1
                    if result.get("status") == "accepted":
                        return True
                    if calls >= max_judge_calls:
                        return False
            if len(fwd_visited) + len(bwd_visited) > STATE_LIMIT:
                break
        fwd_frontier = fwd_next

        if time.time() - t0 > time_limit:
            break
        if len(fwd_visited) + len(bwd_visited) > STATE_LIMIT:
            break

        # Expand backward frontier
        bwd_next = []
        for tree, tnorm in bwd_frontier:
            if time.time() - t0 > time_limit:
                break
            for path, new_tree, args, is_symm in _gen_rewrites(tree):
                nn = tree_norm(new_tree)
                if nn in bwd_visited:
                    continue
                bwd_visited[nn] = (tnorm, path, args, is_symm, tree, new_tree)
                bwd_trees[nn] = new_tree
                bwd_next.append((new_tree, nn))
                # Check if meets forward
                if nn in fwd_visited:
                    fwd_chain = _extract_chain(fwd_visited, nn)
                    bwd_chain_raw = _extract_chain(bwd_visited, nn)
                    bwd_chain = []
                    for rp, ra, rs, pt, rt in reversed(bwd_chain_raw):
                        bwd_chain.append((rp, ra, not rs, rt, pt))
                    chain = fwd_chain + bwd_chain
                    proof = _build_tree_bfs_proof(eq2_vars, eq2_lhs, eq2_rhs, chain)
                    code = make_true_code(problem, proof)
                    result = call_judge("true", code)
                    calls += 1
                    if result.get("status") == "accepted":
                        return True
                    if calls >= max_judge_calls:
                        return False
            if len(fwd_visited) + len(bwd_visited) > STATE_LIMIT:
                break
        bwd_frontier = bwd_next

        if not fwd_frontier and not bwd_frontier:
            break
        if len(fwd_visited) + len(bwd_visited) > STATE_LIMIT:
            break

    return False


def _build_tree_bfs_proof(eq2_vars, eq2_lhs, eq2_rhs, chain):
    """Build a Lean proof from a chain of tree-level h-rewrites.
    chain: list of (path, args_str, is_symm, tree_before_step, tree_after_step)
    args_str can be:
      - normal h args like "x y z"
      - "CONST|orig_args|new_args" for constancy via (h orig).symm.trans (h new)
      - "LCONST|orig_args|new_args" for LHS constancy via (h orig).trans (h new).symm
    """
    intro = f"intro {' '.join(eq2_vars)}"

    def _step_just(path, args, is_symm, tree):
        if args.startswith("CONST|"):
            # Constancy: (h orig_args).symm.trans (h new_args)
            parts = args.split("|", 2)
            orig_args = parts[1]
            new_args = parts[2]
            h_expr = f"(h {orig_args}).symm.trans (h {new_args})"
        elif args.startswith("LCONST|"):
            # LHS constancy: (h orig_args).trans (h new_args).symm
            parts = args.split("|", 2)
            orig_args = parts[1]
            new_args = parts[2]
            h_expr = f"(h {orig_args}).trans (h {new_args}).symm"
        else:
            h_expr = f"(h {args}).symm" if is_symm else f"h {args}"
        if not path:
            return h_expr
        return wrap_congr_arg(tree, path, h_expr)

    if len(chain) == 1:
        path, args, is_symm, tree, _ = chain[0]
        return f"{intro}\nexact {_step_just(path, args, is_symm, tree)}"

    lines = [intro, f"calc {eq2_lhs}"]

    for i, (path, args, is_symm, tree, result_tree) in enumerate(chain):
        just = _step_just(path, args, is_symm, tree)
        inter_str = tree_to_str(result_tree)

        if i < len(chain) - 1:
            lines.append(f"  _ = {inter_str} := {just}")
        else:
            lines.append(f"  _ = {eq2_rhs} := {just}")

    return '\n'.join(lines)


def try_constancy_calc_proof(problem, eq1_text, eq2_text, max_judge_calls=4):
    """Try multi-step proofs using constancy lemmas derived from free variables.
    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts2 = eq2_text.split('=', 1)
    if len(parts2) != 2:
        return False
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()

    constancy_info, lhs_only, rhs_only = build_constancy_info(eq1_text, eq1_vars, eq2_vars)
    if not constancy_info:
        return False

    intro = f"intro {' '.join(eq2_vars)}"
    default_fill = eq2_vars[0] if eq2_vars else 'x'

    gl_tree = parse_op_tree(eq2_lhs)
    gr_tree = parse_op_tree(eq2_rhs)

    proof_steps = find_constancy_steps(gl_tree, gr_tree, constancy_info, default_fill)
    if not proof_steps:
        return False

    proof = build_constancy_proof(intro, eq2_lhs, eq2_rhs, gl_tree, gr_tree,
                                  proof_steps, constancy_info)
    code = make_true_code(problem, proof)
    result = call_judge("true", code)
    if result.get("status") == "accepted":
        return True

    return False


def try_hybrid_calc_proof(problem, eq1_text, eq2_text, max_judge_calls=4):
    """Try proofs combining h-instantiation steps with constancy steps.

    Pattern 1: h(args) then constancy steps (goal_lhs →h→ intermediate →const→ goal_rhs)
    Pattern 2: constancy then h(args) (goal_lhs →const→ intermediate →h→ goal_rhs)
    Pattern 3: h then h then constancy (depth 2 h-chain + constancy)

    Returns True if accepted, False otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)

    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return False

    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()
    g_lhs = eq2_lhs.replace(' ', '')
    g_rhs = eq2_rhs.replace(' ', '')

    constancy_info, lhs_only, rhs_only = build_constancy_info(eq1_text, eq1_vars, eq2_vars)
    if not constancy_info:
        return False

    intro = f"intro {' '.join(eq2_vars)}"
    default_fill = eq2_vars[0] if eq2_vars else 'x'
    calls = 0

    # Pre-compute h-instantiations (bare variables + compound terms from eq2_vars)
    h_insts = {}  # normalized_expr -> {normalized_target: args_string}

    def _add_h_inst(combo):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        nl = new_lhs.replace(' ', '')
        nr = new_rhs.replace(' ', '')
        if nl == nr:
            return
        args = ' '.join(combo)
        if nl not in h_insts:
            h_insts[nl] = {}
        if nr not in h_insts[nl]:
            h_insts[nl][nr] = args
        if nr not in h_insts:
            h_insts[nr] = {}
        if nl not in h_insts[nr]:
            h_insts[nr][nl] = args + "|symm"

    # Bare variable combos
    for combo in product(eq2_vars, repeat=len(eq1_vars)):
        _add_h_inst(combo)

    # Compound terms: (a ◇ b) for all pairs
    compound_terms = [f"({a} \u25c7 {b})" for a in eq2_vars for b in eq2_vars]
    n_h = len(eq1_vars)
    n_b = len(eq2_vars)
    n_c = len(compound_terms)

    # k=1: exactly one compound argument position, rest bare
    k1_count = n_h * n_c * (n_b ** max(n_h - 1, 0))
    if k1_count <= 50000:
        for pos in range(n_h):
            for ct in compound_terms:
                for bare_combo in product(eq2_vars, repeat=n_h - 1):
                    combo = list(bare_combo[:pos]) + [ct] + list(bare_combo[pos:])
                    _add_h_inst(combo)

    # Pattern 1: h-step from goal_lhs, then constancy to goal_rhs
    if g_lhs in h_insts:
        for intermediate_norm, args in h_insts[g_lhs].items():
            # Parse intermediate as a tree, check constancy to goal_rhs
            inter_str = _denormalize(intermediate_norm, eq2_vars)
            if inter_str is None:
                continue
            inter_tree = parse_op_tree(inter_str)
            gr_tree = parse_op_tree(eq2_rhs)
            if inter_tree == gr_tree:
                continue  # Would be handled by calc_chain_proof
            csteps = find_constancy_steps(inter_tree, gr_tree, constancy_info, default_fill)
            if not csteps:
                continue

            # Build proof: h-step then constancy
            symm = args.endswith("|symm")
            h_args = args.replace("|symm", "")
            h_step = f"(h {h_args}).symm" if symm else f"h {h_args}"

            const_proof = build_constancy_proof(
                intro, inter_str, eq2_rhs, inter_tree, gr_tree,
                csteps, constancy_info
            )
            # Extract have lines and calc body from const_proof
            const_lines = const_proof.split('\n')
            have_lines = [l for l in const_lines if l.startswith('have ')]
            # Build combined calc
            calc_lines = [f"calc {eq2_lhs}"]
            calc_lines.append(f"  _ = {inter_str} := {h_step}")
            # Add constancy steps
            current_tree = inter_tree
            for i, (path, cargs, csymm, ci_idx) in enumerate(csteps):
                ci_used_map = {}
                for _, _, _, cidx in csteps:
                    if cidx not in ci_used_map:
                        ci_used_map[cidx] = "hconst" if len(ci_used_map) == 0 else f"hconst{len(ci_used_map)+1}"
                hname = ci_used_map[ci_idx]
                inner = f"({hname} {cargs})" if not csymm else f"({hname} {cargs}).symm"
                step_proof = wrap_congr_arg(current_tree, path, inner)
                target_sub = get_subtree(gr_tree, path)
                current_tree = apply_rewrite_at(current_tree, path, target_sub)
                current_str = tree_to_str(current_tree)
                if i < len(csteps) - 1:
                    calc_lines.append(f"  _ = {current_str} := {step_proof}")
                else:
                    calc_lines.append(f"  _ = {eq2_rhs} := {step_proof}")

            # Build ci_used for have lines
            ci_used = {}
            ci_have_lines = []
            idx = 1
            for _, _, _, cidx in csteps:
                if cidx not in ci_used:
                    name = "hconst" if idx == 1 else f"hconst{idx}"
                    line = constancy_info[cidx]['have_line']
                    if idx > 1:
                        line = line.replace('hconst', name, 1)
                    ci_have_lines.append(line)
                    ci_used[cidx] = name
                    idx += 1

            proof = f"{intro}\n" + "\n".join(ci_have_lines) + "\n" + "\n".join(calc_lines)
            code = make_true_code(problem, proof)
            result = call_judge("true", code)
            calls += 1
            if result.get("status") == "accepted":
                return True
            if calls >= max_judge_calls:
                return False

    # Pattern 2: constancy from goal_lhs, then h-step to goal_rhs
    if g_rhs in h_insts:
        for intermediate_norm, args in h_insts[g_rhs].items():
            inter_str = _denormalize(intermediate_norm, eq2_vars)
            if inter_str is None:
                continue
            inter_tree = parse_op_tree(inter_str)
            gl_tree = parse_op_tree(eq2_lhs)
            if gl_tree == inter_tree:
                continue
            csteps = find_constancy_steps(gl_tree, inter_tree, constancy_info, default_fill)
            if not csteps:
                continue

            # The h-step goes from intermediate to goal_rhs
            # args maps intermediate_norm → g_rhs
            symm = args.endswith("|symm")
            h_args = args.replace("|symm", "")
            # Since h_insts[g_rhs][intermediate_norm] = args means intermediate_norm →args→ g_rhs
            # Wait, h_insts[g_rhs] maps targets reachable from g_rhs. So intermediate_norm is a target from g_rhs.
            # That means g_rhs →args→ intermediate_norm. We need intermediate →h→ goal_rhs.
            # So we need the reverse: intermediate_norm →args_rev→ g_rhs
            # Actually h_insts[g_rhs][intermediate_norm] = args means g_rhs can reach intermediate_norm via args.
            # We need intermediate to reach g_rhs: so we go h_insts[intermediate_norm][g_rhs]
            if intermediate_norm not in h_insts or g_rhs not in h_insts[intermediate_norm]:
                continue
            h_args2 = h_insts[intermediate_norm][g_rhs]
            symm2 = h_args2.endswith("|symm")
            h_args2_clean = h_args2.replace("|symm", "")
            h_step = f"(h {h_args2_clean}).symm" if symm2 else f"h {h_args2_clean}"

            # Build have lines for constancy
            ci_used = {}
            ci_have_lines = []
            idx = 1
            for _, _, _, cidx in csteps:
                if cidx not in ci_used:
                    name = "hconst" if idx == 1 else f"hconst{idx}"
                    line = constancy_info[cidx]['have_line']
                    if idx > 1:
                        line = line.replace('hconst', name, 1)
                    ci_have_lines.append(line)
                    ci_used[cidx] = name
                    idx += 1

            # Build calc chain: constancy steps then h-step
            calc_lines = [f"calc {eq2_lhs}"]
            current_tree = gl_tree
            for i, (path, cargs, csymm, ci_idx) in enumerate(csteps):
                hname = ci_used[ci_idx]
                inner = f"({hname} {cargs})" if not csymm else f"({hname} {cargs}).symm"
                step_proof = wrap_congr_arg(current_tree, path, inner)
                target_sub = get_subtree(inter_tree, path)
                current_tree = apply_rewrite_at(current_tree, path, target_sub)
                current_str = tree_to_str(current_tree)
                calc_lines.append(f"  _ = {current_str} := {step_proof}")
            calc_lines.append(f"  _ = {eq2_rhs} := {h_step}")

            proof = f"{intro}\n" + "\n".join(ci_have_lines) + "\n" + "\n".join(calc_lines)
            code = make_true_code(problem, proof)
            result = call_judge("true", code)
            calls += 1
            if result.get("status") == "accepted":
                return True
            if calls >= max_judge_calls:
                return False

    # Pattern 3: 2-step h-chain then constancy
    if g_lhs in h_insts:
        for mid1_norm, args1 in h_insts[g_lhs].items():
            if mid1_norm not in h_insts:
                continue
            for mid2_norm, args2 in h_insts[mid1_norm].items():
                if mid2_norm == g_lhs or mid2_norm == g_rhs:
                    continue  # Skip loops and direct matches
                mid2_str = _denormalize(mid2_norm, eq2_vars)
                if mid2_str is None:
                    continue
                mid2_tree = parse_op_tree(mid2_str)
                gr_tree = parse_op_tree(eq2_rhs)
                if mid2_tree == gr_tree:
                    continue
                csteps = find_constancy_steps(mid2_tree, gr_tree, constancy_info, default_fill)
                if not csteps:
                    continue

                mid1_str = _denormalize(mid1_norm, eq2_vars)
                if mid1_str is None:
                    continue

                symm1 = args1.endswith("|symm")
                h1 = args1.replace("|symm", "")
                h1_step = f"(h {h1}).symm" if symm1 else f"h {h1}"
                symm2 = args2.endswith("|symm")
                h2 = args2.replace("|symm", "")
                h2_step = f"(h {h2}).symm" if symm2 else f"h {h2}"

                ci_used = {}
                ci_have_lines = []
                idx = 1
                for _, _, _, cidx in csteps:
                    if cidx not in ci_used:
                        name = "hconst" if idx == 1 else f"hconst{idx}"
                        line = constancy_info[cidx]['have_line']
                        if idx > 1:
                            line = line.replace('hconst', name, 1)
                        ci_have_lines.append(line)
                        ci_used[cidx] = name
                        idx += 1

                calc_lines = [f"calc {eq2_lhs}"]
                calc_lines.append(f"  _ = {mid1_str} := {h1_step}")
                calc_lines.append(f"  _ = {mid2_str} := {h2_step}")
                current_tree = mid2_tree
                for i, (path, cargs, csymm, ci_idx) in enumerate(csteps):
                    hname = ci_used[ci_idx]
                    inner = f"({hname} {cargs})" if not csymm else f"({hname} {cargs}).symm"
                    step_proof = wrap_congr_arg(current_tree, path, inner)
                    target_sub = get_subtree(gr_tree, path)
                    current_tree = apply_rewrite_at(current_tree, path, target_sub)
                    current_str = tree_to_str(current_tree)
                    if i < len(csteps) - 1:
                        calc_lines.append(f"  _ = {current_str} := {step_proof}")
                    else:
                        calc_lines.append(f"  _ = {eq2_rhs} := {step_proof}")

                proof = f"{intro}\n" + "\n".join(ci_have_lines) + "\n" + "\n".join(calc_lines)
                code = make_true_code(problem, proof)
                result = call_judge("true", code)
                calls += 1
                if result.get("status") == "accepted":
                    return True
                if calls >= max_judge_calls:
                    return False

    return False


def _denormalize(norm_expr, eq2_vars):
    """Convert a normalized (no-space) expression back to readable form.
    This is approximate — adds spaces around ◇ operators."""
    # Simply add spaces around ◇
    result = norm_expr.replace('\u25c7', ' \u25c7 ')
    # Verify it parses
    try:
        parse_op_tree(result)
        return result
    except Exception:
        return None



def build_fix_hint(error_info, verdict):
    """Generate a concrete fix hint from parsed error."""
    etype = error_info["type"]

    # Pre-flight errors — very specific
    if etype.startswith("preflight_"):
        return error_info.get("detail", "Pre-flight check failed.")

    if etype == "table_wrong":
        eq = error_info.get("equation", "the hypothesis")
        fin = error_info.get("fin_size", "N")
        return (f"Your Cayley table on Fin {fin} does NOT satisfy {eq}. "
                f"You must find a table that satisfies the hypothesis equation but violates the goal. "
                f"Try a completely different table structure or a different Fin size.")

    if etype == "type_mismatch":
        if error_info.get("expected") and error_info.get("got"):
            exp = error_info['expected']
            got = error_info['got']
            return (f"Type mismatch: proof gives `{got}` but needs `{exp}`. "
                    "This means a calc step is WRONG — the h-instantiation doesn't produce the equality you think. "
                    "Check: what does `h <your_args>` actually equal? Write it out manually before using it.")
        return ("Type mismatch. Your constancy lemma or calc step has the wrong type. "
                "Write out what `h a b c` produces for your specific arguments and verify the equality manually.")

    if etype == "unknown_tactic":
        tac = error_info.get("detail", "")
        return (f"`{tac}` is not a valid tactic. "
                "Use ONLY: intro, exact, have, calc, rw, conv, apply, constructor, cases, obtain, funext, ext. "
                "For congr_arg: use it as a TERM (`exact congr_arg ...` or in calc), NOT as a standalone tactic.")

    if etype == "unknown_identifier":
        ident = error_info.get("detail", "")
        return (f"`{ident}` doesn't exist. The only given fact is `h`. "
                "Build everything from `h`, `.symm`, `.trans`, `congr_arg`, and `have` lemmas you define yourself.")

    if etype == "unsolved_goals":
        detail = error_info.get('detail', '?')
        return (f"Unsolved goal: `{detail}`. "
                "Your calc chain doesn't reach the target. Try a COMPLETELY different chain: "
                "different intermediate expressions, different h-instantiations, or add more steps.")

    if etype == "app_type_mismatch":
        return ("Wrong number or type of arguments. Count the hypothesis variables — "
                "h needs EXACTLY that many arguments. E.g., if h has x,y,z then `h a b c` (3 args).")

    if etype == "function_expected":
        return "Applied something that's not a function. Check parentheses carefully."

    # Fallback
    raw = error_info.get("raw", "")
    if "sorry" in raw.lower():
        return "Proof contains sorry/admit which is BANNED."
    if "unsolved goals" in raw.lower():
        return "Unsolved goals remain. Your approach may be fundamentally wrong — try a different strategy."
    return f"Lean error: {raw[:300]}"


def main():
    startup = read_message()
    problem = startup["problem"]
    # Normalise magma operator at the source: HF problem text uses `*`, Lean
    # Magma needs `◇`. All internal parsers accept both, but generated Lean
    # proof strings must use `◇` or HMul synthesis fails.
    problem["equation1"] = normalize_op_to_diamond(problem["equation1"])
    problem["equation2"] = normalize_op_to_diamond(problem["equation2"])
    eq1_text = problem["equation1"]
    eq2_text = problem["equation2"]

    # Stage 0: Known counterexample lookup
    n, table = known_counterexample(problem["eq1_id"], problem["eq2_id"])
    if n is not None:
        result = call_judge("false", make_false_code(problem, n, table))
        if result.get("status") == "accepted":
            return

    # Stage 1: Brute-force counterexample search
    n, table = exhaustive_counterexample(eq1_text, eq2_text, max_n=3)
    if n is not None:
        result = call_judge("false", make_false_code(problem, n, table))
        if result.get("status") == "accepted":
            return

    n, table = extended_counterexample(eq1_text, eq2_text, max_n=5, random_attempts=5000)
    if n is not None:
        result = call_judge("false", make_false_code(problem, n, table))
        if result.get("status") == "accepted":
            return

    # Backtracking search with constraint propagation (Fin 4-5)
    n, table = backtrack_counterexample(eq1_text, eq2_text, sizes=(4, 5), time_limit=10)
    if n is not None:
        result = call_judge("false", make_false_code(problem, n, table))
        if result.get("status") == "accepted":
            return

    # Stage 2: Singleton collapse
    if try_singleton(problem, eq1_text, eq2_text):
        return

    # Stage 3: LLM loop with structured error feedback
    notes = analyze_equation_structure(eq1_text, eq2_text)
    notes.append("No counterexample found on Fin 2-7 (exhaustive 2-3 + structured + random 4-7)")
    notes.append("This strongly suggests the implication is TRUE. Focus on writing a proof.")
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    h_insts = compute_h_instantiations(eq1_text, eq1_vars, eq2_vars)

    # Try direct proof via substitution search (0 LLM calls)
    if try_direct_proof(problem, eq1_text, eq2_text):
        return

    # Try library proof via EquationSearch theorem reference (0 LLM calls)
    if try_library_proof(problem):
        return

    # Try transitive library proof via chaining known implications (0 LLM calls)
    if try_transitive_library_proof(problem):
        return

    # Try calc chain proof via BFS over h-instantiations (0 LLM calls)
    if try_calc_chain_proof(problem, eq1_text, eq2_text):
        return

    # Try compound calc chain proof with compound terms like (x ◇ y) as h-arguments (0 LLM calls)
    if try_compound_calc_proof(problem, eq1_text, eq2_text):
        return

    # Try constancy calc proof with congr_arg chains (0 LLM calls)
    if try_constancy_calc_proof(problem, eq1_text, eq2_text):
        return

    # Try hybrid h-step + constancy proof (0 LLM calls)
    if try_hybrid_calc_proof(problem, eq1_text, eq2_text):
        return

    # Try deep constancy proof via spine analysis + compound h-rewriting (0 LLM calls)
    if try_deep_constancy_proof(problem, eq1_text, eq2_text):
        return

    # Try simp rewrite proof with derived constancy lemmas (0 LLM calls)
    if try_simp_rewrite_proof(problem, eq1_text, eq2_text):
        return

    # Try subexpression BFS with bidirectional tree pattern matching (0 LLM calls)
    if try_subexpr_bfs_proof(problem, eq1_text, eq2_text):
        return

    # Deep analysis for proof strategy hints
    deep_hints = deep_proof_analysis(eq1_text, eq2_text)
    if deep_hints:
        notes.extend(deep_hints)

    # Compute BFS near-miss hints for the LLM
    bfs_hints = compute_bfs_near_miss(eq1_text, eq2_text, eq1_vars, eq2_vars)

    # Compute structural proof skeleton hints
    skeleton_hints = compute_proof_skeleton(eq1_text, eq2_text, eq1_vars, eq2_vars)

    # Compute MATCH-COLLAPSE hints for the LLM
    match_collapse = compute_match_collapse_hints(eq1_text, eq2_text)

    # Compute equation analysis
    equation_analysis = compute_equation_analysis(eq1_text, eq2_text)

    last_error_info = None
    seen_answers = set()
    false_attempts = 0

    # No per-problem call cap — loop until wall-clock watchdog or LLM error.
    rnd = -1
    while True:
        rnd += 1
        analysis_parts = list(notes)
        if skeleton_hints:
            analysis_parts.append(skeleton_hints)
        context = {"analysis": "\n".join(analysis_parts)}
        # Force the LLM to see ◇ from the start; the problem source uses * and
        # naive imitation produces proofs that fail to synthesize HMul.
        context["h_text"] = normalize_op_to_diamond(problem.get("equation1", ""))
        context["goal_text"] = normalize_op_to_diamond(problem.get("equation2", ""))
        if h_insts:
            context["h_instantiations"] = "\n".join(f"  {h}" for h in h_insts[:10])

        # BFS hints
        if bfs_hints:
            context["bfs_hints"] = "\n## BFS near-miss results\n" + bfs_hints
        else:
            context["bfs_hints"] = ""

        # Equation analysis and match-collapse hints
        context["equation_analysis"] = equation_analysis
        context["match_collapse_hints"] = match_collapse

        # After failed false attempts, force true verdict
        if false_attempts >= 2:
            context["verdict_hint"] = (
                f"\nIMPORTANT: You have tried {false_attempts} counterexample tables and ALL failed. "
                "This implication is almost certainly TRUE. Provide a tactic proof, not a counterexample."
            )
        else:
            context["verdict_hint"] = ""

        # Temperature strategy: start warm for diversity, escalate further on retries
        temps = [0.3, 0.5, 0.7, 0.9]
        temp = temps[min(rnd, len(temps) - 1)]
        overrides = {"temperature": temp, "seed": rnd * 7 + 13}

        # Build error section only if there's an actual error
        if last_error_info:
            hint = build_fix_hint(last_error_info, "true")
            error_parts = [f"\n## Error from previous attempt (round {rnd})"]
            error_parts.append(f"Error type: {last_error_info['type']}")
            error_parts.append(f"Fix hint: {hint}")
            if last_error_info.get("expected"):
                error_parts.append(f"Expected: {last_error_info['expected']}")
            if last_error_info.get("got"):
                error_parts.append(f"Got: {last_error_info['got']}")
            context["error_section"] = "\n".join(error_parts)
        else:
            context["error_section"] = ""

        llm_result = call_llm(context, overrides=overrides)
        if "error" in llm_result:
            break

        answer = extract_json(llm_result.get("response", ""))
        if not answer:
            continue

        verdict = answer.get("verdict")
        if verdict == "true":
            proof = clean_proof(answer.get("proof", ""))
            if not proof:
                continue
            # Normalise the magma operator. LLM often emits `*` from the problem
            # text; Lean's Magma typeclass requires `◇`.
            proof = normalize_op_to_diamond(proof)
            # Pre-flight validation — catch common LLM mistakes before using judge call
            proof, pf_error = preflight_proof(proof)
            if pf_error:
                last_error_info = pf_error
                notes.append(f"Round {rnd}: pre-flight rejection: {pf_error['type']}")
                continue
            # Dedup
            if proof in seen_answers:
                notes.append(f"Round {rnd}: duplicate proof, skipping")
                continue
            seen_answers.add(proof)
            code = make_true_code(problem, proof)
        elif verdict == "false":
            tbl = answer.get("counterexample_table")
            if not tbl or not isinstance(tbl, list):
                continue
            n = len(tbl)
            if n < 2 or n > 7:
                continue
            tbl_key = str(tbl)
            if tbl_key in seen_answers:
                notes.append(f"Round {rnd}: duplicate table, skipping")
                continue
            seen_answers.add(tbl_key)
            # Local verification before using judge call
            sat1, sat2 = verify_counterexample(eq1_text, eq2_text, n, tbl)
            if not sat1:
                false_attempts += 1
                last_error_info = {
                    "type": "table_wrong",
                    "equation": problem["eq1_id"],
                    "fin_size": str(n),
                    "detail": f"Table does not satisfy {problem['eq1_id']}",
                }
                notes.append(f"Round {rnd}: table on Fin {n} fails {problem['eq1_id']} (local check)")
                continue
            if sat2:
                false_attempts += 1
                last_error_info = {
                    "type": "table_wrong",
                    "equation": problem["eq2_id"],
                    "fin_size": str(n),
                    "detail": f"Table satisfies BOTH equations (need to violate {problem['eq2_id']})",
                }
                notes.append(f"Round {rnd}: table satisfies both equations (local check)")
                continue
            code = make_false_code(problem, n, tbl)
        else:
            continue

        result = call_judge(verdict, code)
        if result.get("status") == "accepted":
            return

        # Auto-repair: try flipping .symm when type mismatch suggests wrong direction
        stderr = result.get("stderr", "") or result.get("message", "")
        if verdict == "true" and "type mismatch" in stderr:
            repaired = try_symm_repair(proof, stderr)
            if repaired and repaired != proof and repaired not in seen_answers:
                seen_answers.add(repaired)
                repair_code = make_true_code(problem, repaired)
                repair_result = call_judge("true", repair_code)
                if repair_result.get("status") == "accepted":
                    return
                # If repair also failed, use its error for feedback
                stderr = repair_result.get("stderr", "") or repair_result.get("message", "")

        # Extract intermediates from failed proof and try BFS through them
        if verdict == "true" and proof:
            intermediates = extract_calc_intermediates(proof)
            if intermediates:
                bfs_result = try_subexpr_bfs_proof(
                    problem, eq1_text, eq2_text,
                    max_judge_calls=1, max_depth=3, time_limit=5,
                    seed_terms=intermediates
                )
                if bfs_result:
                    return

        # Parse error for next round
        last_error_info = parse_lean_error(stderr)
        notes.append(f"Round {rnd}: verdict={verdict}, status={result.get('status')}, error={last_error_info['type']}")


if __name__ == "__main__":
    main()
