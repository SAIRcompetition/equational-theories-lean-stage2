# Tutorial: Solo Track

This tutorial walks through three complete examples showing how the solver, proxy, and judge interact to solve problems on the **Solo track** — one solver subprocess per problem with a fixed per-problem budget. Each walkthrough lists the model used in its header; the reference configuration in `pipeline/config.json` is `openai/gpt-oss-120b` via `deepinfra/bf16`.

For the **Marathon track** (one subprocess for N problems, shared global budget, triage-friendly) see [`../marathon/TUTORIAL.md`](../marathon/TUTORIAL.md). The two tracks share `judge/verify.py` and the five-status mapping; they differ only in solver I/O shape and budgeting.

For setup, architecture, protocol details, and configuration, see the [README](../../README.md) in the project root.

## Running the Demos

Make sure the environment is set up first (`bash scripts/setup.sh` if not done yet):

```bash
source .env.judge
```

Run any demo on the 20-problem sample set:

```bash
# baseline: brute-force + singleton + generic LLM fallback
python3 -m pipeline.runner \
  --submission examples/solo/demos/baseline \
  --problems examples/problems/sample_20.json

# oss_twophase: deeper search + analysis-then-implementation LLM
python3 -m pipeline.runner \
  --submission examples/solo/demos/oss_twophase \
  --problems examples/problems/sample_20.json

# oss_opnorm reference: 16 deterministic strategies + structural-context LLM
python3 -m pipeline.runner \
  --submission examples/solo/demos/oss_opnorm \
  --problems examples/problems/sample_20.json
```

For the full 200-problem evaluation, replace `sample_20.json` with `sample_200.json`. LLM calls require the `OPENROUTER_API_KEY` environment variable (or a per-config `api_key_env` for direct providers — see the README for details).

Your submission is a **single file**: `solver.py`, up to 500 KB. If your solver uses the LLM, the prompt template lives as a top-level `PROMPT = "..."` string constant inside `solver.py` (the proxy extracts it via AST — the module is never imported). All three demos under `examples/solo/demos/` are self-contained — just copy any folder and run.

The three Solo demos form a learning ladder:

- `baseline` — no LLM required; brute-force + singleton + generic LLM fallback. The simplest starting point and a complete reference for the stdin/stdout protocol.
- `oss_twophase` — gpt-oss-120b; deeper deterministic search plus an analysis-then-implementation two-phase LLM. Shown in Walkthrough 1.
- `oss_opnorm` — gpt-oss-120b; flagship reference mining solver — 16 deterministic strategies fed into a structural-context LLM call. Shown in Walkthrough 3.

---

## Walkthrough 1: Deterministic Counterexample (`oss_twophase`)

**Problem**: `false_919_872` -- Does Equation919 imply Equation872?

- Hypothesis (Eq919): `x = y ◇ ((y ◇ y) ◇ (y ◇ x))`
- Goal (Eq872): `x = y ◇ ((x ◇ x) ◇ (y ◇ x))`

**Model**: none — deterministic counterexample; no LLM call is made.

### What happens

The `oss_twophase` solver's deterministic stage exhaustively searches Cayley tables on Fin 2 through Fin 7. It finds a counterexample on **Fin 5** -- a 5x5 operation table where Equation919 holds but Equation872 does not.

### Interaction log

**Step 1** -- Proxy sends the problem to solver:

```json
{"problem": {"id": "false_919_872", "eq1_id": 919, "eq2_id": 872,
  "equation1": "x = y ◇ ((y ◇ y) ◇ (y ◇ x))",
  "equation2": "x = y ◇ ((x ◇ x) ◇ (y ◇ x))"}, "budget": {...}}
```

**Step 2** -- Solver finds counterexample (no LLM needed), sends judge request:

```json
{"call": "judge", "verdict": "false",
 "code": "import JudgeProblem\nimport JudgeDecide.DecideBang\nimport JudgeFinOp.MemoFinOp\nopen MemoFinOp\n\ndef submission : Goal := by\n  let m : Magma (Fin 5) := {\n    op := finOpTable \"[[3, 4, 1, 2, 0], [2, 0, 4, 1, 3], [0, 1, 2, 3, 4], [1, 3, 0, 4, 2], [4, 2, 3, 0, 1]]\"\n  }\n  refine ⟨Fin 5, m, ?_⟩\n  decideFin!\n"}
```

`JudgeProblem` is written by the judge per submission and binds
`EquationLHS` / `EquationRHS` to the two problem equations, plus an
`abbrev Goal` that names the target type (the ∃ or ∀ statement). The
submitter's `Submission.lean` only has to expose a `submission` of
type `Goal` — the theorem statement itself is judge-controlled (lives
in `Problem.lean`, not Submission.lean).

**Step 3** -- Judge compiles and verifies the Lean proof:

```json
{"status": "accepted", "message": "certificate accepted"}
```

### Result

- **Solved**: Yes
- **LLM calls**: 0
- **Judge calls**: 1
- **Time**: 1.9 seconds

This is the ideal case: the solver finds the answer deterministically with no LLM involvement. The brute-force search + `decideFin!` handles most false problems.

---

## Walkthrough 2: LLM Feedback Loop (`baseline`)

**Problem**: `true_608_593` -- Does Equation608 imply Equation593?

- Hypothesis (Eq608): `x = y ◇ (z ◇ (w ◇ (u ◇ x)))`
- Goal (Eq593): `x = y ◇ (z ◇ (w ◇ (y ◇ x)))`

**Model**: `openai/gpt-oss-120b` via `deepinfra/bf16`.

### What happens

The solver's deterministic stages (counterexample search + singleton pattern) both fail. The solver enters the LLM loop. The LLM makes **4 attempts**, receiving judge error feedback each time, before finding the correct proof.

### Interaction log

**Round 0** -- Solver sends LLM request (proxy fills the `PROMPT` template from `solver.py`):

```json
{"call": "llm", "context": {"round": "0"}}
```

The proxy fills the template with problem data and sends to gpt-oss-120b. The filled prompt includes:
```
Does Equation608 imply Equation593?
Hypothesis: x = y ◇ (z ◇ (w ◇ (u ◇ x)))
Goal: x = y ◇ (z ◇ (w ◇ (y ◇ x)))
Previous attempts: (no previous attempts)
```

**LLM response (wrong -- guesses false)**:
```json
{"verdict": "false", "counterexample_table": [[0, 1, 2], [1, 2, 0], [2, 0, 1]]}
```

**Judge rejects** -- the table actually satisfies both equations:
```
error: (kernel) application type mismatch
  of_decide_eq_true (Eq.refl true)
```

**Round 1** -- LLM sees the error, switches to true:
```json
{"verdict": "true", "proof": "intro h\nsimpa using (h (u:=y))"}
```

**Judge rejects** -- invalid argument name:
```
error: invalid argument name 'u' for function
```

**Round 2** -- LLM tries again:
```json
{"verdict": "true", "proof": "by\n  intro h x y z w\n  specialize h x y z w y\n  simpa using h"}
```

**Judge rejects** -- too many `intro` binders (used `intro h` consuming the hypothesis name):
```
error: tactic 'introN' failed, insufficient number of binders
```

**Round 3** -- LLM finally gets the syntax right:
```json
{"verdict": "true", "proof": "intro x y z w\nsimpa using h x y z w y"}
```

**Judge accepts!**

The key insight: Equation608 has variable `u` that appears only in `u ◇ x`. The proof substitutes `y` for `u`, giving exactly the goal. The LLM needed 4 tries to get the Lean syntax right.

### Final accepted code

```lean
import JudgeProblem

def submission : Goal := by
  intro G _ h x y z w
  simpa using h x y z w y
```

### Result

- **Solved**: Yes
- **LLM calls**: 4
- **Judge calls**: 4
- **Time**: 77 seconds

This shows the feedback loop: each judge error is automatically included in `{history.attempts}` for the next LLM call, so the LLM can learn from its mistakes.

---

## Walkthrough 3: Reference Mining Solver (`oss_opnorm`)

**Problem**: `normal_0121` -- Does Equation3580 imply Equation4304?

- Hypothesis (Eq3580): `x ◇ y = y ◇ ((z ◇ w) ◇ w)`
- Goal (Eq4304): `x ◇ (x ◇ y) = z ◇ (y ◇ y)`

**Model**: `openai/gpt-oss-120b` via `deepinfra/bf16`.

### What happens

`oss_opnorm` is the flagship reference mining solver — not a teaching demo. It runs **16 deterministic proof strategies** (counterexample search on Fin 2-7, singleton detection, library lookup, constancy lemmas, BFS near-miss search, several calc-chain variants). All 16 fail for this problem. On the first LLM call the model emits a correct 3-step `calc` proof and the judge accepts immediately.

The shape of the win mirrors structural-context calc proofs, but the method is triggered autonomously from solver-side constancy analysis rather than a hand-crafted prompt for a designed problem. This was captured during a 1000-problem mining sweep over the `normal` set and is the first LLM-guided win catalogued for `oss_opnorm` (mining run dated 2026-04-23).

### Solver's analysis (sent to LLM via `{solver.*}` placeholders, excerpt)

```
Goal has 3 vars, hypothesis has 4 vars – might be a direct substitution
No counterexample found on Fin 2-7 (exhaustive 2-3 + structured + random 4-7)
This strongly suggests the implication is TRUE. Focus on writing a proof.
CONSTANCY: Variables {'w', 'z'} appear ONLY on the RHS of h. For FIXED {'y'},
the RHS is constant regardless of {'w', 'z'}. So h(same_x, y1, z1) and
h(same_x, y2, z2) give the same LHS.
PROOF STRATEGY: Use a calc chain or transitivity. Apply h with specific args
to rewrite, then apply h again with different args.
```

### LLM response (correct on first try)

```json
{
  "verdict": "true",
  "proof": "intro x y z\ncalc\n  x ◇ (x ◇ y) = (x ◇ y) ◇ ((z ◇ z) ◇ z) := h x (x ◇ y) z z\n  _ = (y ◇ y) ◇ ((z ◇ z) ◇ z) := by\n    have hxy : x ◇ y = y ◇ y := (h x y z z).trans ((h y y z z).symm)\n    exact congrArg (fun t => t ◇ ((z ◇ z) ◇ z)) hxy\n  _ = z ◇ (y ◇ y) := (h z (y ◇ y) z z).symm"
}
```

**Judge accepts!**

### Final accepted code

```lean
import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    x ◇ (x ◇ y) = (x ◇ y) ◇ ((z ◇ z) ◇ z) := h x (x ◇ y) z z
    _ = (y ◇ y) ◇ ((z ◇ z) ◇ z) := by
      have hxy : x ◇ y = y ◇ y := (h x y z z).trans ((h y y z z).symm)
      exact congrArg (fun t => t ◇ ((z ◇ z) ◇ z)) hxy
    _ = z ◇ (y ◇ y) := (h z (y ◇ y) z z).symm
```

### Result

- **Solved**: Yes
- **LLM calls**: 1 (after 16 deterministic strategies failed)
- **Judge calls**: 17
- **Time**: 87.4 seconds

The mining-sweep sweet spot: deterministic strategies cover the easy bulk, and when they fall short, the solver's structural analysis (constancy, near-miss, useful instantiations) feeds the LLM enough context to nail the proof on the first try — the pattern emerging autonomously during live mining rather than from a hand-crafted prompt.

---

## Summary: Demo Comparison

| Demo | Model | Strategy | LLM Role |
|------|-------|----------|----------|
| `baseline` | OpenRouter default | Brute-force + singleton + generic LLM fallback | Generic — retries with error feedback |
| `oss_twophase` | gpt-oss-120b | Deeper search + two-phase LLM | Structured — analysis phase, then implementation |
| `oss_opnorm` | gpt-oss-120b | 16 deterministic strategies + structural-context LLM | Flagship — fed constancy / near-miss / instantiation analysis |

## Key Takeaways for Contestants

1. **Deterministic strategies first**: Counterexample search on Fin 2-7 solves most false problems. Singleton detection, library matching, and transitive chains solve many true problems. No LLM needed.

2. **The prompt matters more than the solver loop**: The difference between `baseline` (generic prompt, several LLM rounds for a simple problem) and `oss_opnorm` (specialized prompt with solver-side structural analysis, often one LLM round for a hard problem) is largely in the prompt template and the structural context it receives.

3. **Judge feedback is free information**: Each judge error is automatically included in `{history.attempts}`. Design your prompt to help the LLM learn from these errors.

4. **Solver context is your secret weapon**: The `{solver.*}` placeholders let you pass arbitrary analysis to the LLM. The more structural information you compute deterministically (constancy, BFS near-misses, useful instantiations), the better the LLM performs.

5. **Budget awareness**: Each problem has a wall-clock budget (3600s in the Stage 2 reference config — tuned for multi-round LLM loops under `reasoning_effort=medium`; subject to refinement from community feedback) and a per-call `max_output_tokens` cap on LLM responses (65536 by default) — there is **no per-problem cap** on the number of judge or LLM calls. Deterministic judge calls are cheap (~1s); LLM calls are expensive (~20s). Spend deterministic judge calls freely to try patterns; pace your LLM calls so you don't burn the wall-clock before trying the promising strategies.
