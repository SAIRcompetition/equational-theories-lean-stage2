# Tutorial: Marathon Track

The Marathon track gives one solver process a **batch of N problems and a single shared global budget** (time + tokens), then asks "how many can you solve before the budget runs out?" — instead of running one isolated subprocess per problem like the Solo track. The strategic surface is different: triage, cross-problem caching, and budget allocation become first-class.

This tutorial walks through three concrete walkthroughs and ends with a side-by-side comparison of every demo solver. For Solo-track examples see [`../solo/TUTORIAL.md`](../solo/TUTORIAL.md). For the protocol details see [`../../docs/marathon_mode.md`](../../docs/marathon_mode.md).

## Running the Demos

Set up the environment first (`bash scripts/setup.sh` if not done yet) then:

```bash
source .env.judge

# baseline: brute-force only, no LLM. Useful as a sanity floor.
python3 scripts/run_marathon.py \
  --solver examples/marathon/demos/baseline \
  --manifest tests/marathon_fixtures/manifests/normal_5.jsonl \
  --budget-seconds 60 --budget-tokens 0

# triage: difficulty-sorted LLM Pass B + budget-aware Pass C deeper-thought retry on Pass-B no-shows.
python3 scripts/run_marathon.py \
  --solver examples/marathon/demos/triage \
  --manifest tests/marathon_fixtures/manifests/normal_5.jsonl

# fewshot: in-run lemma cache + relevance-ranked few-shot prompt.
python3 scripts/run_marathon.py \
  --solver examples/marathon/demos/fewshot \
  --manifest tests/marathon_fixtures/manifests/normal_5.jsonl
```

Marathon LLM calls go through a per-run local HTTP proxy at `127.0.0.1:<port>` — the upstream key (`OPENROUTER_API_KEY` / `OPENAI_API_KEY` / `DEEPSEEK_API_KEY`) is held by the runner and never reaches the solver subprocess. Set the upstream variable in your shell before launching; the runner refuses to start a proxy without one.

The default budgets are derived from a per-problem reference (600 s /
65 536 tokens — see `REF_PER_PROBLEM_*` in `scripts/run_marathon.py`,
deliberately decoupled from Solo's 3600 s for dev-loop practicality)
multiplied by `N × compression_ratio = N × 0.5`:

```
budget_seconds = compression_ratio × N × ref_seconds_per_problem
budget_tokens  = compression_ratio × N × ref_tokens_per_problem
```

Override with `--compression-ratio 1.0` (no compression — every problem at the per-problem reference cost) or with explicit `--budget-seconds` / `--budget-tokens`.

A submission is one file: `solver.py`, ≤500 KB. The marathon runner sets `JUDGE_MARATHON_MANIFEST` in the env when launching; the solver should read that JSONL of problems, append answers to `JUDGE_MARATHON_OUTPUT`, and exit. When the env var is absent, the same file should fall back to the Solo stdin/stdout protocol — one file, two modes. See [`../../docs/marathon_mode.md`](../../docs/marathon_mode.md) for the full env contract.

The three Marathon demos under `examples/marathon/demos/` form a learning ladder:

- `baseline` — no LLM; brute-force counterexample search on Fin 2..3 across every problem. The free-yield floor.
- `triage` — gpt-oss-120b; difficulty-sorted Pass B + budget-aware Pass C deeper-thought retry on Pass-B no-shows on Pass-B failures. Entry-level LLM-using marathon solver.
- `fewshot` — gpt-oss-120b; in-run lemma cache + few-shot transfer (a submitted proof becomes prompt context for later problems). Marathon-only strategy — cross-problem state is structurally impossible in Solo.

---

## Walkthrough 1: Free Counterexample Harvest (`baseline`)

**Manifest**: `tests/marathon_fixtures/manifests/normal_5.jsonl` (5 problems sampled from `normal.jsonl`).

**Model**: none — pure brute-force.

### What happens

The baseline solver enumerates every Cayley table on Fin 2 and Fin 3 for each problem, checks whether the table satisfies law A (the hypothesis) but violates law B (the goal), and submits the table as a `verdict: false` certificate when it finds one. The Lean side compiles the table into a `Magma (Fin n)` and discharges the goal via `decideFin!` — finite case-split, so verification is decidable and fast.

For roughly **40-50% of `normal`-distribution problems**, a small Cayley table works. Those are zero-token wins available to every solver before the LLM is even consulted.

### Run output

```
Marathon Run
  Solver:       baseline
  Manifest:     normal_5.jsonl (N=5)
  Budget:       60s wall, 0 tokens (compression_ratio=0.5 × 5 × 600s/65536tok)

Solver exited rc=0 wall=1.0s sigterm=False sigkill=False

=== Result ===
  Score:         1 / 5
  Attempted:     1
  Not attempted: 4
  By status:     {'not_attempted': 4, 'accepted': 1}
  Wall used:     1.0s of 60s budget
  Tokens used:   0 of 0 budget
```

`normal_0003` got a `Fin 2` table; the other four problems are likely true implications and are reported as `not_attempted` — the baseline never tries to *prove* anything, so it leaves them blank rather than guessing. In Marathon scoring, `not_attempted` and a wrong answer both score zero, so guessing has no upside.

### Why this is the right floor

Anything better than the baseline must do at least one of:

1. **Search wider** — try Fin 4 / Fin 5, or non-table-shaped counterexamples.
2. **Prove implications** — actually attempt the `verdict: true` problems.
3. **Both, with budget discipline** — neither (1) nor (2) is free, and the budget is shared across all N problems.

The remaining walkthroughs all start with the same brute-force pass, then layer different strategies for spending the LLM budget on whatever the brute-force pass left behind.

---

## Walkthrough 2: Triage + Deeper-thought Retry (`triage`)

**Manifest**: `tests/marathon_fixtures/manifests/normal_5.jsonl`.

**Model**: `openai/gpt-oss-120b` via `deepinfra/bf16`. Two LLM passes — a low-effort first pass over difficulty-sorted survivors, and a higher-effort retry pass on the problems Pass B left without any submission, *only if budget remains*.

### What happens

The solver runs the Pass A brute-force harvest first (same as `baseline`). For everything the brute-force pass leaves unsolved, Pass B sorts the survivors by an estimated-difficulty heuristic (variable count, term depth, constancy hints) and asks the LLM for a Lean tactic body **cheap-first** — the easy-looking ones get spent on first while the budget is still healthy. Pass C then re-attempts only the **Pass-B no-shows** (parse fails, empty bodies, LLM errors, missing counterexamples) with a higher `reasoning_effort` and a larger output cap, but **only fires if `tokens_used < cap_tokens − pass_c_reserve / 2`** (where `pass_c_reserve = PASS_C_MIN_BUDGET_FRACTION × cap_tokens`, default 10 %). Pass-B successes are deliberately *not* retried — marathon scoring is last-write-wins and there is no in-run judge feedback, so retrying a working answer with the same prompt risks overwriting it with a worse one.

The marathon helper enforces token budget at the call site: if the next call's `prompt_tokens + max_output_tokens` would exceed `budget_tokens − tokens_used`, the helper returns an `error` shape instead of contacting upstream, and the solver moves on. Both Pass B and Pass C use the helper the same way — Pass B with `reasoning_effort=low` and `max_output_tokens=8192`, Pass C with `reasoning_effort=high` and a doubled `max_output_tokens` so harder problems get more compute on their second look. (The exact Pass C value lives in `examples/marathon/demos/triage/solver.py`; bump it locally if your budget allows.)

### Solver-side contract

Every marathon solver imports the proxy helper:

```python
import os, sys
sys.path.insert(0, os.environ["JUDGE_MARATHON_LIB_DIR"])
from marathon_llm import call_llm

resp = call_llm(prompt, config={
    "model": "openai/gpt-oss-120b",
    "provider": "deepinfra/bf16",
    "max_output_tokens": 8192,
    "temperature": 0.0,
    "reasoning_effort": "low",
})
if "error" in resp:
    # token budget exhausted, upstream error, etc — skip and continue
    continue
text = resp["response"]              # the model's reply
spent = resp["tokens_used_call"]     # this call's cost
left  = resp["budget_remaining"]     # budget after this call
```

`call_llm` is the only blessed way to reach the LLM, but solvers that prefer the OpenAI SDK directly still go through the same proxy because that's the only LLM endpoint reachable from the solver's network env. Either route is metered identically.

### Why difficulty-sort matters

On the `normal` distribution (the Marathon reference set), the easiest 30-40% of LLM-eligible problems consume ~10-20% of per-call tokens; the hardest 10% can consume 40-60% of a single call's budget on `reasoning_effort=low` alone. If you walk the manifest in input order, a single hard problem early in the queue can drain the budget before the cheap wins are even attempted. Sorting by an estimated-difficulty heuristic peels off the easy wins first and pushes the budget-busters to the end where running out of tokens is just a graceful skip.

Pass C is the deliberate counter-balance: cheap-first ordering plus low effort can leave a problem unsolved that medium effort would have nailed. Re-attempting only the misses, only when budget remains, recovers most of those without doubling per-problem cost across the board.

---

## Walkthrough 3: Marathon-Distinctive Strategy (`fewshot`)

`fewshot` implements a strategy **only Marathon mode makes possible**: it uses cross-problem state — patterns that worked on earlier problems become prompt context for later ones. This is structurally impossible in Solo, where each problem gets its own subprocess and its own LLM context window.

### In-Run Lemma Cache + Few-Shot Transfer

Whenever the solver submits a `verdict: true` answer, it appends the `(problem, proof_body)` pair to an in-memory `fewshot_pool`. For every subsequent unsolved problem, it ranks the pool by relevance (variable-set overlap, length similarity), takes the top `K = 2`, and prepends them to the prompt as worked examples:

```
You are solving an equational-theory implication in Lean 4.

Here are 2 worked examples from this same run:

Example 1: Equation608 → Equation593
  exact h x y z (h y z y x).symm
  -- ...

Example 2: Equation472 → Equation101
  intro x y; rw [h x y, h y x]
  -- ...

Now solve:
  Law A (Equation919): x = y ◇ ((y ◇ y) ◇ (y ◇ x))
  Law B (Equation872): ...
```

Why this is Marathon-only: in the Solo track each problem gets its own subprocess and its own LLM context window. There's no shared in-memory state for "what just worked five problems ago", and the proxy doesn't surface other problems' transcripts across subprocesses. In Marathon the solver *is* the long-lived process across all N problems, so submitted patterns naturally accumulate.

The same submitted answers are also persisted to `<scratch>/proof_lib.jsonl` for post-mortem inspection — useful for debugging and for catalog-building, though scratch is wiped at the next run, so this is not a cross-run cache (Marathon explicitly forbids that — see `anti_persist` in the harness).

**Caveat (and a fork-target).** The pool is populated as soon as the solver *submits* an answer, not when the judge *accepts* it. The judge runs after the solver exits, so a hallucinated proof that looks plausible can enter the pool and degrade later prompts. A stricter fork can spawn `lake env lean` inside the sandbox to self-validate each candidate before insertion, at the cost of a few seconds per check. Marathon explicitly allows this (see `../../docs/marathon_mode.md` § "What the solver may do").

### Where to take this next

`fewshot` is a starting point, not a finished product. Natural directions to fork it:

- **Prompt-context engineering** — tune the few-shot relevance score, raise `K`, swap variable-set overlap for a richer feature (term shape, constancy patterns, ID-pair distance in the equation graph).
- **Budget allocation across passes** — combine cross-problem state with non-uniform per-problem effort: a low-effort first pass to seed the pool, then a higher-effort second pass that consumes the pool as few-shot context. Marathon's shared global budget is what makes this expressible.
- **Self-validation before insertion** — spawn `lake env lean` to check candidates and only admit accepted proofs into the pool, at the cost of a few seconds per insert.

---

## Summary: Marathon Demo Comparison

| Demo          | LLM | Strategy                                                                | Marathon-distinctive? |
| ------------- | --- | ----------------------------------------------------------------------- | --------------------- |
| `baseline`    | no  | brute-force counterexample only                                         | no — same as a Solo brute-force solver run sequentially |
| `triage`  | yes | brute-force + difficulty-sorted Pass B + budget-aware Pass C deeper-thought retry on Pass-B no-shows | partial — a deeper-thought retry pass is feasible in Solo too |
| `fewshot` | yes | brute-force + in-run lemma cache + few-shot transfer                    | **yes** — requires cross-problem state |

## Key Takeaways for Marathon Contestants

1. **Take the free counterexamples first.** Brute-force on Fin 2..3 is essentially free and clears 40-50% of `normal`. Don't spend any LLM budget on a problem you haven't first checked for a small Cayley counterexample. Every demo here starts with this pass for that reason.

2. **Triage is the central decision.** The shared global budget means every token spent on problem A is a token not spent on problem B. Demos that decide *which* problems to attempt and *in what order* (`triage`, `fewshot`) consistently outperform a strict-sequential walk on the same budget.

3. **Watch the helper's pre-call budget gate.** `marathon_llm.call_llm` refuses any call where `prompt_tokens + max_output_tokens > budget_remaining`. If you set `max_output_tokens = 32768` on a compressed budget, **every** call gets refused before contacting upstream and your solver looks like it's hung but is actually thrashing through error-returns. The reference demos default to `max_output_tokens = 8192`; raise this only when you know the budget can absorb it.

4. **Cross-problem state is the first thing Solo can't do.** The most distinctive marathon strategies — caching prior wins as few-shot exemplars, mining a lemma library mid-run, transferring a `simp` set across problems — all rely on persistent solver state across the N problems. If you fork a Solo solver and just adapt its I/O, you've left the strategy headroom on the table.

5. **Determinism matters for the harness.** The marathon harness has a `determinism` case (run twice, scores must match). If you're seeding LLM calls (`use_seed=True, seed=0`), keep that seed stable across runs — and don't use `time.time()` or `random.random()` to break ties on equally-ranked problems, since both vary across runs.

6. **Observable I/O caps** the runner enforces, in case your solver trips one:

   - **`solver.py` ≤ 500 KB.** Submissions above this are rejected before launch.
   - **Answer JSONL ≤ 50 MB.** The runner watchdog SIGTERMs your solver (with `sigterm_reason="output"`) if the cumulative answer file exceeds this. You should never come close — per-problem `code` is already bounded by the 100 KB judge cap — but a runaway log into the answer file is still detectable.
   - **Manifest ≤ 50 MB.** Manifests above this are rejected before scoring snapshot. Organizer manifests are normally a few MB, so this is a defensive bound you shouldn't see.
   - **Stderr is drained but not preserved in full.** Only the last ~512 lines (≤1 KB each) are kept in the run summary. If you're debugging, prefer file-based logs in `JUDGE_MARATHON_SCRATCH_DIR` over `print(..., file=sys.stderr)`.

7. **`budget_tokens=0` means no LLM at all, not "unmetered".** A zero budget refuses every reservation in the proxy with HTTP 402; both the helper (`marathon_llm.call_llm`) and a direct OpenAI SDK call hit the same wall. Use `0` deliberately for brute-force-only baselines (the `baseline` demo runs this way). Negative `budget_tokens` is an unlimited dev-only sentinel and should not appear in real runs.
