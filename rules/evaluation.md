# Stage 2 Evaluation Setup

> **We want your feedback.** The evaluation plan described below — including the model, configuration, scoring rules, and problem sets — is still being refined, and items marked **TBD** will be decided based on community input. Please share suggestions on the [SAIR Foundation Zulip](https://zulip.sair.foundation/).

This page specifies how Stage 2 submissions are evaluated: submission format, solver environment, budget, scoring, proof policy, and the evaluation model.

For the high-level task description, key dates, and participation policy, see **[overview.md](overview.md)**.

## Submission Format

A Stage 2 submission is **a single Python file**.

| File | Purpose | Size limit |
|------|---------|------------|
| `solver.py` | The solving program for both tracks. Must contain all solving logic, including any prompt text as an in-file constant. The I/O protocol depends on the track (see below). | **500 KB** |

The solver is a free-form Python program. No required function signatures — the only requirement is following the I/O protocol of the chosen track.

If the solver uses LLM calls in **Solo**, it declares its prompt template as a top-level `PROMPT = "..."` string literal; the proxy extracts it via static AST parsing (the module is never imported or executed on the host), fills `{placeholder}` variables, and queries the LLM. In **Marathon**, the solver makes LLM calls itself via the helper `from marathon_llm import call_llm` (or any OpenAI-SDK call) against a local HTTP proxy; no template extraction.

## Tracks

Stage 2 has two tracks. Both share the same judge, the same five-status verdict mapping, and the same single-file `solver.py` contract (≤ 500 KB). They differ only in I/O shape and budgeting:

| Track | Workload per process | Budget | I/O |
|-------|----------------------|--------|-----|
| **Solo** | One problem per solver subprocess | Fixed per-problem | stdin (problem JSON) / stdout (answer JSON) |
| **Marathon** | N problems per solver subprocess (reference N=100) | Single global budget = `compression_ratio × N × Solo per-problem` (default `compression_ratio = 0.5`) | manifest JSONL in / append-only JSONL out |

One solver source can support both. Full specs: `docs/solo_mode.md` and `docs/marathon_mode.md` in the repository.

## Solver Environment

The solver runs in an isolated subprocess:

- **No secrets**: no inherited API keys or environment variables beyond a minimal allowlist (`PATH`, `HOME`, `LANG`, etc.)
- **No direct network**: the internet is reachable only through the organizer-provided proxy
- **LLM access**: through the proxy — Solo via stdin/stdout JSON, Marathon via a local-only HTTP endpoint that authenticates with a per-run shared secret and meters tokens against the global budget
- **Judge access**: through the proxy — Solo via stdin/stdout JSON, Marathon via append-only JSONL output that the runner scores at end of run

```
Solver (subprocess) <--track-specific protocol--> Proxy <---> Judge (Lean verification)
                                                        <---> LLM (OpenAI-compatible API)
```

## Solver Budget

Reference values in `pipeline/config.json`. Numbers may still be tuned during Stage 2 based on community feedback.

**Solo (per problem):**

| Resource | Reference value | Notes |
|----------|-----------------|-------|
| Wall-clock timeout | 3600 seconds | Excludes organizer-side LLM latency. |
| LLM max output tokens per call | 65536 | Per-call cap on the LLM response length. |
| Submitted Lean code | 100 KB | Per-call code size cap. |

**Marathon (per run, N problems):**

The global budget is derived from Solo's per-problem reference:

| Resource | Formula | Default at N=100 |
|----------|---------|------------------|
| Wall-clock | `compression_ratio × N × 3600 s` | 180 000 s (50 h) at `0.5` |
| Tokens | `compression_ratio × N × 65536` | ~3.3 M at `0.5` |

`compression_ratio` defaults to `0.5` — the solver cannot finish all N at single-problem cost and must triage. Setting it to `1.0` removes compression; smaller values squeeze harder.

The solver manages its own pacing within the budget. Deterministic strategies cost no tokens. Exceeding the wall-clock or token budget terminates the solver.

## Answer Format

For each problem, the solver submits a proof certificate via a judge call:

```json
{"call": "judge", "verdict": "true", "code": "<Lean code>"}
```

or

```json
{"call": "judge", "verdict": "false", "code": "<Lean code>"}
```

- **True certificate**: a Lean 4 proof that the hypothesis equation implies the goal equation.
- **False certificate**: a Lean 4 proof that there exists a finite magma satisfying the hypothesis but not the goal.

Both are verified by the deterministic Lean judge. The judge returns exactly one of the following statuses:

| Status | Meaning |
|--------|---------|
| `accepted` | Certificate verified successfully |
| `unparsed` | Raw JSON could not be parsed |
| `malformed` | JSON parsed but violates schema |
| `incomplete_proof` | Proof uses `sorry`, `admit`, or disallowed axioms/declarations |
| `incorrect` | Proof is structurally valid but does not verify in Lean |

A problem is solved when the judge returns `accepted`.

## Scoring

**TBD.** Final scoring rules (point assignment, aggregation across problems, and tiebreakers) are still being decided based on community feedback. The baseline intent is: a problem is solved when the judge returns `accepted`, and higher solved counts are better.

## Proof Policy

Submitted proofs are checked against a dependency policy:

- **Allowed trusted axioms**: `propext`, `Quot.sound`, `Classical.choice`
- **Allowed declarations**: configurable allowlist per problem (when specified)
- Proofs using `sorry`, `admit`, or disallowed axioms/declarations are rejected as `incomplete_proof`.

## Evaluation Model

**TBD.** The evaluation model — including the model family, provider, and routing — is still being decided. The current candidate under consideration is an open-weight model accessed via OpenRouter with a pinned provider route and deterministic settings (seeded, low temperature), but this is subject to community feedback.

## Evaluation Configuration

**TBD.** Final generation parameters (temperature, max output tokens, reasoning effort, seeding, provider fallback policy) will be published alongside the confirmed evaluation model. Whatever settings are finalized will be reflected in `pipeline/config.json` in the repository.

## Evaluation Problem Sets

**TBD.** The private Stage 2 evaluation set (size, composition, balance between true/false implications) is still being decided. The set is **separate** from any public problem sets.

For development, participants can use:

- Problems from the Equational Theories Project and the Stage 1 public subsets.

The organizer runs offline evaluation on the private evaluation set.

## Official Repository

The official GitHub repository for Stage 2:

- [https://github.com/SAIRcompetition/equational-theories-lean-stage2](https://github.com/SAIRcompetition/equational-theories-lean-stage2)

This repository includes:

- the evaluation pipeline (proxy, runner, judge)
- demo solvers organized by track under `examples/{solo,marathon}/demos/` (Solo: `baseline/`, `oss_twophase/`, `oss_opnorm/`; Marathon: `baseline/`, `triage_oss/`, `fewshot_oss/`)
- a step-by-step tutorial per track (`examples/solo/TUTORIAL.md`, `examples/marathon/TUTORIAL.md`)
- local testing support via `scripts/run_harness.py` (Solo) and `scripts/run_marathon_harness.py` (Marathon)

## Local Testing

The repository supports full local testing before submission. A typical workflow:

1. Run `bash scripts/setup.sh` (one-time environment setup).
2. Source the environment: `source .env.judge`.
3. Study the demo solvers (start with `examples/solo/demos/baseline/`) and read `examples/solo/TUTORIAL.md` for annotated walkthroughs. For the Marathon track, see `examples/marathon/TUTORIAL.md`.
4. Test your solver locally, for example:
   ```bash
   python3 -m pipeline.runner \
     --submission examples/solo/demos/baseline \
     --problems examples/problems/sample_20.json
   ```
5. Review results in `pipeline/results/`.
6. Iterate — improve deterministic strategies first, then refine your prompt.
7. Submit only after your solver is stable locally.
