# Solo Mode

> Status: production. Sister track: [`docs/marathon_mode.md`](marathon_mode.md).
> Both share `judge/verify.py` and the five-status mapping; they differ
> only in solver I/O shape and budgeting.

## Mission

The Solo track runs **one solver subprocess per problem**, each with a
fixed budget. The proxy launches `solver.py`, hands it a single problem
on stdin, reads its answer on stdout, and verifies the result via
`judge/verify.py`. Every problem starts with a clean process — no state
carries between problems. This is the foundational track most
contestants start with.

## Reference Configuration

| Knob                       | Value      | Notes                                                      |
| -------------------------- | ---------- | ---------------------------------------------------------- |
| Wall-clock per problem     | **3600 s** | `solver.timeout_seconds` in `pipeline/config.json`. Widened from earlier 600 s reference so multi-round LLM loops finish under `reasoning_effort=medium`. |
| LLM max output tokens per call | **65 536** | `llm.max_output_tokens` — per-call cap on the response length, not a problem-wide token meter. |
| Lean code size (per `code` field) | **100 KB** | `judge.max_code_length`.                            |
| False-cert payload size    | **20 KB**  | `judge.max_false_cert_bytes` (the false branch's `code`).   |
| Solver source size         | **500 KB** | `solver.py` upload limit.                                  |
| Hard kill                  | wall-clock timeout → SIGTERM → SIGKILL | Solver process group is terminated.                |

These are the **reference budgets**. Local runs may set them higher; the
official judge enforces these exact values.

## Solver Contract

Single-file submission:

```
my_submission/
└── solver.py    # Up to 500 KB. No other files.
```

Communication: **JSON messages over stdin/stdout**, one JSON object per
line. The proxy starts one solver process per problem and tears it down
when the verdict is final.

### Inbound — proxy → solver

The first line on stdin is a `start` message:

```json
{
  "type": "start",
  "problem": {"id": "normal_0001", "eq1_id": 2, "eq2_id": 387, "equation1": "...", "equation2": "..."},
  "budget": {"timeout_seconds": 3600, "max_code_length": 100000, "max_false_cert_bytes": 20000}
}
```

The solver may issue any number of `judge` and `llm` requests until it
finalises with a `submit` message. See README's
[Communication Protocol](../README.md#communication-protocol) section
for the exhaustive message catalogue (`judge`, `llm`, `submit`, plus
proxy-side responses including streaming token chunks).

### Outbound — solver → proxy

The terminal message is `submit` with the answer payload:

```json
{
  "type": "submit",
  "answer": {"verdict": "true", "code": "<full Lean source — see Answer Format>"}
}
```

`verdict` is `"true"` (prove `lhs → rhs`) or `"false"` (prove
`lhs ∧ ¬ rhs`). Both branches are certificates; the only difference is
the goal statement the proof must close. The submitted `code` is the
**full Lean source**, including imports and a `submission` term whose
type matches the judge-generated `Goal`.

### What the solver may do

- Run any computation locally up to the wall-clock budget
- Issue `judge` requests to self-verify a candidate `code` before the final `submit`
- Issue `llm` requests; the proxy renders a `PROMPT` template embedded in `solver.py` and forwards the call
- Issue any number of `llm` calls within the wall-clock budget; each call is capped at `llm.max_output_tokens` (65 536) on the output side
- Submit early; the proxy stops accepting messages after `submit`

### What the solver may not do

- Reach the network beyond the proxy
- Open files outside its own working directory + the standard sandbox FS
- Persist anything across problems (every problem is a fresh process)
- Read the judge's internal state (proof policy, allowed declarations) — only the responses to `judge` calls
- Spawn subprocesses that escape the sandbox

## Answer Format

```json
{"verdict": "true",  "code": "<full Lean 4 source>"}
{"verdict": "false", "code": "<full Lean 4 source>"}
```

The `code` field exposes a term named `submission` whose type is
definitionally equal to the judge-generated `Goal`. See README's
[Answer Format](../README.md#answer-format) section for both branches'
exact `Goal` shape, examples, and the universe note.

## Judge / Scoring — five public statuses

Every solver answer maps to **exactly one** of:

| Status              | Meaning                                                                                       |
| ------------------- | --------------------------------------------------------------------------------------------- |
| `accepted`          | Lean verified the certificate; all dependency-policy checks passed.                            |
| `unparsed`          | Raw JSON payload could not be parsed.                                                          |
| `malformed`         | Parsed JSON, but violates schema, branch rules, or size limits.                                |
| `incomplete_proof`  | Proof contains `sorry` / `admit`, or depends on a banned axiom or declaration.                 |
| `incorrect`         | Structurally valid, but Lean rejects (typecheck fail, counterexample fails, timeout, etc.).    |

Score = number of `accepted` verdicts across the problem set. There is
no partial credit and no wrong-answer penalty.

Internal infrastructure failures (missing Lean, broken fixtures,
non-determinism in the judge itself) are **harness errors**, not public
verdicts — they never collapse to `incorrect`.

## Anti-cheat / Defensive posture

| Concern                   | Defense                                                                                                  |
| ------------------------- | -------------------------------------------------------------------------------------------------------- |
| Payload smuggling         | Single-file solver contract — `solver.py` and nothing else.                                              |
| Network exfil / unmetered LLM | All LLM calls go through the proxy; the proxy holds the upstream API key and meters tokens.           |
| Per-call output cap       | The proxy passes `llm.max_output_tokens` to the upstream API; runaway generations are bounded per call.   |
| Banned axioms / declarations | Lean's `#judge_report` introspects the certificate's transitive dependency closure; mismatches → `incomplete_proof`. |
| Sandbox boundary          | Production runs the solver in a Docker sandbox (`mode: docker` in `pipeline/config.json`; image built by `scripts/setup.sh`).                             |
| Deterministic re-runs     | Same `solver.py` + same problem must produce the same verdict; the harness covers this explicitly.        |

## Resource Enforcement

- **Wall-clock**: proxy SIGTERMs the solver process group at the
  per-problem deadline; SIGKILL after grace.
- **LLM tokens**: counted by the proxy from upstream `usage`. A call
  that would exceed the remaining budget is refused (`{"error": "..."}`)
  rather than silently truncated. Solvers can read the running total
  from each `llm` response.
- **Code size**: enforced at `judge` request boundary — oversize `code`
  returns `malformed`.

## Sandbox Python environment

The sandbox image is `python:3.11-slim` plus a small approved set of
third-party packages (versions pinned in `Dockerfile`):

| Package | Version  | Purpose                                                                    |
|---------|----------|----------------------------------------------------------------------------|
| `sympy` | `1.13.3` | Symbolic algebra — term parsing, substitution, equation normalization.     |

The standard library is otherwise the only thing available — no
`numpy`, `z3`, `networkx`, etc. A solver that imports an unlisted
package will fail at runtime with `ModuleNotFoundError` in production.
Open an issue with the use case to request additions
(`CONTRIBUTING.md`).

## Implementation map

| File                           | Role                                                                              |
| ------------------------------ | --------------------------------------------------------------------------------- |
| `pipeline/proxy.py`            | Launches solver, mediates stdin/stdout, fills `PROMPT` template, forwards LLM, enforces budgets. |
| `pipeline/runner.py`           | Batch entry point — runs the proxy over a problem set and aggregates results.      |
| `pipeline/config.json`         | Reference budgets (`solver.timeout_seconds`, `llm.max_output_tokens`, `judge.max_code_length`, …). |
| `judge/verify.py`              | Deterministic Lean verifier — the same `verify_answer` function both tracks call.  |
| `scripts/run_harness.py`       | Canonical Solo harness — green gate for any judge/proxy change.                    |
| `scripts/submit.py`            | Interactive CLI for one-off solver runs (colorized).                               |

## Harness Coverage

`scripts/run_harness.py` runs every case in `tests/harness_manifest.json`
plus the adversarial cases in `tests/challenger_manifest.json`. Required
coverage (per CLAUDE.md):

- Accepted true-cert and false-cert cases
- `unparsed`, `malformed`, `incomplete_proof`, `incorrect` mappings
- Banned-axiom and banned-declaration regressions
- Wrong-proof and wrong-counterexample cases
- Determinism re-runs on representative accepted and rejected cases
- Challenger sweep covering smuggled axioms / smuggled theorem deps

When the harness exits 0 the implementation matches the public 5-status
contract.

## Non-goals (explicit)

- No human review; no LLM-as-judge
- No partial credit
- No persistent state across problems
- No multi-solver collaboration (one `solver.py` per submission)
- No new public statuses beyond the five above
