# Marathon Mode

> Status: implemented and harness-covered (`scripts/run_marathon_harness.py`).
> Sister track: see [`docs/solo_mode.md`](solo_mode.md). Solo and Marathon
> share the judge (`judge/verify.py`) and the five-status mapping; they
> differ only in solver I/O shape and budgeting.

## Mission

Add a second competition track to this judge: instead of one solver
subprocess **per problem**, hand the solver a **batch of N problems with
a single global budget** and let the solver decide how to spend it. This
rewards triage, cross-problem caching, and prompt-context reuse —
complementary to the Solo track (one subprocess per problem, fixed
per-problem budgets), which is preserved unchanged.

## Reference Configuration

The two global budgets are derived from a per-problem reference,
multiplied by the manifest length `N` and the tunable knob
**`compression_ratio`**:

```
budget_seconds = compression_ratio × N × ref_seconds_per_problem
budget_tokens  = compression_ratio × N × ref_tokens_per_problem
```

The Marathon reference per-problem values are **600 s / 65 536 tokens**,
defined as `REF_PER_PROBLEM_SECONDS` / `REF_PER_PROBLEM_TOKENS` in
[`scripts/run_marathon.py`](../scripts/run_marathon.py). These are
deliberately decoupled from Solo's `solver.timeout_seconds` (3600 s in
`pipeline/config.json`) so the Marathon dev-loop wall-clock stays
practical; the long-form Solo budget would push a single 100-problem
Marathon run beyond a development day even at compression 0.5.

`compression_ratio < 1` compresses the global budget below the
fair-share total, forcing triage. `compression_ratio = 1.0` means no
compression — the solver gets enough budget to attempt every problem at
the per-problem reference cost. The reference value is **`0.5`**.

| Knob               | Value                                  | Notes                                                              |
| ------------------ | -------------------------------------- | ------------------------------------------------------------------ |
| N                  | 100                                    | First 100 lines of `examples/problems/normal.jsonl` (no shuffle).  |
| `compression_ratio` | **0.5**                               | Reference. Configurable via `--compression-ratio` on the CLI.       |
| Time budget        | 0.5 × 100 × 600 s = **30 000 s (≈ 8.3 h)** | Derived; can be set explicitly with `--budget-seconds`.        |
| Token budget       | 0.5 × 100 × 65 536 = **3 276 800 tokens** | Derived; can be set explicitly with `--budget-tokens`. Counted by the marathon proxy at the network layer. |
| Concurrency        | Solver-controlled                      | Runner only enforces the two budgets.                              |
| Manifest source    | `examples/problems/normal.jsonl[:100]` | Fixed slice; no shuffle for MVP.                                   |
| Hard kill          | SIGTERM at budget, SIGKILL 5 s later   | Output JSONL frozen at SIGTERM time.                               |

Why default to 0.5: triage must be load-bearing. At
`compression_ratio = 1.0` a sequential solver could plausibly attempt
every problem at Solo-equivalent budget and the track collapses back
into "Solo run N times in series"; at 0.5 the solver must pick.

## Solver Contract

Single-file `solver.py`, same as Solo. Marathon mode is opted in **by
environment**: when `JUDGE_MARATHON_MANIFEST` is present, the solver
should read that manifest and append answers to
`JUDGE_MARATHON_OUTPUT`. When the var is absent, the same file should
behave as a Solo single-problem solver (stdin → stdout). One file, two
modes.

```
JUDGE_MARATHON_MANIFEST       /abs/scratch/manifest.jsonl   read-only manifest copy
JUDGE_MARATHON_OUTPUT         /abs/answers.jsonl            append-only JSONL
JUDGE_MARATHON_BUDGET_SECONDS 30000                         global wall-clock
JUDGE_MARATHON_BUDGET_TOKENS  3276800                        global LLM tokens
JUDGE_MARATHON_SCRATCH_DIR    /abs/scratch                  wiped each run
JUDGE_MARATHON_LIB_DIR        /abs/repo/pipeline            on PYTHONPATH; provides marathon_llm
OPENAI_BASE_URL               http://127.0.0.1:<port>/v1    marathon proxy (only LLM endpoint reachable)
OPENAI_API_KEY                <per-run shared secret>        proxy auth; NOT a real upstream key
```

`JUDGE_MARATHON_MANIFEST` points at a **runner-owned copy** of the
manifest under the scratch dir, not at the original on-disk file.
Scoring uses an in-memory snapshot taken before the solver starts, so a
solver that overwrites this file cannot affect the score.

### Manifest format

JSONL, one problem per line, existing schema (`id`, `eq1_id`, `eq2_id`,
`equation1`, `equation2`, optional `answer`).

### Output format

JSONL, append-only, one entry per attempted problem:

```json
{"id": "normal_0042", "verdict": "true", "code": "import JudgeProblem\n\ndef submission : Goal := by\n  intro G _ h\n  exact rfl"}
```

The `code` field is the same Lean source the Solo `verify_answer`
expects — *full file contents* including imports and the `def submission`
declaration, not just a tactic body.

Solver appends as it solves. Late writes (after budget exhausted) may
land on disk but are ignored at scoring. Multiple lines for the same
`id` → last one wins; explicit by harness rule.

### What the solver may do

- Read the manifest in any order
- Decide which problems to attempt and in what sequence
- Allocate any per-problem time slice
- Reuse computation across problems (lemma library, prompt patterns, prior LLM context)
- Run `lake env lean` inside the sandbox to self-validate before submitting (same allowance as Solo)
- Write debug / cache to `JUDGE_MARATHON_SCRATCH_DIR`; harness ignores its contents
- Call the marathon proxy via `from marathon_llm import call_llm` (recommended) or directly with the OpenAI SDK — both routes hit the same proxy and are metered identically

### What the solver may not do

- Reach the network beyond the marathon proxy (only `127.0.0.1:<port>` is wired up; raw upstream keys are not in the env)
- Persist anything across runs (scratch dir is wiped each run)
- Spawn parallel solver processes outside the sandbox
- Mutate the runner-owned manifest copy expecting scoring to follow

## Judge / Scoring

After the solver exits (cleanly or via SIGTERM/SIGKILL):

1. Read every line of the output JSONL.
2. For each `id`, take the last submitted entry.
3. Run the Solo `verify_answer` against the matching manifest entry **from the in-memory snapshot** (not from disk).
4. **Score = number of `accepted` verdicts.** Tiebreak: lower wall-clock used wins.

The five Solo statuses still apply per submitted answer. A problem with
no submitted answer is reported as `not_attempted` in the per-run
summary but is **not a public verdict** — `not_attempted` never appears
in `verify_answer` output.

No partial credit. No wrong-answer penalty in the MVP — a failed attempt
and a skipped problem both score 0.

## Anti-cheat / Defensive posture

Marathon mode mirrors the Solo defensive posture (`pipeline/proxy.py`)
with shape-appropriate mechanisms:

| Concern                        | Defense                                                                                              |
| ------------------------------ | ---------------------------------------------------------------------------------------------------- |
| Payload smuggling              | Single-file solver contract — `solver.py` and nothing else (same rule as Solo). Solver source is rejected pre-launch above 500 KB (`SOLVER_MAX_BYTES`). |
| Network exfil / unmetered LLM   | Real upstream keys (`OPENROUTER_API_KEY` etc.) are **not** in the solver env. The runner starts a local HTTP proxy on `127.0.0.1:<random>` and sets `OPENAI_BASE_URL` / `OPENAI_API_KEY` (per-run secret) to point the solver there. The proxy holds the upstream credentials. |
| Token budget bypass             | The proxy itself is the authoritative source of truth for the running total — held in process memory under `threading.Lock`, advanced by the proxy as it observes upstream `usage`. The runner watchdog reads it via the proxy handle, never via a file the solver could touch. The proxy refuses (HTTP 402) once `BUDGET_TOKENS` is reached, including pessimistic char-based fallback when no upstream `usage` is returned. A solver writing its own `tokens_used.txt` has no effect (`token_tamper_inert` regression). |
| Manifest mutation               | Runner snapshots the manifest in memory before launching, hands the solver a writable copy under scratch, and scores against the snapshot. Overwriting the on-disk manifest does not affect scoring. |
| Wall-clock evasion / fork-bomb  | Solver runs in its own session/process group (`start_new_session=True`); SIGTERM at budget and SIGKILL after 5 s grace reach descendants too. |
| Cross-run persistence           | Scratch dir is wiped at run start (verified by `anti_persist` harness case).                          |
| Output replay / late writes     | Output JSONL read **once** at end; late writes may land on disk but are graded last-write-wins and the timing watchdog has already cut. |
| Output / manifest disk floods   | Runner watchdog SIGTERMs (`sigterm_reason="output"`) when the answer file exceeds 50 MB; manifests above 50 MB are refused before launch. Caps are deliberately generous — legitimate manifests are a few MB and answer JSONL is per-problem-bounded by the 100 KB Lean code cap. |
| Stderr OOM                     | Runner drains stdout/stderr through bounded ring buffers (`maxlen=512` lines, 1 KB per-line truncation); a solver streaming gigabytes of stderr no longer grows the runner's RSS. |
| Sandbox boundary                | Solver runs in the existing Solo Docker sandbox — same filesystem and network constraints.            |

## Resource Enforcement

- **Wall-clock**: runner watchdog SIGTERMs the solver process group at
  `BUDGET_SECONDS`, SIGKILL after 5 s grace.
- **Tokens**: every LLM call goes through `pipeline/marathon_proxy.py`.
  The proxy uses a **reserve → forward → settle** pattern under
  `threading.Lock`: on entry it reserves a pessimistic estimate
  (prompt-char estimate + clamped `max_tokens`), forwards the call,
  then settles with `max(observed_usage, reservation)` once upstream
  responds. Upstream errors still settle with the reservation as the
  billing floor, so a solver cannot mine free attempts by triggering
  upstream failures (`upstream_failure_bills_reservation` regression).
  Calls past `BUDGET_TOKENS` get HTTP 402 before forwarding. Multipart
  prompts (OpenAI's `list[{"type": ..., ...}]` content shape) are
  walked end-to-end; non-text parts are rejected with HTTP 400
  (`multipart_prompt_charged_correctly` regression).
- **`budget_tokens` semantics** — three branches:
  - `budget_tokens > 0` (normal): finite cap. Both proxy reservation
    and runner watchdog enforce it.
  - `budget_tokens == 0`: deny-all. The proxy refuses every reservation
    with HTTP 402; the helper-side `marathon_llm.call_llm` short-circuits
    before even reaching the proxy. A solver that bypasses the helper
    and calls the OpenAI SDK directly still hits the 402 wall
    (`zero_token_budget_rejects_llm` regression).
  - `budget_tokens < 0`: unlimited. Proxy disables the cap; runner
    watchdog never fires on tokens. Reserved for development.
- **Watchdog uses settled-only**: the runner SIGTERMs on
  `tokens_settled >= BUDGET_TOKENS`, *not* on the
  reserved-plus-settled effective total. A solver holding a large
  reservation while sleeping does not trip the watchdog from
  reservation pressure alone (`watchdog_uses_settled_only` regression).
- **Pre-call headroom check**: `marathon_llm.call_llm` refuses calls
  where `tokens_used + estimated_prompt + max_tokens > budget_tokens`
  before contacting the proxy, so a solver that asks for 32 K
  `max_tokens` on a 10 K-remaining budget short-circuits cleanly
  rather than getting half-way through a forwarded call and trapped
  on a 402.
- The two budgets are independent; whichever hits first triggers the
  corresponding cutoff.

## Harness Coverage

`scripts/run_marathon_harness.py` runs every case in
`tests/marathon_manifest.json`. Current cases:

End-to-end & status mapping:

1. `baseline_smoke` — sequential solver against a 5-problem manifest, end-to-end scoring.
2. `skip_path` — solver writes nothing → score 0, every problem `not_attempted`.
3. `partial_path` — mix of valid + invalid lines exercises status mapping.

Budget enforcement:

4. `budget_kill` — solver `time.sleep(99999)` → wall-clock SIGTERM at budget.
5. `token_kill` — solver burns tokens past budget; runner SIGTERMs with `sigterm_reason=tokens`.
6. `over_budget_call_rejected` — pre-call headroom check refuses the LLM call before the proxy reservation.
7. `zero_token_budget_rejects_llm` — `budget_tokens=0` deny-all path: both helper and direct SDK calls hit HTTP 402.
8. `watchdog_uses_settled_only` — runner watchdog ignores reservation pressure and only fires on settled tokens.
9. `multipart_prompt_charged_correctly` — list-of-parts prompts are walked end-to-end for the char estimate; non-text parts rejected.
10. `upstream_failure_bills_reservation` — proxy still bills the pessimistic reservation when the upstream call fails, blocking attack-via-failure.
11. `token_tamper_inert` — solver writes its own `tokens_used.txt`; runner ignores it.

Output safety / I/O bounds:

12. `oversized_solver_rejected` — `solver.py` above 500 KB is rejected before launch.
13. `oversized_manifest_rejected` — manifest above 50 MB is rejected before scoring snapshot.
14. `stderr_flood_bounded` — solver streams hundreds of thousands of stderr lines; runner stays bounded by the deque + per-line truncation.
15. `output_flood_killed` — solver writes 10 MB-per-line answer JSONL until SIGTERM with `sigterm_reason="output"`.

Determinism / replay:

16. `determinism` — same solver + manifest produces identical scores across two runs.
17. `anti_persist` — pre-populated stale file in scratch is not visible to the solver.
18. `late_write` — post-SIGTERM writes are graded last-write-wins (not silently dropped).
19. `duplicate_id` — multiple lines for the same `id`; last real cert is graded.
20. `manifest_mutation` — solver overwrites the scratch manifest; scoring ignores the overwrite (uses the in-memory snapshot).

Key isolation:

21. `key_isolation` — solver env probe: confirms raw upstream keys are absent and `OPENAI_BASE_URL` is loopback.

When the harness exits 0 every documented marathon behaviour is covered.

## Implementation map

| File                                                | Role                                                                                |
| --------------------------------------------------- | ----------------------------------------------------------------------------------- |
| `pipeline/marathon_runner.py`                       | Manifest snapshot, scratch lifecycle, env injection, proxy lifecycle, dual-budget watchdog. |
| `pipeline/marathon_proxy.py`                        | Local HTTP proxy: shared-secret auth, OpenAI-SDK forwarding, token meter, budget 402.       |
| `pipeline/marathon_score.py`                        | Last-write-wins parser, per-line `verify_answer`, summary with `not_attempted`.            |
| `pipeline/marathon_llm.py`                          | Solver-side helper. Importable as `from marathon_llm import call_llm`.                     |
| `scripts/run_marathon.py`                           | CLI entry; runs the runner then the score path.                                            |
| `scripts/run_marathon_harness.py`                   | Regression harness, separate from `scripts/run_harness.py`.                                |
| `examples/marathon/demos/baseline/`     | Sequential, no LLM; brute-force reference baseline.                                              |
| `examples/marathon/demos/triage/`   | Difficulty-sorted Pass B + budget-aware Pass C deeper-thought retry on Pass-B no-shows (entry-level LLM).  |
| `examples/marathon/demos/fewshot/`  | In-run lemma cache + few-shot transfer (cross-problem state — Marathon-only strategy).           |
| `tests/marathon_manifest.json` + `tests/marathon_fixtures/` | Harness cases and fixture solvers.                                                            |

## Non-goals (explicit)

- No change to Solo reference budgets in `pipeline/config.json`
- No change to `verify_answer` or the 5-status mapping
- No persistent solver state across runs
- No multi-solver collaboration (one solver per submission, same as Solo)
- No new public-status values (`not_attempted` is a *summary* notation, not a public verdict)
