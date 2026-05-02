# Mathematics Distillation Challenge — Equational Theories — Stage 2

> Official competition page:
> <https://competition.sair.foundation/competitions/mathematics-distillation-challenge-equational-theories-stage2/overview>

## Background

The pilot task is **equational implication over magmas** (a set with
one binary operation `◇`): given two laws `E₁` and `E₂`, decide whether
`E₁ ⇒ E₂` holds across **every** magma.

This challenge is based on the [Equational Theories Project](https://teorth.github.io/equational_theories/),
initiated by Terence Tao:

- Raw implication graph: [export_raw_implications](https://teorth.github.io/equational_theories/implications/)
- Law list — 4694 laws of order ≤ 4: [equations.txt](https://github.com/teorth/equational_theories/blob/main/data/equations.txt)
- Larger law list of order 5 used by Stage 2: bundled at [`examples/problems/eq_size5.txt`](examples/problems/eq_size5.txt) (~62 K laws)

Example: `E_4: x = x * y` implies `E_3: x = x * x`.

Stage 1 asked models for a yes/no answer. **Stage 2 raises the bar**:
every answer must come with a machine-verifiable Lean 4 certificate —
a proof for true implications, or a finite magma witness where the
hypothesis holds but the goal fails. A deterministic Lean judge
accepts or rejects each answer — no partial credit, no probabilistic
scoring, no LLM-as-judge. The same judge code runs locally and at the
official evaluation: if the harness in this repo turns green for
your `solver.py`, the judge returns the same verdict in production.

The submission is a single `solver.py`. The competition runs **two
tracks** with shared judging but different solver shapes — pick
whichever fits your strategy.

## Pick Your Track

The competition has **two tracks**. Both share the same judge, the same
five-status verdict mapping (`accepted` / `unparsed` / `malformed` /
`incomplete_proof` / `incorrect`), and the same submission contract:
**a single `solver.py` file, ≤ 500 KB**. They differ only in how
problems and budgets are shaped — one solver source can support both.

### → Solo track

- **One problem per solver subprocess.** Every problem gets a fresh process.
- **Fixed per-problem budget**: 3600 s wall-clock; LLM calls capped at 65 536 output tokens each; submitted Lean code ≤ 100 KB.
- Communication: stdin (problem JSON) → stdout (answer JSON), one line each.
- **Best for**: getting started, deep single-problem search.
- **Quick Start**: [Solo Quick Start](#solo-quick-start) below.
- **Full spec**: [`docs/solo_mode.md`](docs/solo_mode.md).

### → Marathon track

- **N problems per solver subprocess** (reference: N=100). One process, one shared global budget.
- **Compressed global budget**: `compression_ratio × N × Marathon per-problem reference` (600 s + 65 536 tokens per problem; deliberately tighter than Solo's wall-clock, see [`docs/marathon_mode.md`](docs/marathon_mode.md)). Default `compression_ratio = 0.5` — solver cannot finish all N at the per-problem reference cost and must triage.
- Communication: file-based (read manifest JSONL, append answers JSONL).
- **Best for**: triage strategies, cross-problem caching, prompt reuse.
- **Quick Start**: [Marathon Quick Start](#marathon-quick-start) below.
- **Full spec**: [`docs/marathon_mode.md`](docs/marathon_mode.md).

Most contestants start with Solo. Marathon is the long-form track where
strategic budget allocation is rewarded.

---

## Solo Quick Start

```bash
# One-command setup (installs Lean, fetches Mathlib, builds judge modules)
bash scripts/setup.sh

# Install Python deps (OpenAI SDK — defaults to OpenRouter; override
# via OPENAI_BASE_URL / OPENAI_API_KEY to hit api.openai.com)
pip install openai

# Activate the environment
source .env.judge

# Verify the judge works
python3 scripts/run_harness.py

# Run a demo solver on 20 sample problems
python3 -m pipeline.runner \
  --submission examples/solo/demos/baseline \
  --problems examples/problems/sample_20.json
```

### Prerequisites

- **OS**: macOS (Apple Silicon / Intel) or Linux (x86_64). Windows
  users should run under WSL 2 — the setup targets POSIX shells.
- **Disk**: ~3 GB free (Lean toolchain + Mathlib olean cache — this
  repo is a self-contained lake package depending only on Mathlib; no
  `equational_theories` clone required).
- **RAM**: 8 GB minimum, 16 GB recommended.
- **Network**: Required for initial setup only.
- **Python**: 3.8+ (with `openai` for pipeline LLM calls).
- **Git**: 2.x+.

### Manual setup (step-by-step)

If you prefer to set things up step by step instead of using `setup.sh`:

1. **Install elan** (Lean version manager):
   ```bash
   curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
   export PATH="$HOME/.elan/bin:$PATH"
   ```

2. **Install the Lean toolchain** (version from this repo's `lean-toolchain`):
   ```bash
   TOOLCHAIN=$(cat lean-toolchain | tr -d '[:space:]')
   elan toolchain install "$TOOLCHAIN"
   elan default "$TOOLCHAIN"
   ```

3. **Fetch Mathlib and build the judge modules**:
   ```bash
   lake update                  # pin Mathlib per lakefile.lean
   lake exe cache get           # ~2 GB of pre-compiled Mathlib oleans
   lake build JudgeMagma.Magma JudgeDecide.DecideBang \
              JudgeFinOp.MemoFinOp JudgeSupport.Inspect
   ```

4. **Configure environment**:
   ```bash
   cat > .env.judge <<EOF
   export LEAN_BIN="$(which lean)"
   export LAKE_BIN="$(which lake)"
   export PATH="\$HOME/.elan/bin:\$PATH"
   EOF
   source .env.judge
   ```

5. **Verify**: `python3 scripts/run_harness.py`

---

## Marathon Quick Start

Marathon mode runs **one solver subprocess against N problems** under a
single global budget instead of one subprocess per problem. The solver
contract is the same single-file `solver.py`; the difference is the I/O
shape (file-based) and the budgeting.

```bash
# Run the bundled sequential baseline against a 5-problem manifest.
python3 scripts/run_marathon.py \
  --solver examples/marathon/demos/baseline \
  --manifest tests/marathon_fixtures/manifests/normal_5.jsonl

# Run a strategic, LLM-using marathon solver. Set OPENROUTER_API_KEY
# (or OPENAI_API_KEY) first — it's used by the marathon proxy, never
# forwarded into the solver subprocess.
export OPENROUTER_API_KEY=sk-...
python3 scripts/run_marathon.py \
  --solver examples/marathon/demos/triage \
  --manifest examples/problems/marathon/normal_100.jsonl \
  --compression-ratio 0.5
# 100 problems × 600 s × 0.5 ≈ 30 000 s wall-clock. Swap in
# examples/problems/normal.jsonl (1000 problems, ~83 h at the same
# compression) when you're ready for the full reference set.
```

The runner derives `budget_seconds` and `budget_tokens` from
`compression_ratio × N × Marathon-per-problem-reference` (600 s and
65 536 tokens; see [`docs/marathon_mode.md`](docs/marathon_mode.md)).
Override either budget directly with `--budget-seconds` /
`--budget-tokens`, or change just the multiplier with
`--compression-ratio` (default `0.5`; smaller squeezes harder, `1.0` =
no compression).

Regression harness (separate from `run_harness.py`):

```bash
python3 scripts/run_marathon_harness.py
```

Full Marathon spec: [`docs/marathon_mode.md`](docs/marathon_mode.md).

---

## What You Submit

Your submission is a **single Python file** named `solver.py`, up to
**500 KB**. The file is identical in shape for both tracks; what differs
is the I/O it implements (Solo: stdin/stdout JSON; Marathon:
manifest-in / answers-out files). One source file can support both — see
[`docs/marathon_mode.md`](docs/marathon_mode.md) for the env-var trigger.

```
my_submission/
└── solver.py       # Your program. For Solo: stdin/stdout JSON protocol.
                    #                For Marathon: see docs/marathon_mode.md.
                    # If it uses the LLM in Solo, a module-level
                    # PROMPT = """..."""  string holds the template.
```

The Solo proxy extracts the `PROMPT` constant from `solver.py` via AST
parsing (the module is never imported or executed on the host), fills
placeholders, and sends the rendered prompt to the LLM on the solver's
behalf. The Marathon path uses the helper `from marathon_llm import
call_llm` (or any OpenAI-SDK call) instead — it does not parse a
`PROMPT` constant.

The solver is a free-form program. There are no required function
signatures — the only requirement is the I/O protocol of the track you
are running (described in the Solo sections below and in
[`docs/marathon_mode.md`](docs/marathon_mode.md) respectively).

---

## Reference problem sets

This repo bundles four problem sets at
[`examples/problems/`](examples/problems/) — mirrored from the
HuggingFace dataset
[`SAIRfoundation/equational-theories-selected-problems`](https://huggingface.co/datasets/SAIRfoundation/equational-theories-selected-problems)
— **as practice and training material**. The Stage 2 final evaluation
runs on a held-back set drawn from the same underlying corpus
(including order-5 laws), so the bundled sets are not the eval set;
they are the reference distribution you tune your solver against.

| Set       | Size  | True / False split | Difficulty                                                    |
|-----------|-------|---------------------|---------------------------------------------------------------|
| `normal`  | 1 000 | 500 / 500           | Reference distribution. Start here.                           |
| `hard1`   |    69 |  24 / 45            | Tightly packed pairs; small set, high "compute / row" ratio. |
| `hard2`   |   200 | 100 / 100           | Where the easy patterns run out.                              |
| `hard3`   |   400 | 195 / 205           | Highest difficulty in the public split.                       |

Plus two synthetic samples for fast iteration:
[`examples/problems/sample_20.json`](examples/problems/sample_20.json)
(smoke test) and
[`examples/problems/sample_200.json`](examples/problems/sample_200.json)
(200, 100 true / 100 false). Beginners should validate their solver on
`sample_20.json` first, then move to `normal` once the loop is
reliable.

---

## Examples & Tutorial

The `examples/` directory contains demo submissions, sample problems, and per-track tutorials. Each track has **3 reference demos** chosen as a learning ladder (skeleton → entry-level LLM → flagship strategy):

```
examples/
├── problems/                     # Sample sets + HF JSONL mirrors
│   ├── sample_20.json            #   20 sample problems (quick test)
│   ├── sample_200.json           #   200 problems (100 true + 100 false)
│   └── (normal|hard1|hard2|hard3).jsonl
├── solo/
│   ├── TUTORIAL.md               # Solo: 3 annotated walkthroughs
│   └── demos/
│       ├── baseline/             #   Brute-force + singleton + generic LLM fallback (start here)
│       │   └── solver.py
│       ├── twophase/             #   gpt-oss-120b: deeper search + analysis-then-implementation LLM
│       │   └── solver.py
│       └── opnorm/               #   gpt-oss-120b: 16 deterministic strategies + structural-context LLM (flagship)
│           └── solver.py
└── marathon/
    ├── TUTORIAL.md               # Marathon: 3 walkthroughs (baseline / triage / cross-problem state)
    └── demos/
        ├── baseline/             #   Sequential brute-force, no LLM (start here, zero token cost)
        │   └── solver.py
        ├── triage/               #   Difficulty-sorted Pass B + Pass C deeper-thought retry on Pass-B no-shows (entry-level LLM)
        │   └── solver.py
        └── fewshot/              #   In-run lemma cache + few-shot transfer (cross-problem state, Marathon-only)
            └── solver.py
```

Every submission — including every demo — is a single `solver.py` (≤ 500 KB). If the solver uses the LLM, the prompt template lives as a top-level `PROMPT = """..."""` constant inside that same file (Solo) or is embedded inline in the solver (Marathon).

### Running demos

After `source .env.judge`:

```bash
source .env.judge

# Baseline demo on 20 problems
python3 -m pipeline.runner \
  --submission examples/solo/demos/baseline \
  --problems examples/problems/sample_20.json

# OSS two-phase demo on 200 problems
python3 -m pipeline.runner \
  --submission examples/solo/demos/twophase \
  --problems examples/problems/sample_200.json

# OSS opnorm reference solver on 200 problems
python3 -m pipeline.runner \
  --submission examples/solo/demos/opnorm \
  --problems examples/problems/sample_200.json

# Custom output path
python3 -m pipeline.runner \
  --submission examples/solo/demos/baseline \
  --problems examples/problems/sample_200.json \
  --output results.json
```

**Resume behavior**: If the output file already exists, solved problems are skipped (their entries are kept verbatim). Failed entries are dropped on resume and re-run, and the new outcome replaces the old entry — only one row per problem id ever lands in the output file. To start fresh, delete or rename the output file.

### Interactive CLI

`scripts/submit.py` wraps the same `pipeline.proxy.run_solver` engine as `pipeline.runner`, but adds colorized per-problem rows, a per-problem debug log, and exits `0` iff every selected problem is solved. Use it when you want a tighter feedback loop than the plain runner.

```bash
# Quick smoke on the bundled 20-problem sample
python3 scripts/submit.py \
  --submission examples/solo/demos/baseline \
  --problems   examples/problems/sample_20.json

# Narrow to a handful of IDs and stream JSON results to disk atomically
python3 scripts/submit.py \
  --submission examples/solo/demos/baseline \
  --problems   examples/problems/hard1.jsonl \
  --problem-ids hard1_0001,hard1_0007,hard1_0012 \
  --output     pipeline/results/hard1_spot.json \
  --verbose
```

Any typo in `--problem-ids` or an empty problem set fails with exit code `2` rather than silently running nothing, so a mistyped flag never masquerades as success.

### Tutorial

**Solo** — see [`examples/solo/TUTORIAL.md`](examples/solo/TUTORIAL.md) for three annotated walkthroughs showing the full solver-proxy-judge interaction:

1. **Deterministic counterexample** -- solver finds a Fin 5 counterexample, no LLM needed (1.9s)
2. **LLM feedback loop** -- LLM tries 4 times with judge error feedback until proof accepted (77s)
3. **MATCH-COLLAPSE** -- 9 deterministic strategies fail, then 1 LLM call with specialized prompt succeeds (73s)

**Marathon** — see [`examples/marathon/TUTORIAL.md`](examples/marathon/TUTORIAL.md) for three walkthroughs of marathon-specific strategies:

1. **Free counterexample harvest** -- baseline brute-force pass clears ~40-50% of `normal` at zero token cost
2. **Triage + deeper-thought retry** -- difficulty-sorted Pass B + budget-aware Pass C re-attempt on Pass-B no-shows with bumped reasoning effort (`triage`)
3. **Marathon-distinctive: in-run lemma cache + few-shot transfer** -- `fewshot` accumulates winning patterns across problems and prepends them to later prompts; cross-problem state is structurally impossible in Solo

## Problem Format

Problems use the [HuggingFace-aligned format](https://huggingface.co/datasets/SAIRfoundation/equational-theories-selected-problems). The binary operation may use `◇` or `*` (auto-normalized to `◇` for Lean):

```json
{
  "id": "normal_0646",
  "eq1_id": 2034,
  "eq2_id": 2417,
  "equation1": "x = (y ◇ (z ◇ w)) ◇ (u ◇ v)",
  "equation2": "x = (y ◇ (z ◇ (w ◇ x))) ◇ z",
  "answer": true
}
```

The question: **Does equation1 imply equation2?**

## Answer Format

```json
{"verdict": "true", "code": "<full Lean 4 source code>"}
```

- `verdict`: `"true"` (prove implication) or `"false"` (prove non-implication)
- `code`: Complete Lean 4 source exposing a `submission : Goal` term (see below)

The judge writes a per-verify `JudgeProblem.lean` with the two problem
equations bound as `EquationLHS` / `EquationRHS` plus a verdict-specific
`abbrev Goal`. Submitter code lives in `Submission.lean` and only has
to expose a term named `submission` whose type is definitionally equal
to `Goal`. The goal statement itself is judge-controlled (lives in a
separately-generated `Problem.lean`), so the submitter doesn't need to
write the theorem header at all.

**Lean primitives the certificates use** (all provided by the judge — no
external Mathlib imports needed for the canonical false-cert shape):

- `◇` — the magma's binary operation (single character; `*` in your
  problem text is auto-normalized to `◇`)
- `Magma G` — Lean type class declaring `G` as a magma; `[Magma G]`
  introduces an instance bringing `◇` into scope
- `Fin n` — the standard finite type `{0, 1, …, n-1}`; the canonical
  false-certificate domain
- `finOpTable "<json>"` — judge helper that turns a JSON-encoded n×n
  table into a `Fin n → Fin n → Fin n` operation
- `decideFin!` — judge tactic that closes a finite-domain goal by
  exhaustive evaluation of the magma's operation table

### True certificate

`Goal` expands to `∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G`.

```lean
import JudgeProblem

def submission : Goal := by
  intro G _ h x y z
  …tactics that produce EquationRHS G using h …
```

### False certificate

`Goal` expands to `∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G`.

```lean
import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 2) := { op := finOpTable "[[0,0],[1,1]]" }
  refine ⟨Fin 2, m, ?_⟩
  decideFin!
```

> **Universe note**: `Goal` is pinned to concrete `Type` (= `Type 0`)
> in both branches because `abbrev Goal : Prop := ∀ (G : Type _) …`
> leaves a stuck universe meta that Lean can't resolve at `abbrev`
> elaboration. Submitters work with small types (`Fin n`, concrete
> magmas) which all live in `Type 0`, so this isn't a practical
> restriction.
>
> **Backward compatibility**: old-style `theorem submission :
> <explicit goal> := …` submissions still verify if they use the new
> `import JudgeProblem` imports — `Goal` is `@[reducible]`, so the
> explicit type and `Goal` unify by definitional equality.

---

## System Architecture (Solo)

> Marathon's architecture is parallel but file-based and uses a local
> HTTP LLM proxy instead of stdin/stdout — see
> [`docs/marathon_mode.md`](docs/marathon_mode.md).

```
┌──────────────────────────────────────────────────────────────┐
│                       Proxy (organizer)                       │
│                                                               │
│  1. Start solver as subprocess (sandboxed in production)      │
│  2. Send problem + budget to solver via stdin                 │
│  3. Wait for solver requests on stdout                        │
│  4. For judge calls: forward to judge, return result          │
│  5. For LLM calls: fill PROMPT template, call LLM API         │
│  6. On judge "accepted" → record result                       │
│  7. On wall-clock timeout → terminate solver                  │
│                                                               │
│  ┌────────────────┐                     ┌──────────────────┐ │
│  │     Solver      │  stdin/stdout JSON  │      Proxy       │ │
│  │  (contestant)   │◄═══════════════════►│   (organizer)    │ │
│  │                 │                     │       │    │     │ │
│  │  - isolated     │                     │       │    │     │ │
│  │  - no secrets   │                     │       ▼    ▼     │ │
│  │                 │                     │   ┌─────┐ ┌───┐ │ │
│  │                 │                     │   │Judge│ │LLM│ │ │
│  └────────────────┘                     │   └─────┘ └───┘ │ │
└──────────────────────────────────────────────────────────────┘
```

| Component | Provider | Network | Description |
|-----------|----------|---------|-------------|
| **Solver** | Contestant | Isolated (no secrets, sandboxed in production) | Your program; communicates with proxy via stdin/stdout |
| **Proxy** | Organizer | Online | Launches solver, mediates all I/O, fills prompt templates, calls LLM API, enforces limits |
| **Judge** | Organizer | Offline | Deterministic Lean verifier, returns `accepted` or an error |
| **LLM** | Organizer | Online | Generates proofs/counterexamples when prompted |
| **Prompt** | Contestant | N/A | `PROMPT` constant inside `solver.py` (single-file submission); proxy fills its placeholders before each LLM call |

---

## Communication Protocol

> **Solo only.** Marathon uses a file-based contract (manifest in, JSONL out) plus a local HTTP LLM proxy — see [`docs/marathon_mode.md`](docs/marathon_mode.md).

All communication between solver and proxy uses **JSON messages over stdin/stdout**, one JSON object per line. The proxy starts **one solver process per problem**. No state carries between problems.

### Startup: Proxy -> Solver

When the solver process starts, the proxy writes the problem and budget to stdin:

```json
{
  "problem": {
    "id": "normal_0646",
    "eq1_id": 2034,
    "eq2_id": 2417,
    "equation1": "x = (y ◇ (z ◇ w)) ◇ (u ◇ v)",
    "equation2": "x = (y ◇ (z ◇ (w ◇ x))) ◇ z"
  },
  "budget": {
    "timeout_seconds": 3600,
    "max_code_length": 100000,
    "max_false_cert_bytes": 20000
  }
}
```

### Solver -> Proxy: Judge Request

```json
{"call": "judge", "verdict": "true", "code": "import JudgeProblem\n\ndef submission : Goal := by\n..."}
```

Proxy forwards to judge, returns:

```json
{"status": "accepted"}
```

or:

```json
{"status": "incorrect", "stderr": "type mismatch..."}
```

When proxy sees `"status": "accepted"`, it records the result automatically. The solver does NOT need a separate "submit" action.

### Solver -> Proxy: LLM Request

The solver sends a context dict (not a raw prompt). The proxy reads the `PROMPT` constant from `solver.py`, fills all placeholders, and sends the assembled prompt to the LLM.

```json
{"call": "llm", "context": {"analysis": "No counterexample on Fin 2-3"}}
```

Proxy fills template, calls LLM, returns:

```json
{"response": "{\"verdict\": \"true\", \"proof\": \"intro x y\\n...\"}"}
```

### Full Example Session

```
Proxy  ──stdin──→  {"problem": {...}, "budget": {...}}

                   (solver reads problem, does brute-force search, prepares context)

Solver ──stdout─→  {"call": "llm", "context": {"analysis": "No counterexample on Fin 2-5"}}
Proxy  ──stdin──→  {"response": "{\"verdict\": \"true\", \"proof\": \"intro ...\"}"}

                   (solver parses LLM response, builds full Lean code)

Solver ──stdout─→  {"call": "judge", "verdict": "true", "code": "import ..."}
Proxy  ──stdin──→  {"status": "incorrect", "stderr": "type mismatch ..."}

                   (solver retries — proxy auto-includes error in {history.*})

Solver ──stdout─→  {"call": "llm", "context": {"analysis": "Judge rejected: type mismatch..."}}
Proxy  ──stdin──→  {"response": "{\"verdict\": \"true\", \"proof\": \"have ...\"}"}

Solver ──stdout─→  {"call": "judge", "verdict": "true", "code": "import ..."}
Proxy  ──stdin──→  {"status": "accepted"}

                   (proxy records result, terminates solver process)
```

---

## Prompt Template System

> **Solo only.** The Marathon proxy is an HTTP forwarder — solvers build their own prompts and call it via the OpenAI SDK or `marathon_llm.call_llm`. See [`docs/marathon_mode.md`](docs/marathon_mode.md).

Contestants provide a prompt template as a `PROMPT` string constant inside `solver.py`, using placeholders from three namespaces. The proxy fills them before each LLM call.

### `{problem.*}` -- Problem data (auto-filled)

| Placeholder | Example |
|-------------|---------|
| `{problem.id}` | `normal_0646` |
| `{problem.eq1_id}` | `2034` |
| `{problem.eq2_id}` | `2417` |
| `{problem.eq1_name}` | `Equation2034` |
| `{problem.eq2_name}` | `Equation2417` |
| `{problem.equation1}` | `x = (y ◇ (z ◇ w)) ◇ (u ◇ v)` |
| `{problem.equation2}` | `x = (y ◇ (z ◇ (w ◇ x))) ◇ z` |

### `{history.*}` -- Judge history (auto-accumulated)

| Placeholder | Description |
|-------------|-------------|
| `{history.attempts}` | Formatted log of each attempt's verdict, status, and error |
| `{history.round}` | Number of judge calls so far (`0`, `1`, `2`, ...) |
| `{history.last_error}` | stderr or message from the most recent rejection |
| `{history.last_status}` | `incorrect`, `incomplete_proof`, etc. |

### `{solver.*}` -- Solver context (dynamic)

The solver sends arbitrary key-value pairs in the `context` field of its LLM request. The proxy maps each key `k` to `{solver.k}`.

Example: `{"call": "llm", "context": {"analysis": "..."}}` fills `{solver.analysis}` in the template.

### Unfilled placeholders

Any `{problem.*}`, `{solver.*}`, or `{history.*}` placeholder not matched is silently removed.

### Example PROMPT constant

```python
PROMPT = """You are an expert in universal algebra and Lean 4 theorem proving.

Does {problem.eq1_name} imply {problem.eq2_name}?

Hypothesis ({problem.eq1_name}): ∀ elements, {problem.equation1}
Goal ({problem.eq2_name}): ∀ elements, {problem.equation2}

## Solver's analysis

{solver.analysis}

## Previous attempts (round {history.round})

{history.attempts}

## Response format

ONLY valid JSON, no markdown fences:
{"verdict": "true", "proof": "<tactic body>"}
or
{"verdict": "false", "counterexample_table": [[0,1],[1,0]]}
"""
```

---

## Judge

### Statuses

| Status | Meaning |
|--------|---------|
| `accepted` | Proof compiles, type-checks, and passes dependency policy |
| `unparsed` | Answer is not valid JSON |
| `malformed` | JSON parses but violates required schema |
| `incomplete_proof` | Uses `sorry`, `admit`, or banned axioms/dependencies |
| `incorrect` | Structurally valid but Lean rejects the proof |

The judge is deterministic: same input always produces same output.

### Constraints

| Constraint | Value |
|------------|-------|
| Max code length | 100,000 characters |
| Max false certificate code | 20,000 bytes |
| Lean timeout | 300 seconds per proof |
| Banned tokens | `sorry`, `admit`, `sorryAx`, `dbg_trace`, `dbgTrace`, `run_tac`, `mkSorry`, `initialize`, `builtin_initialize` |

### Available Imports

Your code runs with a sandboxed LEAN_PATH covering the judge's own
modules and the Mathlib olean cache. Available imports:

- `JudgeProblem` — binds `EquationLHS` / `EquationRHS` to the two
  problem equations (generated per-verify) plus an `abbrev Goal`
  whose body is the verdict-specific ∀ / ∃ statement
- `JudgeDecide.DecideBang` — `decideFin!` / `decide!` tactics for
  finite-model checking
- `JudgeFinOp.MemoFinOp` — `open MemoFinOp` exposes `finOpTable`, a
  JSON-string → `Fin n → Fin n → Fin n` helper for building finite
  magmas
- `JudgeMagma.Magma` — the `◇` operator (re-imported by
  `JudgeProblem`, so you rarely need this directly)
- `Mathlib.*` — any Mathlib module, pinned by `lakefile.lean`

---

## Configuration

> Below: **Solo** reference budgets and LLM parameters. Marathon derives its global budgets from these via `compression_ratio` — see [`docs/marathon_mode.md`](docs/marathon_mode.md).

> The numbers in `pipeline/config.json` (wall-clock timeout, Lean timeout, code-size caps, sandbox limits, LLM parameters) are a **reference configuration** for Stage 2. They will be tuned based on community feedback as the competition progresses — expect the wall-clock budget and sandbox limits in particular to settle once we see how contestant solvers actually behave. The single-file solver contract and the public five-status verdict semantics are stable; the numerical knobs are not.

### LLM Parameters

All LLM parameters are fixed by the organizer in `pipeline/config.json`. Contestants cannot change them.

| Parameter | Value |
|-----------|-------|
| Model | `openai/gpt-oss-120b` |
| Provider | `deepinfra/bf16` |
| Max output tokens | 65,536 |
| Temperature | 0.0 |
| Reasoning effort | medium |
| Seed | 0 (deterministic) |

`reasoning_effort` is pinned to `medium` as a reference: at `high`, `openai/gpt-oss-120b` on `deepinfra/bf16` has been observed to burn the entire HTTP budget inside the reasoning chain and return empty `content` on hard problems. `medium` consistently emits substantive Lean within the budget and is the value we run the reference solver against. Subject to change as providers and models evolve.

LLM calls go through the OpenAI SDK with `base_url` pointing at
OpenRouter by default. Set one of `OPENAI_API_KEY` or
`OPENROUTER_API_KEY`; flip to OpenAI directly by also setting
`OPENAI_BASE_URL=https://api.openai.com/v1` (and adjusting the model
name).

There are **two routing styles**, both work end-to-end:

1. **Env-driven (single global provider)** — `OPENAI_BASE_URL` +
   `OPENAI_API_KEY` set in the shell apply to every config. Best for
   "I just want to swap OpenRouter for OpenAI everywhere".
2. **Config-driven (per-run / per-experiment provider)** — set
   `llm.base_url` and `llm.api_key_env` in the config JSON. The
   environment value of `llm.api_key_env` is read at call time:

   ```json
   "llm": {
     "model": "deepseek-v4-flash",
     "base_url": "https://api.deepseek.com/v1",
     "api_key_env": "DEEPSEEK_API_KEY",
     "max_output_tokens": 8192,
     "temperature": 0.2
   }
   ```

   The proxy talks to any OpenAI-compatible endpoint this way:
   DeepSeek, Kimi/Moonshot, GLM/Zhipu, Minimax, Qwen, api.openai.com,
   etc. — no code changes. OpenRouter-only fields (`provider`,
   `reasoning_effort`) are emitted only when `base_url` actually
   points at OpenRouter, so a config that adds just `base_url` +
   `api_key_env` to the default never leaks OpenRouter routing hints
   to a direct provider.

### Solver Budgets

| Limit | Value | Description |
|-------|-------|-------------|
| Wall-clock timeout | 3600s | Single per-problem budget; pacing LLM/judge calls within this is the solver's responsibility. Widened from the earlier 600s reference so multi-round LLM loops have room to finish under `reasoning_effort=medium`. |
| Solver file size | 500 KB | `solver.py` larger than this is rejected pre-launch |

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `LEAN_BIN` | auto-detected | Path to the `lean` binary |
| `LAKE_BIN` | auto-detected | Path to the `lake` binary |
| `JUDGE_ARTIFACT_DIR` | `.artifacts` | Where per-verify `JudgeProblem.lean`, `Submission.lean`, and `Problem.lean` are written |
| `JUDGE_LEAN_PATH` | (none; falls back to `lake env`) | Operator override for `LEAN_PATH` — useful when `.lake/` is read-only and `lake env` can't recompute |
| `LEAN_TIMEOUT_SECONDS` | `120` (raw `judge/verify.py`) / `300` (via pipeline, from `judge.lean_timeout_seconds` in `pipeline/config.json`) | Per-proof compilation timeout. The pipeline's 300 s value is what actually runs during evaluation; the 120 s default only applies if you invoke `judge/verify.py` directly without the runner. |
| `OPENAI_API_KEY` | (none) | Preferred API key for LLM calls — OpenAI SDK reads it first |
| `OPENROUTER_API_KEY` | (none) | Fallback key if `OPENAI_API_KEY` is unset; same wire format |
| `OPENAI_BASE_URL` | `https://openrouter.ai/api/v1` | Env-level base URL; overridden by `llm.base_url` in the config |
| `<llm.api_key_env>` | (none) | Whichever name the config's `llm.api_key_env` points at — e.g. `DEEPSEEK_API_KEY` for direct DeepSeek routing |

### Solver Sandbox (optional, MVP)

Contestant `solver.py` can be run inside a Docker container for host isolation. Mode is controlled by `pipeline/config.json`:

```json
"sandbox": {
  "mode": "none",            // "none" (default) | "docker"
  "image": "ee-solver:latest",
  "memory_mb": 2048,
  "cpus": 2,
  "pids_limit": 64,
  "tmpfs_size_mb": 64
}
```

With `mode = "none"` the `memory_mb`, `cpus`, `pids_limit`, and `tmpfs_size_mb` fields are inert — the solver runs in-process on the host and inherits the host's resources. They take effect only when `mode = "docker"`, where they are mapped to `--memory` / `--memory-swap` / `--cpus` / `--pids-limit` / `--tmpfs /tmp:size=` on the `docker run` invocation below. The values shown are **reference** numbers that let the bundled reference solver and demos finish within budget on a modest box; like the rest of the config they will be refined from community-feedback once Docker-mode runs are common.

When `mode = "docker"` the solver is launched as:

```
docker run --rm -i --network=none --read-only \
  --cap-drop=ALL --security-opt=no-new-privileges:true \
  --memory=<memory_mb>m --memory-swap=<memory_mb>m \
  --cpus=<cpus> --pids-limit=<pids_limit> \
  --tmpfs /tmp:size=<tmpfs_size_mb>m \
  -v <submission>:/solver:ro -e PYTHONUNBUFFERED=1 <image>
```

Hardening layers: no network, read-only root FS, all capabilities dropped, no-new-privileges, non-root `solver` user (from the image), `--memory-swap` pinned to `--memory` so swap can't double the effective limit, bounded CPU/pid/tmpfs, `/solver` mount read-only. The host `docker` CLI inherits the full host environment (so DOCKER_HOST / DOCKER_CONFIG / TLS vars reach the daemon); the container sees only the minimal env injected via explicit `-e` flags.

Building the image: `bash scripts/setup.sh` will build `ee-solver:latest` automatically when Docker is running (silently skipped otherwise).

Verifying the sandbox: `python3 scripts/sandbox_smoke.py` runs four checks (benign solver boots, network blocked, mounted dir read-only, container runs non-root with capability bitmap cleared). Exits `2` (skip) if the Docker daemon is unreachable; not part of the canonical harness yet.

The default remains `"none"` so existing setups work unchanged; opt in by flipping `mode` to `"docker"` after `setup.sh` succeeds.

### Testing & Harness

The canonical completion gate is `python3 scripts/run_harness.py` — deterministic, offline, non-interactive. Exit `0` means every suite below passed.

| Suite | Current count | Source of truth | Covers |
|---|---|---|---|
| Judge cases | 66 | `tests/harness_manifest.json` | Accepted / malformed / unparsed / incomplete_proof / incorrect on curated fixtures (incl. FALSE_CERT_TOO_LARGE) |
| Judge internals | 32 | `run_judge_internal_cases` in `scripts/run_harness.py` | Unit-level invariants on verify.py helpers (equation normalization, byte-length cap, path stripping, render template stability, JudgeConfig budget-field plumbing for the three judge caps) |
| Banned tokens | 24 | `run_banned_token_cases` in `scripts/run_harness.py` | Placeholder-detector word-boundary + substring matrix for every entry in `BANNED_PROOF_TOKENS` |
| Repeatability | 4 | `repeatability_cases` in the same manifest | Selected cases run 3× and must project byte-identical results |
| Pipeline regressions | 55 | Inlined in `scripts/run_harness.py` | Single-file `PROMPT` extraction (all bundled demos), stray `prompt.txt` is ignored, AST extractor hostile inputs (scope, type, first-wins, AnnAssign, NUL / invalid UTF-8), sandbox argv shape (none / docker / unknown), host-vs-container env selection, stderr drained into bounded ring buffer (so contestant tracebacks land in a `solver_stderr` log entry instead of being silently dropped, without re-introducing the kernel-pipe deadlock), 500 KB `solver.py` intake cap, single-file layout (helper / payload / subdir / symlink rejected), stdout line cap, wall-clock deadline clamping LLM + Lean timeouts, docker-cleanup-in-finally static check, doc-drift guard, public-allowlist demo count, `_call_llm` falls back to DeepSeek-style `reasoning_content` (streaming + non-streaming) when `content` is empty and surfaces `truncated: True` when `finish_reason=length` left no final answer |
| Verify branches | 3 | `run_verify_branch_cases` in `scripts/run_harness.py` | LEAN_TIMEOUT via mocked `subprocess.run`; FALSE_CERT_TOO_LARGE rejection respects `JudgeConfig.max_false_cert_bytes` (cap=10 KB rejects 15 KB; cap=20 KB admits the same payload) |
| Public challenger | 79 | `tests/challenger_manifest.json :: public_attack_cases` | Bypass attempts (banned placeholder / axiom / declaration smuggling, stdout injection) plus positive-control regressions for previously-false-negative proofs |
| Infra challenger | 4 | same manifest, `infra_attack_cases` | Organizer-side malformed problems must raise `JudgeConfigurationError`, never map to a contestant verdict |

Current repo baseline: **267 green checks** across the suites above (the harness also runs submit-CLI and loader smoke tests, plus a README self-check; the JSON summary lists every `passed_*_count` field separately). The README self-check (`run_readme_consistency_check`) reads the live `summary` map after every suite has run and compares each cell here to the matching `passed_*_count` — so adding a regression auto-bumps the canonical numbers, and any drift here fails the gate. Any nonzero exit blocks completion — do not weaken a test to get green.

Reading the JSON summary the harness prints:

- `passed_case_count` / `case_count` — judge suite
- `passed_pipeline_count` / `pipeline_count` — proxy-layer tests
- `passed_repeatability_count` / `repeatability_count` — determinism
- `challenger.passed_public_attack_count` / `public_attack_count` — challenger public
- `challenger.passed_infra_attack_count` / `infra_attack_count` — organizer infra
- `failing_*` arrays are empty on green; populated with the offending case detail on failure

Adding a new regression (quickest path):

1. Drop the fixture into `tests/fixtures/` (or `tests/challenger/` for adversarial cases).
2. Append an entry to the matching manifest with `expected_status` and `expected_error_code`.
3. Rerun `python3 scripts/run_harness.py` and confirm it picks up the new case.

Opt-in Docker sandbox check — *not* part of the canonical gate because it needs the Docker daemon:

```
python3 scripts/sandbox_smoke.py
```

Exits `0` when the sandbox image boots, blocks network, and blocks writes to the mounted solver dir; `2` when Docker is unreachable (treated as skip); `1` on any assertion failure.

---

## Project Structure

```
.
├── README.md                        # This file (entry point + Pick Your Track)
├── docs/                            # Track specs (read these before submitting)
│   ├── solo_mode.md                 #   Solo track: I/O contract, budgets, scoring
│   └── marathon_mode.md             #   Marathon track: same, plus compression_ratio
│
├── judge/                           # Deterministic Lean verifier (shared by both tracks)
│   ├── verify.py                    #   Core verification logic
│   ├── challenger.py                #   Adversarial test runner
│   ├── JudgeMagma/Magma.lean        #   `◇` operator + Magma class
│   ├── JudgeDecide/DecideBang.lean  #   `decideFin!` / `decide!` tactics
│   ├── JudgeFinOp/MemoFinOp.lean    #   `finOpTable` helper for finite magmas
│   └── JudgeSupport/Inspect.lean    #   #judge_report dep-tracking metaprogram
│
├── pipeline/                        # Evaluation orchestration
│   ├── proxy.py                     #   Solo: launches solver, mediates stdin/stdout, fills prompts
│   ├── runner.py                    #   Solo: batch evaluation entry point
│   ├── config.json                  #   Solo per-problem budgets + LLM parameters
│   ├── marathon_runner.py           #   Marathon: snapshot manifest, dual-budget watchdog
│   ├── marathon_proxy.py            #   Marathon: local HTTP proxy (key isolation + token meter)
│   ├── marathon_score.py            #   Marathon: last-write-wins parser + per-line verify_answer
│   └── marathon_llm.py              #   Marathon: solver-side LLM helper (call_llm)
│
├── examples/                        # Demo submissions + sample problems
│   ├── problems/                    #   Sample sets + HF JSONL mirrors
│   │   ├── sample_20.json           #     20 sample problems
│   │   ├── sample_200.json          #     200 problems (100 true + 100 false)
│   │   └── (normal|hard1|hard2|hard3).jsonl   # HF SAIR sets
│   ├── solo/                        #   Solo track: 3 reference demos + tutorial
│   │   ├── TUTORIAL.md
│   │   └── demos/
│   │       ├── baseline/            #     Brute-force + singleton + LLM fallback (start here)
│   │       ├── twophase/            #     gpt-oss-120b + two-phase strategy
│   │       └── opnorm/              #     gpt-oss-120b + opnorm flagship reference solver
│   └── marathon/                    #   Marathon track: 3 reference demos + tutorial
│       ├── TUTORIAL.md
│       └── demos/
│           ├── baseline/            #     Sequential brute-force, no LLM (start here, zero token cost)
│           ├── triage/              #     Difficulty-sorted Pass B + Pass C deeper-thought retry on Pass-B no-shows
│           └── fewshot/             #     In-run lemma cache + few-shot transfer (Marathon-only strategy)
│           # Each demo is a single solver.py
│
├── tests/                           # Test data
│   ├── harness_manifest.json        #   Solo harness cases
│   ├── challenger_manifest.json     #   Solo adversarial cases
│   ├── fixtures/                    #   Solo fixtures
│   ├── marathon_manifest.json       #   Marathon harness cases
│   └── marathon_fixtures/           #   Marathon fixtures (manifests + fixture solvers)
│
├── scripts/
│   ├── setup.sh                     #   One-command environment setup
│   ├── run_harness.py               #   Solo harness — canonical green gate
│   ├── run_marathon.py              #   Marathon CLI entry (run + score)
│   ├── run_marathon_harness.py      #   Marathon harness — separate green gate
│   └── submit.py                    #   Interactive CLI runner (colorized; Solo)
│
├── lakefile.lean                    #   Self-contained lake package (depends only on Mathlib)
├── lake-manifest.json               #   Pinned Mathlib revision
├── lean-toolchain                   #   Pinned Lean toolchain version
└── .env.judge                       #   (gitignored) generated environment config
```

## Troubleshooting

**"missing lean/lake binary"**
-- `source .env.judge` to set the correct paths, or install elan and re-run setup.

**Lean timeout on valid proofs**
-- The pipeline already passes `judge.lean_timeout_seconds = 300` from `pipeline/config.json`; that value is what runs during evaluation. If you're invoking `judge/verify.py` directly (outside the runner), it falls back to a 120 s default — `export LEAN_TIMEOUT_SECONDS=300` matches the pipeline. To raise the cap globally, edit `pipeline/config.json`.

**"lake env failed"**
-- Mathlib isn't built in this working tree. Run `lake update && lake exe cache get && lake build JudgeMagma.Magma JudgeDecide.DecideBang JudgeFinOp.MemoFinOp JudgeSupport.Inspect`, or re-run `bash scripts/setup.sh`.

**"JudgeProblem does not have expected universe"** / universe inference errors in the judge output
-- Your submission's type uses `Type _` in a position where Lean can't infer the universe at elaboration. The judge's `Goal` is pinned to concrete `Type` (= `Type 0`); use `Type` in any explicit type annotations that must unify with `Goal`. See the Universe note under [Answer Format](#answer-format) for details.

**LLM call returns an empty response with `reasoning` populated**
-- The model exhausted its token budget mid-chain-of-thought. The proxy will fall back to `message.reasoning` automatically. The default `reasoning_effort` in `pipeline/config.json` is already `medium`; if you keep hitting this, drop it to `low` or `minimal`, or trim your PROMPT so the model has room to emit a structured answer after reasoning.

**"OPENAI_API_KEY or OPENROUTER_API_KEY not set"**
-- Set either one in the environment (they're interchangeable at the wire level). Persist to `.env` if you want it across shells.

## License

Licensed under the [Apache License, Version 2.0](LICENSE). See `LICENSE` for the full text.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) — issue-first policy, bug-report
required fields, and trivial-fix exceptions are documented there.
