# Mathematics Distillation Challenge - Equational Theories (Stage 2)

*(Damek Davis, Terence Tao)*

## Overview

This competition explores a core question in AI for mathematics: can strong mathematical reasoning be distilled into a compact, human-readable artifact that improves LLM performance on formal tasks?

This competition is organized by:

Damek Davis (Associate Professor, Department of Statistics and Data Science, University of Pennsylvania)

Terence Tao (Fields Medalist, Professor at UCLA, Co-Founder of SAIR Foundation)

and SAIR Foundation.

The setup is inspired by Honda, Murakami, and Zhang (2025), *[Distilling Many-Shot In-Context Learning into a Cheat Sheet](https://arxiv.org/abs/2509.20820)*.
Our difference is that the distilled artifact is discovered through an open competition process rather than a single model query.

## Background

The pilot task is equational implication over magmas: given Equation 1 and Equation 2, determine whether Equation 1 implies Equation 2.

This challenge is based on the [Equational Theories Project](https://teorth.github.io/equational_theories/):

- Raw implication graph: [export_raw_implications](https://teorth.github.io/equational_theories/implications/)
- Law list (4694 laws): [equations.txt](https://github.com/teorth/equational_theories/blob/main/data/equations.txt)

Example: `E_4: x = x * y` implies `E_3: x = x * x`.

## Core Task

Stage 2 raises the bar from Stage 1. Instead of only predicting true/false, participants must **prove** their answers:

- If the implication is **true**: a Lean 4 proof that the hypothesis implies the goal.
- If the implication is **false**: a Lean 4 proof certificate (a finite magma witness where the hypothesis holds but the goal fails).

Both directions require machine-verifiable certificates. A deterministic Lean judge accepts or rejects each answer — no partial credit, no probabilistic scoring.

## What Participants Submit

Participants submit a **solver**: a single `solver.py` file, **≤ 500 KB**, that follows the I/O protocol of the chosen track.

The solver can combine:

- **Deterministic strategies** (brute-force counterexample search, pattern matching, symbolic proof construction)
- **LLM calls** (via the organizer-provided proxy)
- **Judge calls** (submit candidate proofs for Lean verification, receive accept/reject feedback)

## Tracks

Stage 2 has two tracks. Both share the same judge, the same five-status verdict mapping, and the same single-file `solver.py` contract (≤ 500 KB). They differ only in I/O shape and budgeting:

- **Solo** — one problem per solver subprocess, fixed per-problem budget, stdin/stdout JSON protocol.
- **Marathon** — N problems per solver subprocess (reference N=100), one shared global budget = `compression_ratio × N × Marathon per-problem reference` (default `compression_ratio = 0.5`), file-based manifest in / append-only JSONL out. The Marathon per-problem reference is deliberately tighter than Solo's wall-clock — see `docs/marathon_mode.md` for the rationale.

One source file can support both tracks. Concrete I/O, size limits, budgets, scoring, and the evaluation model are documented in **[evaluation.md](evaluation.md)**.

## Key Dates

- Stage 2 pre-registration opens: **April 23, 2026**
- Stage 2 officially starts: **May 1, 2026, 12:00 UTC**
- Stage 2 submission deadline: **August 31, 2026, 23:59 AoE**

## Official Repository

The official GitHub repository for Stage 2 contains the evaluation pipeline, demo solvers, a step-by-step tutorial, and local testing support:

- [https://github.com/SAIRcompetition/equational-theories-lean-stage2](https://github.com/SAIRcompetition/equational-theories-lean-stage2)

For setup instructions and the recommended local testing workflow, see **[evaluation.md](evaluation.md)**.

## Publication Policy

- Stage 1 submitted prompts may be made public to support community learning.
- Stage 2 submitted solvers may be made public after evaluation.

## Eligibility and Registration

Stage 2 registration is **open to everyone** — participation is not restricted to Stage 1 participants or top-performing teams. Anyone can register a team and submit a solver before the Stage 2 submission deadline.

## Team Participation and Anti-Cheating Policy

- Each individual or organization can participate in only one team.
- Teams must register members and sponsors in advance.
- If coordinated cheating is detected (including sockpuppet teams), all related teams will be disqualified.

## Community Feedback

Rules, scoring details, and evaluation procedures are still being refined and will be shaped by community input. Community contributions are welcome.

Join the SAIR Foundation Zulip community for discussion and collaboration:

- [https://zulip.sair.foundation/](https://zulip.sair.foundation/)
