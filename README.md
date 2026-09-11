# Explicit Lean

A source-to-source translator replacing executable `simp` and `simp only`
calls in pinned Mathlib with deterministic, search-free applications of checked
results. Stock `simp` runs during recording; the generated replacements must
not run the simplifier, simprocs, dischargers or tactic search. Original calls
remain as adjacent comments. Public statements and computational semantics are
preserved.

**New agent: read [HANDOFF.md](HANDOFF.md).** It provides the current state,
first checks, code map and next milestone without requiring the campaign history.

## Current position

At the September 10 handoff, the inventory has 83,627 calls in 8,264 modules.
There are 529 successful v10 module reports covering 2,063 calls, plus 62 cached
semantic/unsupported failures. Complete translated-tree acceptance is still
zero. The user merged the reviewed supervisor branch at `ee30955`.

The next direction is a bounded AWS/Linux pilot, initially one 128 GiB machine
and one worker, followed by foundational semantic fixes. No cloud machine has
been provisioned; concrete launch limits and the expired campaign scheduling
policy still need to be settled. The small override-memory cleanup saves about
half a GiB in isolation and is optional.

## Pins and implementation

- Lean: `leanprover/lean4:v4.32.2` (see [lean-toolchain](lean-toolchain)).
- Mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c`, via the pinned
  [Lake manifest](lake-manifest.json).
- Active output: `simp_engine_boundary_select` with encoded result application.
  Active artifact schema 5, selector schema 2, module report schema 13.
- The existing schema-27 `simp_engine_apply` is **legacy operational replay**.
  Its name is not evidence that it implements the current boundary replacement.

## Documents

| Document | Read it for |
| --- | --- |
| [HANDOFF.md](HANDOFF.md) | First steps, next deliverable, constraints and code map |
| [AGENTS.md](AGENTS.md) | Working rules |
| [tracking/STATUS.md](tracking/STATUS.md) | Concise current evidence and blockers |
| [tracking/campaign.json](tracking/campaign.json) | Current policy and work state |
| [tracking/handoff-snapshot.json](tracking/handoff-snapshot.json) | Portable counts, 62 failures and 15 pilot candidates |
| [tracking/REVIEW-2026-09-09.md](tracking/REVIEW-2026-09-09.md) | Detailed review and subsequent measured findings |
| [WEEKLY.md](WEEKLY.md) | Original campaign and still-applicable acceptance criteria |
| [PLAN.md](PLAN.md), [simprocs.md](simprocs.md) | Historical design background, read as needed |
| [REPORTS.md](REPORTS.md) | Historical archive conventions; no automatic upload |
| [SIMP_ENGINE_COVERAGE.md](SIMP_ENGINE_COVERAGE.md) | Frozen schema-27 legacy contract only |

Large evidence lives in git-ignored `.lake`. A fresh clone contains the portable
handoff summary, not the local database, reports or compiled artifacts. The
previous long README remains available in Git at `ee30955:README.md`.
