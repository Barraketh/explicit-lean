# T57 result

Status: partial, fail-closed. Fourteen safe ordinary-Lean proof replacements
are integrated. Full `Mathlib.Logic.Basic` certification is not claimed.

## Implementation

- Added a separate broader-family overlay, applied after ordinary simp-site
  rendering. Each entry authenticates the exact pinned environment, module
  source hash, UTF-8 byte range/text and deterministic occurrence identity.
- Missing, shifted, duplicate, overlapping, protected-site, wrong-environment,
  malformed UTF-8 and unused entries fail closed. Original source remains as an
  adjacent, correctly indented comment.
- Added 14 readable proof replacements for `grind`/`simpa` declarations in
  `Mathlib.Logic.Basic`; theorem statements and simp attributes are preserved.
- Rejected two attempted metadata deletions during coordinator review.
  `@[grind =] xor_def` and
  `grind_pattern Exists.choose_spec => P.choose` remain unchanged because a
  valid replacement must preserve their environment-extension semantics.

## Checks

- `python3 -B Experiment/pipeline/check_pipeline.py`: 341 checks passed.
- `python3 -B Experiment/check_simp_family_lint.py`: 46 passed, 2 opt-in corpus
  sweeps skipped.
- `python3 -m py_compile Experiment/pipeline/broader_overlay.py
  Experiment/pipeline/check_pipeline.py Experiment/pipeline/replay_module.py`:
  passed; `git diff --check`: passed.
- `python3 -B Experiment/check_explicit_rw.py`: passed before the final
  authentication/layout-only fixes (16 fixtures, 14 syntax rejections,
  138-theorem axiom audit and 108 escape probes; about 293s).
- Fresh no-new-axiom comparison passed for all 14 changed proof declarations:
  `.lake/private/T57-no-new-axiom-round2-20260919T092119Z/no-new-axiom.json`.

## Current-main integration probe

Using current integrated main as both accepted T1 and T2 inputs:

- Fresh replay command output `/tmp/T58-main-replay-20260919T092803Z` in 6.86s:
  all 31/31 direct simp sites replayed, stock whole-module compile returned 0,
  and the 14 broader proof replacements were applied.
- Simp-disabled compilation with the strict prior translated dependency root
  returned 1, emitted no olean, and reported exactly two engine executions: the
  unchanged `@[grind =]` operation and `grind_pattern` command.
- Static lint returned 1 with exactly two distinct dormant source findings: the
  Meta `simp symmExpr` bodies at generated lines 56 and 87. They did not execute
  during this module compile but remain forbidden source.

The earlier 31-direct-site failure used stale divergent T1/T2 task worktrees and
is not the current baseline. The current remaining Logic.Basic work is two
semantics-bearing Grind metadata operations plus two dormant Meta simp bodies.
Frozen evidence was only read/copied; no frozen source or receipt was modified.
