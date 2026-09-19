# T57 result

Status: partial, fail-closed.  The broader-family mechanism is implemented and a
private Logic.Basic diagnostic copy certifies; freshly generated direct-simp
source remains blocked by the current T1/T2 trace contract.

## Fresh reproduction

- `python3 -B Experiment/pipeline/replay_module.py --module Mathlib/Logic/Basic.lean --t1 /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture --t2 /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw --out $PWD/.lake/private/T57-pipeline-overlay-20260919T020142` (6.01s): 31 sites; 30 `render_failed:missing_derivation`, 1 unresolved; stock whole-module compile 0.
- Fresh output: `.lake/private/T57-fresh-generated-cert-20260919T020210/Mathlib/Logic/Basic.lean`.
- `run.py` on that fresh output: 45 diagnostics (31 forbidden simp-engine executions, 14 cascading unknown constants), exit 1, no olean: `.lake/private/T57-fresh-generated-cert-20260919T020210/certification.log`.
- `python3 -B Experiment/simp_family_lint.py .lake/private/T57-fresh-generated-cert-20260919T020210/Mathlib/Logic/Basic.lean`: 33 findings (31 retained direct sites plus 2 dormant Meta bodies at source lines 56 and 87).

## Implementation and verified reduction

- Added `Experiment/pipeline/broader_overlay.py` and authenticated data
  `Experiment/pipeline/broader_simp_family_overrides.json`: 16 Logic.Basic
  entries (xor grind proofs/attribute, simpa declarations, grind metadata and
  four additional grind declarations).  Each exact UTF-8 range/text is checked;
  missing, shifted, duplicate, overlapping, protected-simp-site and unused
  rendered entries fail closed.  Original text is an adjacent comment.
- `python3 -B Experiment/pipeline/check_pipeline.py`: 328 checks passed.
- `python3 -B Experiment/check_simp_family_lint.py`: 46 tests passed.
- `python3 -B Experiment/check_explicit_rw.py`: PASS (16 fixtures, 14 rejected-syntax cases; 138-theorem axiom audit; 108 escape probes; about 293s).
- `python3 -m py_compile Experiment/pipeline/replay_module.py Experiment/pipeline/check_pipeline.py Experiment/pipeline/broader_overlay.py`; `git diff --check`: passed.
- Applying the overlay to a fresh private copy of the frozen T55 diagnostic
  source (never modifying the frozen tree), then `lake env lean`: exit 0.
  `run.py` was invoked with absolute source/output paths and explicit pinned
  `LEAN_PATH`: exit 0, fresh olean, 1.33s. Output:
  `.lake/private/T57-certified-overlay-20260919T020332/`.
- No-new-axiom comparison: 15 changed declarations, no replacement axiom set
  exceeded stock; report `.lake/private/T57-axiom-20260919T020246/no-new-axiom.json`.

## Limits

The fresh generator cannot yet authenticate T55-style operational derivations,
so the full freshly generated Logic.Basic certification is not claimed.  The
frozen-source overlay validation certifies the 16 broader replacements only;
31 direct simp sites remain visibly unresolved in the fresh output.  Dormant
Meta bodies remain source lint findings but did not execute under certification.
