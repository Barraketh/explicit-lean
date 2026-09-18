# T38 — stable hypothesis scope for multi-step replay

## Result

Fixed the two remaining Function.Basic replay failures (one-based ordinals 2
and 16).  `explicit_rw` now composes a multi-step replacement against a
stable hypothesis declaration and calls `MVarId.replace` once.  Previously,
the first propositional step rebound the hypothesis and later steps reused its
stale `FVarId`, producing an `unknown free variable _fvar...` diagnostic.

Changed:

- `ExplicitLean/ExplicitRw/Tactic.lean`: stable local-target composition in
  `runSteps`; goal-target behavior is unchanged.
- `test/ExplicitRw/T38TransportScope.lean`: exact site-shaped replacements
  for `not_surjective_Type` ordinal 2 and
  `surjective_comp_right_iff_injective` ordinal 16.

Checks:

- `lake build ExplicitLean.ExplicitRw` — PASS.
- `lake env lean test/ExplicitRw/T38TransportScope.lean` — PASS; both exact
  generated replacement forms compile, including ordinal 16's one-call
  four-step hypothesis rewrite.
- `python3 -B Experiment/check_explicit_rw.py` — PASS (12 fixtures, 14
  rejected-syntax cases, 135-theorem axiom audit, 110 escape probes).
- `python3 -B Experiment/check_no_simp_family.py` — PASS (4 files).
- `python3 -B Experiment/pipeline/check_pipeline.py` — PASS (295 checks;
  existing Nontrivial.Defs render failure remains unrelated).
- `git diff --check` — PASS.

No recorder, renderer, schema, or source-call changes were needed: the
failure was a bounded consumer-side stale-local scope defect.
