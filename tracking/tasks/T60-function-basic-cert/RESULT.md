# T60 result

Status: completed for the Function.Basic slice and final dependent review. No
cloud, package cache, frozen evidence, or compiler build was changed.

## Changes and evidence

- The authenticated overlay has 13 entries: `Function.hfunext`,
  `Function.Injective.dite`, `injective_comp_right_iff_surjective`,
  `Bijective.existsUnique_iff`, the `Function.update` definition plus
  `rec_update`, `apply_update`, `apply_update₂`, `pred_update`, `update_comm`,
  `update_idem`, `Pi.map_injective`, and `LeftInverse.cast_eq`. Originals stay
  adjacent as comments and replacements are readable ordinary Lean.
- The catalog covers the observed `grind`, `simpa`, and `Function.update`
  metadata executions; the stock/replacement fixtures compare every
  `EMatchTheorem` field for the complete `Function.update` differential.
- `explicit_grind_def` now fails closed on the exact Name literal
  ``Function.update``. `RejectedFunction.lean` proves another definition is
  rejected before generic equation lookup; the successful differential remains.
- Fresh Function.Basic replay: **25/25**, all replayed, with stock whole-module
  compilation. Evidence and compact diagnostics are under
  `.lake/private/T60-review/evidence/`; the fresh replay paths are in `/tmp`.
- Pipeline: **367 checks** (the prior 364 plus three guard checks); helper lint:
  **46 passed, 2 skipped**; fresh generated Function.Basic lint: **0**.
  No-new-axiom comparison: **13/13** declarations matched.
- Fresh strict `Logic.Basic`, `Function.Basic`, and dependent `IsEmpty.Basic`:
  **rc 0**; translated-root first-match resolution: **69/69**. `ExistsUnique`
  returned the expected **rc 1** at the unresolved broader-family guard.
- The old segfault was diagnosed as stale, overbroad/mixed output staging, not a
  Function.Basic defect. The exact dependent probe now passes; no whole-cone or
  whole-tree acceptance is claimed.

## Checks

`python3 -B Experiment/pipeline/check_pipeline.py`, Python compilation,
`python3 -B Experiment/check_simp_family_lint.py`,
`python3 -B Experiment/check_no_simp_family.py`, and `git diff --check` passed;
package status was clean. Final reruns did not build the compiler.
