# T60 result

Status: completed for the assigned Function.Basic broader-family slice. No
cloud, deadline, package, or frozen evidence was changed.

## Changes

- Added 13 authenticated `Mathlib/Logic/Function/Basic.lean` overlay entries,
  using the pinned Function.Basic source hash
  `edceb49f6bbaf313b6803a49b31d9d51aef09a85057b26d6ee3f147d281217fe` and
  deterministic occurrence IDs. Every replacement is readable ordinary Lean;
  every original call/declaration remains an adjacent comment.
- Catalogued the observed engine executions: `Function.hfunext` (`grind`),
  `Function.Injective.dite` (`grind`),
  `injective_comp_right_iff_surjective` (`simpa using congr_fun this b₀`),
  `Bijective.existsUnique_iff` (`simpa [hx]`, then the static second
  `simpa [hz]`), `rec_update`/`apply_update`/`apply_update₂`/`pred_update`/
  `update_comm`/`update_idem` (`grind`), `Pi.map_injective` (`simpa using
  congrFun h i`), and `LeftInverse.cast_eq` (`grind`). The newly exposed
  `@[grind] def Function.update` metadata execution was catalogued separately
  and replaced with a complete stock/replacement E-match registration.
- Extended `ExplicitLean.Grind.Metadata` with the narrow
  `explicit_grind_def Function.update` operation. It uses the exact generated
  equation theorem and disables pattern normalization; it does not delete
  metadata. Added a pinned stock/replacement differential fixture.
- `replay_module.py` imports the helper for Function.Basic; pipeline checks now
  cover all 29 overlay entries and the Function metadata differential.

## Checks

- Fresh current-main T1/T2 replay (`/tmp/T60-function-basic-fresh-20260919T0540`):
  **25/25**, stock whole-module compile, 6.0s.
- Fresh final overlay replay (`/tmp/T60-function-basic-fresh-20260919T0620`):
  **25/25**, 25 replayed, 0 unresolved/render/compile failures, 6.0s.
- `python3 -B Experiment/pipeline/check_pipeline.py`: **364 checks passed**.
- `python3 -B Experiment/check_simp_family_lint.py`: **46 passed, 2 skipped**;
  fresh generated Function.Basic lint: **0 findings**.
- Fresh strict compile via `Toolchain/SimpDisabled/run.py`: **rc 0**, fresh
  Function.Basic olean `/tmp/T60-function-basic-strict-20260919T0625`.
  The translated-root audit resolves fresh Logic.Basic and Function.Basic
  oleans from `/tmp/T60-function-basic-translated-root-20260919T0630`.
- Dependent stock probes importing that translated root passed for
  `Logic.IsEmpty.Basic`, `Logic.Function.Conjugate`, and a Function.Basic
  declaration probe (fresh oleans, 1.7s/1.7s/under 1s). A patched strict
  dependent import probe was attempted but the pinned compiler exited 245
  (segmentation fault while loading the translated dependency cone), so no
  strict dependent pass is claimed.
- Stock/generated `#print axioms` comparison passed for all 13 changed
  declarations; both sides have identical axiom sets. `py_compile` and
  `git diff --check` passed.

## Limitations

The T59 `eqComm`/`iffComm` source blockers remain unchanged. The strict root
uses fresh Logic.Basic/Function.Basic outputs plus copied pinned dependency
oleans solely to establish import resolution; whole-tree acceptance is not
claimed.
