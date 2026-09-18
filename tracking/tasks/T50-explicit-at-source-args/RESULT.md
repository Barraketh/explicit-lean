# T50 — preserve explicit-`@` source argument spines

Implemented in commit `d5714bc87bb5fa710c4501e1dd704c3d7c8addb3`.

The whitelist term elaborator previously rebuilt a source argument such as
`@xor_not_left _ b` through nested quotations, equivalent to `(@xor_not_left) _
b`.  Lean then inserted the theorem's implicit binders before applying the
source arguments.  The fix identifies the direct T22 source argument head and
application spine, and reconstructs the ordinary parser application node with
the explicit marker on the head, preserving Lean's explicit/implicit binder
semantics without parsing `callText` or inspecting proof terms.

Added `test/ExplicitRw/SourceAtArguments.lean` covering the two actual
`Mathlib/Logic/Basic.lean` shapes:
`@xor_not_left _ b` (occurrence `8e17e105590e562a`) and
`@forall_eq _ p a` (occurrence `42f1163b9fd99b7b`).

Checks:

* `lake env lean test/ExplicitRw/SourceAtArguments.lean` — pass.
* Generic `Mathlib/Logic/Basic.lean` replay with only these two overrides
  disabled — whole-module compile exit 0; 31/31 sites replayed, including both
  target sites, and the translated module was published.
* `python3 -B Experiment/pipeline/check_pipeline.py` — 331 checks pass.
* `python3 -B Experiment/check_simp_family_lint.py` — 46 pass, 2 opt-in sweep
  tests skipped.
* `python3 -B Experiment/check_no_simp_family.py` — pass (4 files scanned).
* `git diff --check` — pass.
