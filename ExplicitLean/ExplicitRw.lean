module
prelude

public meta import ExplicitLean.ExplicitRw.Basic
public meta import ExplicitLean.ExplicitRw.Tactic

/-!
# `explicit_rw`

The product tactic that replays a recorded simp trace positionally, with no
search. Importing this module is all a translated Mathlib file needs.

See `ExplicitLean/ExplicitRw/Tactic.lean` for the surface syntax and
`tracking/SIMP-TRACE-SPEC.md` for the position convention.

This module and everything it imports is product code: it must not call, import
for use, or expand to `Lean.Meta.Simp` or any simp-family tactic. The lint
`Experiment/check_no_simp_family.py` enforces that.
-/
