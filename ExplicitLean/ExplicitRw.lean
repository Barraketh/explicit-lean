module
prelude

public meta import ExplicitLean.ExplicitRw.Basic
public meta import ExplicitLean.ExplicitRw.Tactic
public meta import ExplicitLean.ExplicitRw.LocalHandles
public meta import ExplicitLean.ExplicitRw.Operational

/-!
# Explicit rewrite tactics

This module exposes the existing positional trace replayer and the separate
closed `explicit_rw_v2` operational DSL. Both are search-free; the v2 parser
does not overload or dispatch through the existing tactic.

See `ExplicitLean/ExplicitRw/Tactic.lean` for the existing trace-replay syntax,
`ExplicitLean/ExplicitRw/Operational.lean` for `explicit_rw_v2`, and
`tracking/SIMP-TRACE-SPEC.md` for the position convention.

This module and everything it imports is product code: it must not call, import
for use, or expand to `Lean.Meta.Simp` or any simp-family tactic. The lint
`Experiment/check_no_simp_family.py` enforces that.
-/
