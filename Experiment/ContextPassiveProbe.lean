import ExplicitLean.SimpExplicit
import Mathlib.Data.Nat.Basic

namespace ContextPassiveProbe

example (n : Nat) (h : n + 0 = n) : n = n := by
  set_option explicitLean.simpExplicit.passive true in
    set_option explicitLean.simpExplicit.report true in
      simp_explicit? [Nat.add_zero, eq_self] at h
  rfl

end ContextPassiveProbe
