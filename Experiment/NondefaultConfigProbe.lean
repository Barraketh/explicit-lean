import ExplicitLean.SimpExplicit
import Mathlib.Data.Nat.Basic

namespace NondefaultConfigProbe

example (n : Nat) : n + 0 = n := by
  set_option explicitLean.simpExplicit.passive true in
    set_option explicitLean.simpExplicit.occurrenceId "nd-target" in
      simp_explicit? +contextual [Nat.add_zero]

example (n : Nat) (h : n + 0 = n) : n = n := by
  set_option explicitLean.simpExplicit.passive true in
    set_option explicitLean.simpExplicit.occurrenceId "nd-hyp" in
      simp_explicit? +contextual [Nat.add_zero] at h
  rfl

example (n : Nat) : n + 0 = n ∧ n + 0 = n := by
  simp_explicit_body_scope "nd-multi-body" in
    constructor <;>
      set_option explicitLean.simpExplicit.passive true in
        set_option explicitLean.simpExplicit.occurrenceId "nd-multi" in
          simp_explicit? +contextual [Nat.add_zero]

end NondefaultConfigProbe
