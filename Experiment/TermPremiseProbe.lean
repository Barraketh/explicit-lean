import ExplicitLean.SimpExplicit

/- The opaque value prevents the target from closing before the guarded rule
   is attempted. The untagged axiom is supplied explicitly and its premise is
   discharged only by the recorded `eq_self`/`and_self` proof. -/
opaque guardedNat : Nat := 0
axiom guardedEqConj (h : (0 : Nat) = 0 ∧ (0 : Nat) = 0) :
  guardedNat + 0 = guardedNat

set_option explicitLean.simpExplicit.report true in
example : guardedNat + 0 = guardedNat := by
  simp_explicit? only [guardedEqConj, eq_self, and_self]

