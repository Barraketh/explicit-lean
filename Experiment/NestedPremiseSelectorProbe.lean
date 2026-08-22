import ExplicitLean.SimpExplicit

opaque selectorNat : Nat := 0
axiom selectorOuter (h : (0 : Nat) = 0 ∧ (0 : Nat) = 0 ∧ (0 : Nat) = 0) :
  selectorNat + 0 = selectorNat

set_option explicitLean.simpExplicit.report true in
example : selectorNat + 0 = selectorNat := by
  simp_explicit? only [selectorOuter, eq_self, and_self]
