import ExplicitLean.SimpExplicit

/- This theorem is intentionally not tagged `[simp]`.  Recording is allowed to
   use it because it is supplied explicitly; replay must use only the emitted
   rule and the recorded closed premise. -/
theorem guardedSub {n m : Nat} (h : n ≤ m) : n - m = 0 :=
  Nat.sub_eq_zero_of_le h

set_option explicitLean.simpExplicit.report true in
example (n : Nat) : 0 - n = 0 := by
  simp_explicit? only [guardedSub, Nat.zero_le]
