import ExplicitLean.SimpExplicit

set_option explicitLean.simpExplicit.report true in
example (n : Nat) : 0 - n = 0 := by
  simp_explicit?

/- The closed replay has no ambient discharger.  The premise is supplied by
   the explicit provider attached to this theorem attempt. -/
example (n : Nat) : 0 - n = 0 := by
  simp_explicit [Nat.sub_eq_zero_of_le using [Nat.zero_le n]]

example (n : Nat) : 0 - n = 0 := by
  have h_premise_1 : 0 ≤ n := by
    simp_explicit [Nat.zero_le]
  simp_explicit [
    Nat.sub_eq_zero_of_le using [h_premise_1],
    eq_self
  ]

/- A mismatched proposition is rejected by the provider rather than being
   silently discharged. -/
example (n : Nat) : 0 - n = 0 := by
  fail_if_success simp_explicit [Nat.sub_eq_zero_of_le using [Nat.zero_le (n + 1)]]
  simp_explicit [Nat.sub_eq_zero_of_le using [Nat.zero_le n]]

/- Missing and unconsumed premises are distinct replay errors. -/
example (n : Nat) : 0 - n = 0 := by
  fail_if_success simp_explicit [Nat.sub_eq_zero_of_le using []]
  fail_if_success simp_explicit [Nat.sub_eq_zero_of_le using [Nat.zero_le n, Nat.zero_le n]]
  simp_explicit [Nat.sub_eq_zero_of_le using [Nat.zero_le n]]
