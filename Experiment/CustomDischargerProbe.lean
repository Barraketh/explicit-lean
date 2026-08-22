import ExplicitLean.SimpExplicit

/- Source-supplied dischargers remain passive in O4.  The original simp call
   still closes the goal, but its operational report is deliberately deferred
   and contains no premise proof or certificate. -/
set_option explicitLean.simpExplicit.passive true in
set_option explicitLean.simpExplicit.report true in
example (n : Nat) : 0 - n = 0 := by
  simp_explicit? (discharger := simp) only [Nat.sub_eq_zero_of_le]
