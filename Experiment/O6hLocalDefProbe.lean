import ExplicitLean.SimpExplicit

/- `reduce local_def s` expands exactly the named ambient local let. Its value
   deliberately starts with another `let`, so zeta remains a separate,
   ordered certificate operation. -/
example (n : Nat) : n = n := by
  let s := let t := n; t + 0
  let other := let t := n; t + 0
  change s = n
  fail_if_success
    simp_explicit [reduce zeta, Nat.add_zero, eq_self]
  fail_if_success
    simp_explicit [reduce local_def other, reduce zeta, Nat.add_zero, eq_self]
  fail_if_success
    simp_explicit [reduce zeta, reduce local_def s, Nat.add_zero, eq_self]
  fail_if_success
    simp_explicit [reduce local_def n, reduce zeta, Nat.add_zero, eq_self]
  simp_explicit [reduce local_def s, reduce zeta, Nat.add_zero, eq_self]
