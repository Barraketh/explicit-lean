import ExplicitLean.SimpExplicit

theorem guardedAdd (n : Nat) (_h : 0 ≤ n) : n + 0 = n := Nat.add_zero n

example (n : Nat) : n + 0 = n := by
  simp_explicit [match 1 => Nat.add_zero]

example (n : Nat) : (n + 0) + 0 = n + 0 := by
  simp_explicit [match 2 => Nat.add_zero]

example (n : Nat) : n + 0 = n := by
  simp_explicit [tick 11 => Nat.add_zero]

example (n : Nat) : n + 0 = n := by
  simp_explicit [11 => Nat.add_zero]

example (n : Nat) : (n + 0) + 0 = n + 0 := by
  simp_explicit [match 2 => guardedAdd n using [Nat.zero_le n]]

example (n : Nat) : n + 0 = n := by
  fail_if_success simp_explicit [match 2 => Nat.add_zero]
  simp_explicit [Nat.add_zero]

example (n : Nat) : n + 0 = n := by
  fail_if_success simp_explicit [tick 11 => ↓ Nat.add_zero]
  simp_explicit [Nat.add_zero]

example (n : Nat) : n + 0 = n := by
  fail_if_success simp_explicit [match 0 => Nat.add_zero]
  fail_if_success simp_explicit [tick 0 => Nat.add_zero]
  fail_if_success simp_explicit [0 => Nat.add_zero]
  simp_explicit [Nat.add_zero]
