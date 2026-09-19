import Mathlib

example (n : Nat) : n + 0 = n := by
  simp_rw [Nat.add_zero]
