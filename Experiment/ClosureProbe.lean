module

import Mathlib

/- Small syntax-inventoried closure fixture.  The checker runs the complete
   module through the one-recording closure path, then mutates one candidate
   to exercise declaration-group diagnostics. -/

example (n : Nat) : n + 0 = n := by
  simp

example (n : Nat) : n + 0 = n ∧ n + 0 = n := by
  constructor <;> simp

example (n : Nat) : n + 0 = n := by
  first | rfl | simp

example (h : True) (n : Nat) : n + 0 = n ∧ True := by
  first
  | (simp only [Nat.add_zero]; fail)
  | simp [h]

example (n : Nat) : n = n := by
  first
  | (simp only [Nat.add_zero]; fail)
  | rfl
