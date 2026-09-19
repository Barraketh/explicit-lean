import Mathlib

example (a b : Nat) (h : a = b) : a = b := by
  rw [h]

example : (1 : ℤ) = 1 := by
  rfl
