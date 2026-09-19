import Mathlib

example (n : Nat) : (n : Int) = n := by
  norm_cast
