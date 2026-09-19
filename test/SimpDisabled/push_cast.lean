import Mathlib

example (m n : Nat) : ((m + n : Nat) : Int) = m + n := by
  push_cast
