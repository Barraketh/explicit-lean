import Lean

set_option explicitLean.simpDisabled false in
example (n : Nat) : n + 0 = n := by
  simp
