module

import Mathlib

/- These are ordinary source-level simp calls.  The focused checker obtains
   their occurrence IDs and owner ranges from SimpInventory rather than
   assigning duplicate IDs by hand. -/

example (n : Nat) : n + 0 = n ∧ n + 0 = n := by
  constructor <;> simp

example (n : Nat) : n + 0 = n ∧ n + 0 = n := by
  constructor
  all_goals simp

example (n : Nat) : (n + 0 = n) ∧ ((n + 0 = n) ∧ (n + 0 = n)) := by
  constructor <;> repeat simp

example (n : Nat) : n + 0 = n := by
  first | rfl | simp

axiom f2ProbeP : Prop

example (h : f2ProbeP) (n : Nat) : n + 0 = n ∧ f2ProbeP := by
  first
  | (simp only [Nat.add_zero]; fail)
  | simp [h]
