module

import Mathlib
import ExplicitLean.SimpExplicit

/- A closed `first` owner whose first branch makes progress and then fails.
   The second branch succeeds, so the owner itself has a proof that can be
   exported even though the first dynamic simp attempt is backtracked. -/
example (h : True) (n : Nat) : n + 0 = n ∧ True := by
  first
  | (simp only [Nat.add_zero]; fail)
  | simp [h]
