module

import Mathlib

public section

set_option autoImplicit false

-- A proof argument belongs to the whole outer call, not to its continuation.
theorem boundaryNestedRule (n : Nat) : n + 0 = n := by
  simp only [show n + 0 = n from by simp only [Nat.add_zero]]

theorem boundaryNestedSiblings (n : Nat) : n + 0 = n ∧ n * 1 = n := by
  simp only [show n + 0 = n from by simp only [Nat.add_zero],
    show n * 1 = n from by simp only [Nat.mul_one], and_self]

-- Every descendant points directly to the outermost replacement, not a chain.
theorem boundaryNestedDeep (n : Nat) : n + 0 = n := by
  simp only [show n + 0 = n from by
    simp only [show n + 0 = n from by simp only [Nat.add_zero]]]

theorem boundaryNestedDischarger (p q : Prop) (h : p) (hpq : p → q) : q := by
  simp (disch := simp only [h]) only [hpq]

-- The child may succeed while its parent fails. Only the outer outcome is
-- observable to the unchanged alternative.
theorem boundaryNestedFailure (n : Nat) (P : Prop) (h : P) : P := by
  first
  | simp (config := { failIfUnchanged := true }) only
      [show n + 0 = n from by simp only [Nat.add_zero]]
  | exact h

-- The final declaration oracle must compare this computational value too.
def boundaryNestedComputational (n : Nat) : Fin (n + 0 + 1) := by
  simp only [show n + 0 = n from by simp only [Nat.add_zero]]
  exact ⟨0, Nat.zero_lt_succ n⟩

-- Neither call executes; the outer fail-closed dispatcher consumes the child.
theorem boundaryNestedUnobserved (n : Nat) (P : Prop) (h : P) : P := by
  first
  | exact h
  | simp only [show n + 0 = n from by simp only [Nat.add_zero]]
