import Lean

def wrapped : Nat := 1

example (a b : Nat) (h : a = b) : a = b := by
  rw [h]
example (a b : Nat) (h : a = b) : a = b := by
  exact h
example : wrapped = 1 := by
  change 1 = 1
  rfl
example : wrapped = 1 := by
  unfold wrapped
  rfl
example : True := by
  exact True.intro
