import Lean

def wrapped : Nat := 1
example : wrapped = 1 := by dsimp [wrapped]
