import Lean

example : True := by
  try simp
  exact True.intro
