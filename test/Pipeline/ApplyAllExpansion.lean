import Mathlib

set_option linter.unusedTactic false

theorem originalApplyAll : (True ∧ True) ∧ (True ∧ True) := by
  constructor <;> constructor <;> skip <;> simp

theorem expandedApplyAll : (True ∧ True) ∧ (True ∧ True) := by
  constructor <;> constructor <;> skip
  · skip
    exact True.intro
  · skip
    exact True.intro
  · skip
    exact True.intro
  · skip
    exact True.intro

theorem nestedInlineExpanded (b : Bool) : True := by
  have h : True := by
    cases b
    · exact True.intro
    · exact True.intro
  exact h

theorem nestedMultilineExpanded (b : Bool) : True := by
  have h : True :=
    by
      cases b
      · exact True.intro
      · exact True.intro
  exact h
