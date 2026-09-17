import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace A2

-- (1) `at *`: unchanged hyp h2 must survive; check exact hypothesis list.
example (a b c d : Nat) (h1 : a + 0 = b) (h2 : c < d) (h3 : b + 0 = c) : a = a := by
  simp at *
  trace_state
  rfl
example (a b c d : Nat) (h1 : a + 0 = b) (h2 : c < d) (h3 : b + 0 = c) : a = a := by
  simp_trace at *
  trace_state
  rfl

-- (2) hypothesis rewritten to False: simp closes the goal
example (a : Nat) (h : a ≠ a) : False := by
  simp at h
example (a : Nat) (h : a ≠ a) : False := by
  simp_trace at h

-- (3) hypothesis rewritten to True: simp clears it
example (a b : Nat) (h : a = a) (h2 : b = b) : Nat := by
  simp at h h2
  trace_state
  exact a
example (a b : Nat) (h : a = a) (h2 : b = b) : Nat := by
  simp_trace at h h2
  trace_state
  exact a

end A2
