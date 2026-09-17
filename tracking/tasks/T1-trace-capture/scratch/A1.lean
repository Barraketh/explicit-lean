import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace A1

-- (1) `at *` with several hyps, some unchanged
example (a b c : Nat) (h1 : a + 0 = b) (h2 : c = c) (h3 : b + 0 = c) : True := by
  simp at *
  trace_state
  trivial

example (a b c : Nat) (h1 : a + 0 = b) (h2 : c = c) (h3 : b + 0 = c) : True := by
  simp_trace at *
  trace_state
  trivial

-- (2) at h ⊢
example (a b : Nat) (h : a + 0 = b) : b + 0 = b := by
  simp at h ⊢
  trace_state
  simp [h]

example (a b : Nat) (h : a + 0 = b) : b + 0 = b := by
  simp_trace at h ⊢
  trace_state
  simp [h]

end A1
