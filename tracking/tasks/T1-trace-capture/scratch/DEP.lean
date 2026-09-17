import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace DEP
-- `at h` where h' depends on h
example (a b : Nat) (h : a + 0 = b) (h' : h = h) : True := by
  simp at h
  trace_state
  trivial
example (a b : Nat) (h : a + 0 = b) (h' : h = h) : True := by
  simp_trace at h
  trace_state
  trivial
end DEP
