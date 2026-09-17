import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace A8
-- discharger: custom simp discharger form
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp (discharger := assumption) [h]
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace (discharger := assumption) [h]

-- simp [h] at h : erasing the hyp from its own simp set
example (a b : Nat) (h : a + 0 = b) : True := by
  simp [h] at h
  trace_state
  trivial
example (a b : Nat) (h : a + 0 = b) : True := by
  simp_trace [h] at h
  trace_state
  trivial
end A8
