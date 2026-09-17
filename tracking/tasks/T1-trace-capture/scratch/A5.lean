import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace A5

-- Hypothesis ORDER after `at h`: does the rewritten hyp keep its position?
example (a b : Nat) (h : a + 0 = b) (k : Nat) (h2 : k < k) : True := by
  simp at h
  trace_state
  trivial
example (a b : Nat) (h : a + 0 = b) (k : Nat) (h2 : k < k) : True := by
  simp_trace at h
  trace_state
  trivial

-- config: decide
example : (2 : Nat) + 2 = 4 := by
  simp (config := { decide := true })
example : (2 : Nat) + 2 = 4 := by
  simp_trace (config := { decide := true })

-- +decide token form
example : (2 : Nat) + 2 = 4 := by
  simp +decide
example : (2 : Nat) + 2 = 4 := by
  simp_trace +decide

end A5
