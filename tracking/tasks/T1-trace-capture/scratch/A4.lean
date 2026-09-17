import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace A4
-- simp [*]
example (a b c : Nat) (h : a = b) : a + 0 = b := by
  simp [*]
example (a b c : Nat) (h : a = b) : a + 0 = b := by
  simp_trace [*]

-- simp only [] at h  (no lemmas)
example (a b : Nat) (h : a + 0 = b) : True := by
  simp only [] at h
  trace_state
  trivial
example (a b : Nat) (h : a + 0 = b) : True := by
  simp_trace only [] at h
  trace_state
  trivial
end A4
