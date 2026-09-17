import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace A3

-- failIfUnchanged: nothing changes -> both must error the same way
example (a b : Nat) (h : a < b) : a < b := by
  simp
  exact h
example (a b : Nat) (h : a < b) : a < b := by
  simp_trace
  exact h

end A3
