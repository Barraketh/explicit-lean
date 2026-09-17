import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace A9
-- D1 variants, each on its own line
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace (disch := assumption) [h]
end A9
