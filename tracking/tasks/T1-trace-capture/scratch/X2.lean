import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace X2
example (a : Nat) : ∃ n, n + 0 = a := by
  refine ⟨?_, ?_⟩
  case refine_2 => simp_trace
  exact a
end X2
