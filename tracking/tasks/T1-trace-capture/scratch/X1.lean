import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace X1
-- residual side goals / dischargeWrapper `simp ... <;>`: metavariable in goal
example (a : Nat) : ∃ n, n + 0 = a := by
  refine ⟨?_, ?_⟩
  case refine_2 => simp
  exact a
end X1
