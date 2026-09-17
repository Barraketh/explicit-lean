import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
set_option linter.unusedVariables false
namespace A7
-- D2: +decide -> hard error, but stock simp succeeds
example : (2:Nat) + 2 = 4 := by simp +decide
example : (2:Nat) + 2 = 4 := by simp_trace +decide
end A7
