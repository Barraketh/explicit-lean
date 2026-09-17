import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
set_option linter.unusedVariables false
namespace A6
-- D1: (config := ...) rejected by the parser
example : (2:Nat) + 2 = 4 := by
  simp_trace (config := { decide := true })
end A6
