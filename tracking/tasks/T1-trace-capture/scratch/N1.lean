import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace N1
-- inaccessible hypothesis name used as a rewrite rule
example (a b : Nat) : a = b → a + 0 = b := by
  intro _
  simp_trace (out := "tracking/tasks/T1-trace-capture/scratch/inacc.json") [*]
end N1
