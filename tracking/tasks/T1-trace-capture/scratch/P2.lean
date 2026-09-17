import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace P2
-- mdata: `show` inserts mdata? try let expressions
example (a : Nat) : (let y := a + 0; y + 0) = a := by
  simp_trace (out := "tracking/tasks/T1-trace-capture/scratch/letE.json")
end P2
