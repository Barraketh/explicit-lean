import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace P1
-- shadowed binder names, nested
example (f : Nat → Nat → Nat) : (fun x => (fun x => f x (x + 0)) (x + 0)) = (fun x => f x x) := by
  simp_trace (out := "tracking/tasks/T1-trace-capture/scratch/shadow.json")
end P1
