import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace M1
-- same lemma at two different instantiations in one call
example (a b : Nat) (f : Nat -> Nat) : f (a + 0) + (b + 0) = f a + b := by
  simp_trace (out := "tracking/tasks/T1-trace-capture/scratch/two_inst.json")
-- mdata via `show`
example (a : Nat) : a + 0 = a := by
  show a + 0 = a
  simp_trace (out := "tracking/tasks/T1-trace-capture/scratch/mdata.json")
end M1
