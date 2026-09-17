import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace A10
-- P1: two identical subterms rewritten by the same lemma (cache)
example (a b : Nat) : (a + 0) + (a + 0) = a + a := by
  simp_trace (out := "tracking/tasks/T1-trace-capture/scratch/dup.json")
-- P2: before occurring both inside and outside a binder
example (f : Nat → Nat) (a : Nat) : (a + 0) + (List.map (fun x => x + 0) [a]).length = a + 1 := by
  simp_trace (out := "tracking/tasks/T1-trace-capture/scratch/binder_dup.json")
end A10
