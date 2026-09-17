import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
set_option linter.unusedVariables false
namespace P3
example (f : Nat → Nat → Nat) : (fun x => (fun x => f x (x + 0)) (x + 0)) = (fun x => f x x) := by
  simp
example (a : Nat) : (let y := a + 0; y + 0) = a := by
  simp
end P3
