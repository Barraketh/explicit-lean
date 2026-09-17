/- Focused T22 source-argument identity fixtures. -/
import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic

namespace ExplicitLean.SimpTrace.T22

theorem foo (a b : Nat) (h : a = b) : a = b := h

structure EqWitness (a b : Nat) where
  eq : a = b

example : (if False then True else False) ↔ False := by
  simp_trace [if_neg fun h => False.elim h] =>trace "test/SimpTrace/out/t22_if_neg.json"

example (a b : Nat) (H : EqWitness a b) : a = b := by
  simp_trace [H.eq] =>trace "test/SimpTrace/out/t22_field_local.json"

example {α : Sort} (a : α) : HEq a a := by
  simp_trace [heq_comm (a := a)] =>trace "test/SimpTrace/out/t22_named_arg.json"

example (a b : Nat) (h : b = a) : a = b := by
  -- λ before the call exercises scalar offsets before and inside the argument.
  simp_trace [← foo b a h] =>trace "test/SimpTrace/out/t22_reverse.json"

example (p q : Prop) (h : p ∧ q) : p ∧ q := by
  simp_trace [h] =>trace "test/SimpTrace/out/t22_one_to_many.json"

example (a b : Nat) (h : a = b) : a = b := by
  simp_trace [h, h] =>trace "test/SimpTrace/out/t22_repeated.json"

example (a b : Nat) : a = b → a = b := by
  intro _
  simp_trace [*] =>trace "test/SimpTrace/out/t22_inaccessible.json"

end ExplicitLean.SimpTrace.T22
