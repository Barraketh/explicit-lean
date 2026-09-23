import ExplicitLean.SimpTrace
import ExplicitLean.ExplicitRw
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic

namespace ExplicitLean.SimpTrace.SourceAppliedArguments

/-- Local alias avoids coalescing the test source with Mathlib's global simp
entry, so the recorder can authenticate both the applied and bare syntax. -/
theorem if_neg {P : Prop} [Decidable P] {α : Type*} {a b : α}
    (h : ¬ P) : (if P then a else b) = b := by
  exact _root_.if_neg h

example {G : Type*} [GroupWithZero G] {a b : G} (ha : a ≠ 0) :
    a * (a⁻¹ * b) = b := by
  simp_trace only [mul_inv_cancel_left₀ ha] =>trace "SOURCE_APPLIED_GLOBAL_TRACE_PATH"

example {α β : Type*} (f : α → β) (hf : Function.Injective f) {x y : α} :
    f x = f y ↔ x = y := by
  simp_trace only [hf.eq_iff] =>trace "SOURCE_APPLIED_METHOD_TRACE_PATH"

example (x : ℝ) (hx : x < 0) :
    (if 0 ≤ x then (1 : ℝ) else 0) = 0 := by
  simp_trace only [if_neg (not_le.mpr hx)] =>trace "SOURCE_APPLIED_IF_NEG_TRACE_PATH"

example (P : Prop) (hp : P) (f g : Nat → Nat)
    (h : P → ∀ n, f n = g n) (n : Nat) : f n = g n := by
  simp_trace only [(h hp)] =>trace "SOURCE_APPLIED_LOCAL_TRACE_PATH"

example (P : Prop) [Decidable P] (h : ¬ P) (a b : Nat)
    (hEq : (if P then a else b) = a) : b = a := by
  simp_trace (discharger := assumption) only [if_neg] at hEq =>trace "SOURCE_APPLIED_BARE_IF_NEG_TRACE_PATH"
  exact hEq

end ExplicitLean.SimpTrace.SourceAppliedArguments
