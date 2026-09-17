import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Init
namespace Risk

-- R1: side trace whose `pre` is stated up to instances (Decidable arg differs)
theorem r1 (P : Prop) [inst : Decidable P] (h : ¬P) (a b : Nat) :
    (if P then a else b) = b := by
  simp_trace [h] =>trace "test/SimpTrace/replay/r1.json"

-- R2: side goal containing a metavariable-ish shape (higher-order lemma)
theorem r2 (f : Nat → Nat) (a : Nat) (h : ∀ x, f x = x) :
    (if f a = a then 1 else 2) = 1 := by
  simp_trace [h] =>trace "test/SimpTrace/replay/r2.json"

-- R3: nested side trace two levels deep with intros at both levels
theorem r3 (P : Prop) [Decidable P] (Q : P → Prop) (R : ¬P → Prop) (h : ¬P) :
    dite P Q R ↔ (∃ p, Q p) ∨ (∃ p, R p) := by
  simp_trace [h, exists_prop_of_false, exists_prop_of_true] =>trace "test/SimpTrace/replay/r3.json"

-- R4: side condition discharged under a binder the traversal introduced
theorem r4 (f : Nat → Prop) [∀ n, Decidable (f n)] (h : ∀ n, ¬ f n) :
    (∀ n : Nat, (if f n then True else False)) ↔ ∀ n : Nat, False := by
  simp_trace [h] =>trace "test/SimpTrace/replay/r4.json"
end Risk
