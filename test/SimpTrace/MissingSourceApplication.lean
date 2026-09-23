import ExplicitLean.SimpTrace
import Mathlib.Data.Set.Basic

namespace ExplicitLean.SimpTrace.MissingSourceApplication

example {α : Type} (f : Nat → α) (g : Nat) (x : α)
    (hv : ∀ n, n = g → f n = x) : f g = x := by
  simp_trace only [hv g rfl] =>trace "T77_MISSING_APPLIED_LOCAL"

example {α : Type} (f : Nat → α) (g : Nat) (x : α) (hv : ∀ n, f n = x) : f g = x := by
  simp_trace only [hv g] =>trace "T77_MISSING_FORALL_LOCAL"

example {P : Nat → Nat → Prop}
    (h : Membership.mem (setOf fun n : Nat => ∀ g : Nat, P n g) 0) : P 0 3 := by
  simp_trace only [h 3] =>trace "T77_MISSING_MEMBERSHIP_LOCAL"

example (h : ∀ s : Nat, ∃ y : Nat, y = s) (s : Nat) : (h s).choose = s := by
  simp_trace only [(h s).choose_spec] =>trace "T77_MISSING_CHOOSE_SPEC"

example {p : Nat → Prop} (x : {n : Nat // p n}) : p x.val := by
  simp_trace only [x.property] =>trace "T77_MISSING_SUBTYPE_PROPERTY"

example (f : Nat → Nat) (n : Nat) (h : f n = n) : f n = n := by
  simp_trace only [show f n = n from h] =>trace "T77_MISSING_SHOW_FROM"

example (p q : Prop) (h : p ∧ q) : p ∧ q := by
  simp_trace only [h] =>trace "T77_MISSING_MULTIPLE_THEOREMS"
  exact ⟨trivial, trivial⟩

end ExplicitLean.SimpTrace.MissingSourceApplication
