import ExplicitLean.ExplicitRw
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.Function.Basic

/-!
Focused consumer fixtures for proposition-valued rule applications and the
ordinary fixed-redex rules that occur beside them in the T15 sites.
-/

namespace ExplicitRwTest.Provenance

universe u

open Relator

/-! Proposition proofs are matched only after the selected redex is navigated. -/

example {α β : Type} [IsEmpty α] (R : α → β → Prop) : LeftTotal R = True := by
  explicit_rw [prop_true leftTotal_empty at [0, 1]]
  rfl

example {α β : Type} [IsEmpty β] (R : α → β → Prop) : RightTotal R = True := by
  explicit_rw [prop_true rightTotal_empty at [0, 1]]
  rfl

example {α β : Sort _} (f : α → β) (a : α) :
    (∃ x, f x = f a) = True := by
  explicit_rw [prop_true exists_apply_eq_apply at [0, 1]]
  rfl

example {α β : Sort u} (e : α = β) (b : α) : (cast e b ≍ b) = True := by
  explicit_rw [prop_true cast_heq at [0, 1]]
  rfl

example (p : Prop) [Decidable p] : (p ∨ ¬p) = True := by
  explicit_rw [prop_true Decidable.em at [0, 1]]
  rfl

example (p : Prop) (hp : ¬p) : p = False := by
  explicit_rw [prop_false hp at [0, 1]]
  rfl

/-! Proof-valued binders use the existing ordered, recursive side-proof syntax. -/

theorem proposition_with_side {p q : Prop} (h : p = q) : p = q := h

example (p q : Prop) (h : p = q) : (p = q) = True := by
  explicit_rw [prop_true proposition_with_side at [0, 1] with
    [explicit_rw [h at [0, 1]] then rfl]]
  rfl

theorem proposition_with_instance {p : Prop} {α : Type} [Inhabited α]
    (_x : α) (h : p) : p := h

example (p : Prop) (hp : p) : p = True := by
  explicit_rw [prop_true proposition_with_instance 0 at [0, 1] with [exact hp]]
  rfl

/-! Ordinary rules still take their explicit/local evidence at a fixed redex. -/

example (p : Prop) [Decidable p] (hp : ¬p) (a b : Nat) :
    (if p then a else b) = b := by
  explicit_rw [if_neg hp at [0, 1]]
  rfl

example (p : Prop) [Decidable p] (hp : p) (x : p → Nat) (y : ¬p → Nat) :
    dite p x y = x hp := by
  explicit_rw [dif_pos hp at [0, 1]]
  rfl

def IsPartialInv {α β} (f : α → β) (g : β → Option α) : Prop :=
  ∀ x y, g y = some x ↔ f x = y

theorem IsPartialInv.eq {α β} {f : α → β} {g} (H : IsPartialInv f g) (x) :
    g (f x) = some x := (H _ _).2 rfl

example {α β} (f : α → β) (g : β → Option α) (H : IsPartialInv f g) (x : α) :
    g (f x) = some x := by
  explicit_rw [IsPartialInv.eq H x at [0, 1]]
  rfl

example {α β γ} {f : α → β} {g : α → γ} (hf : g.FactorsThrough f)
    (e' : β → γ) (a : α) : Function.extend f g e' (f a) = g a := by
  explicit_rw [Function.FactorsThrough.extend_apply hf e' a at [0, 1]]
  rfl

example {α β γ} {f : α → β} (hf : Function.Injective f) (g : α → γ) (e' : β → γ) (a : α) :
    Function.extend f g e' (f a) = g a := by
  explicit_rw [Function.Injective.extend_apply hf g e' a at [0, 1]]
  rfl

example {α : Type} [Subsingleton α] (x y z : α) : (x, z) = (y, z) := by
  explicit_rw [Subsingleton.elim x y at [0, 1, 0, 1]]
  rfl

end ExplicitRwTest.Provenance
