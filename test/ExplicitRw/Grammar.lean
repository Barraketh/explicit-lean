/-
Coverage fixtures for the whitelisted term grammar.

Round 4 widened `explicitRwTerm` to what Lean's pretty printer actually emits, so
that a generator can pass a recorded `lhs`/`rhs`/`to` string through rather than
re-rendering it into a narrower dialect.

Each theorem below uses one such spelling in a real step and asserts the
resulting goal, so it pins both that the spelling **parses** and that it
elaborates to the term it looks like. The negative direction — every escape
construct still rejected — lives in `test/ExplicitRw/RejectedSyntax/`.
-/
import ExplicitLean.ExplicitRw
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Group.Nat

namespace ExplicitRwTest.Grammar

/-! ## Conditionals

`reduceIte` is a common simproc, and T1 records its `lhs` in `if _ then _ else _`
spelling, so this must parse verbatim rather than as `ite True 1 2`.
-/

theorem ite_spelling : (if True then 1 else 2) + 0 = 1 := by
  explicit_rw [eq ((if True then 1 else 2) = 1) by rfl at [0, 1, 0, 1]]
  guard_target =ₛ 1 + 0 = 1
  rfl

theorem dite_spelling (a b : Nat) (h : a = b) :
    (if _hc : True then a else a) = b := by
  -- `dite`'s branches are lambdas, so the body is one binder crossing down.
  explicit_rw [h at [0, 1, 0, 1, 1], h at [0, 1, 1, 1]]
  guard_target =ₛ (if _hc : True then b else b) = b
  rfl

/-! ## Projection on a parenthesised term

The spec's `absurd:<hyp>` close form needs this whenever the contradiction is an
application rather than a bare name.
-/

theorem proj_on_application (p : Prop) (hp : ¬p) (q : p) (a b : Nat) : a = b := by
  explicit_rw [] then exact (hp q).elim

theorem proj_numeric_index (a b c : Nat) (h : a = c) : (a, b).1 = c := by
  explicit_rw [h at [0, 1, 1, 0, 1]]
  guard_target =ₛ (c, b).1 = c
  rfl

/-! ## Binders as the pretty printer writes them: untyped and unparenthesised -/

theorem fun_untyped (f g : Nat → Nat) (h : ∀ x, f x = g x) :
    (fun x => f x) = (fun x => g x) := by
  explicit_rw [h x at [0, 1, 1]]
  guard_target =ₛ (fun x => g x) = (fun x => g x)
  rfl

theorem forall_untyped (p q : Nat → Prop) (h : ∀ x, p x = q x) :
    (∀ x, p x) = (∀ x, q x) := by
  explicit_rw [h x at [0, 1, 1]]
  guard_target =ₛ (∀ x, q x) = (∀ x, q x)
  rfl

theorem exists_untyped (p q : Nat → Prop) (h : ∀ x, p x = q x) :
    (∃ x, p x) = (∃ x, q x) := by
  explicit_rw [h x at [0, 1, 1, 1]]
  guard_target =ₛ (∃ x, q x) = (∃ x, q x)
  rfl

theorem forall_typed (p q : Nat → Prop) (h : ∀ x, p x = q x) :
    (∀ x : Nat, p x) = (∀ x : Nat, q x) := by
  explicit_rw [h x at [0, 1, 1]]
  guard_target =ₛ (∀ x : Nat, q x) = (∀ x : Nat, q x)
  rfl

/-! ## Operators Mathlib's pretty printer emits -/

theorem coercion_arrow (m n : Nat) (h : m = n) : ((↑m : Int)) = ((↑n : Int)) := by
  explicit_rw [h at [0, 1, 1]]
  guard_target =ₛ ((↑n : Int)) = ((↑n : Int))
  rfl

theorem negation_prefix (m n : Int) (h : m = n) : -m = -n := by
  explicit_rw [h at [0, 1, 1]]
  guard_target =ₛ -n = -n
  rfl

theorem membership (a b : Nat) (s : Set Nat) (h : a = b) : (a ∈ s) = (b ∈ s) := by
  explicit_rw [h at [0, 1, 1]]
  guard_target =ₛ (b ∈ s) = (b ∈ s)
  rfl

theorem subset_union_inter (s t u : Set Nat) (h : s = t) :
    (s ∪ u ⊆ s ∩ u) = (t ∪ u ⊆ t ∩ u) := by
  explicit_rw [h at [0, 1, 0, 1, 0, 1], h at [0, 1, 1, 0, 1]]
  guard_target =ₛ (t ∪ u ⊆ t ∩ u) = (t ∪ u ⊆ t ∩ u)
  rfl

theorem composition (f g h' : Nat → Nat) (h : f = g) : f ∘ h' = g ∘ h' := by
  explicit_rw [h at [0, 1, 0, 1]]
  guard_target =ₛ g ∘ h' = g ∘ h'
  rfl

theorem dvd_and_prod (a b : Nat) (h : a = b) : (a ∣ b) = (b ∣ b) := by
  explicit_rw [h at [0, 1, 0, 1]]
  guard_target =ₛ (b ∣ b) = (b ∣ b)
  rfl

theorem order_and_ne (a b : Nat) (h : a = b) : (a ≤ b ∧ a ≠ b) = (b ≤ b ∧ b ≠ b) := by
  explicit_rw [h at [0, 1, 0, 1, 0, 1], h at [0, 1, 1, 0, 1]]
  guard_target =ₛ (b ≤ b ∧ b ≠ b) = (b ≤ b ∧ b ≠ b)
  rfl

/-! ## Set-builder, pairs and sorts -/

theorem set_builder (p q : Nat → Prop) (h : ∀ x, p x = q x) :
    {x | p x} = {x | q x} := by
  -- `{x | p x}` is `setOf fun x => p x`, so the binder is crossed at [0,1,1].
  explicit_rw [h x at [0, 1, 1, 1]]
  guard_target =ₛ {x | q x} = {x | q x}
  rfl

theorem pair_spelling (a b c : Nat) (h : a = c) : (a, b) = (c, b) := by
  explicit_rw [h at [0, 1, 0, 1]]
  guard_target =ₛ (c, b) = (c, b)
  rfl

theorem sort_spellings (α β : Type) (h : α = β) : (α × Nat) = (β × Nat) := by
  explicit_rw [h at [0, 1, 0, 1]]
  guard_target =ₛ (β × Nat) = (β × Nat)
  rfl

/-- `Type`, `Prop`, `Type*` and `Sort*` parse in an ascription. -/
theorem sort_ascriptions (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [change ((a : Nat) + 0) at [0, 1], h at [0, 1, 0, 1]]
  guard_target =ₛ b + 0 = b
  rfl

end ExplicitRwTest.Grammar
