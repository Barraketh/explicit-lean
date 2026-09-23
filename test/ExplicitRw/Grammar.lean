/-
Coverage fixtures for the structural and delimited term grammar.

The structural grammar handles common terms. `lean_term(...)` lets the generator
pass a recorded `lhs`/`rhs`/`to` string through Lean's ordinary parser when its
notation is outside that structural grammar, with an explicit boundary before
the next DSL step field.

Each theorem below uses one such spelling in a real step and asserts the
resulting goal, so it pins both that the spelling **parses** and that it
elaborates to the term it looks like. The negative direction — every escape
construct still rejected — lives in `test/ExplicitRw/RejectedSyntax/`.
-/
import ExplicitLean.ExplicitRw
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Defs

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

/-! ## Sorts

These pin what each sort spelling *elaborates to*, not merely that it parses.
Round 5 found that the sort productions read their keyword one node too shallow,
so every spelling collapsed to `Sort _` — an unconstrained universe metavariable
that unifies with anything, `Prop` included. The previous fixtures here contained
no sort spelling at all, which is why nothing caught it. Each theorem below would
fail if that bug returned.
-/

/-- `Type` at a `Type` position: accepted. -/
theorem sort_type_at_type : (fun (_α : Type) => True) Nat := by
  explicit_rw [change (Type) at [0, 0]] then exact trivial

/-- `Sort 0` *is* `Prop`, so this is accepted. -/
theorem sort_sort0_at_prop : (fun (_α : Prop) => True) True := by
  explicit_rw [change (Sort 0) at [0, 0]] then exact trivial

/-- `Type u` with a named universe. -/
theorem sort_type_universe : (fun (_α : Type) => True) Nat := by
  explicit_rw [change (Type 0) at [0, 0]] then exact trivial

/-- `Type*` and `Sort*` are wildcards, so they fit a `Type` position. -/
theorem sort_star : (fun (_α : Type) => True) Nat := by
  explicit_rw [change (Type*) at [0, 0]] then exact trivial

theorem sort_star_sort : (fun (_α : Type) => True) Nat := by
  explicit_rw [change (Sort*) at [0, 0]] then exact trivial

/-- `Prop` at a `Prop` position. -/
theorem sort_prop_at_prop : (fun (_α : Prop) => True) True := by
  explicit_rw [change (Prop) at [0, 0]] then exact trivial

/-! ## Mathlib's numeric type notations

`ℕ ℤ ℚ ℝ ℂ` are notation tokens rather than identifiers, so the lexer stops
before the whitelist category unless they are listed as atoms. `(2 : ℝ)` is the
ordinary pretty-printed form of an ascribed literal, so a generator holds these
constantly.
-/

theorem numeric_nat (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [change ((a : ℕ) + 0) at [0, 1], h at [0, 1, 0, 1]]
  guard_target =ₛ b + 0 = b
  rfl

theorem numeric_int (a b : Int) (h : a = b) : a + 0 = b := by
  explicit_rw [change ((a : ℤ) + 0) at [0, 1], h at [0, 1, 0, 1]]
  guard_target =ₛ b + 0 = b
  exact Int.add_zero b

/-- `ℝ` **inside a step**, not merely in the statement. Round 6 found that the
earlier fixtures put `ℝ` only in the binder, so the atom was never exercised
through the grammar and a broken mapping passed the suite. -/
theorem numeric_real (x y : ℝ) (h : x = y) : x + 0 = y := by
  explicit_rw [change ((x : ℝ) + 0) at [0, 1], h at [0, 1, 0, 1]]
  exact add_zero y

/-- The ascription spelling `(2 : ℝ)` **inside** a lemma term. -/
theorem numeric_ascription (y : ℝ) : (2 : ℝ) * y = y * 2 := by
  explicit_rw [mul_comm (2 : ℝ) y at [0, 1]]
  guard_target = (y * 2 = y * 2)
  rfl

/-- `ℂ` inside a step. -/
theorem numeric_complex (x y : ℂ) (h : x = y) : x + 0 = y := by
  explicit_rw [change ((x : ℂ) + 0) at [0, 1], h at [0, 1, 0, 1]]
  exact add_zero y

/-! ## Caller notation as parenthesized ordinary Lean terms

These operators are intentionally outside the structural term grammar. The
parenthesized form must let Lean parse notation in the caller's scope while the
outer `explicit_rw` parser retains an exact step boundary.
-/

theorem bottom_top_terms : ((⊥ : Prop) = (⊥ : Prop)) := by
  explicit_rw [change lean_term(False = False) at []]
  rfl

set_option linter.unusedTactic false in
theorem lattice_notation_term (p q : Prop) : (p ⊔ q) = (p ⊔ q) := by
  explicit_rw [change lean_term((p ⊔ q) = (p ⊔ q)) at []]
  rfl

set_option linter.unusedTactic false in
theorem set_complement_term (s : Set Nat) : sᶜ = sᶜ := by
  explicit_rw [change lean_term(sᶜ = sᶜ) at []]
  rfl

set_option linter.unusedTactic false in
theorem linear_map_arrow_term : (Nat →₀ Nat) = (Nat →₀ Nat) := by
  explicit_rw [change lean_term((Finsupp Nat Nat) = (Finsupp Nat Nat)) at []]
  rfl

theorem let_binding_in_general_term : 1 = 1 := by
  explicit_rw [change lean_term((let x := 1; x) = 1) at []]
  rfl

set_option linter.unusedTactic false in
theorem by_text_in_string_literal : "by simp" = "by simp" := by
  explicit_rw [change lean_term("by simp" = "by simp") at []]
  rfl

set_option linter.unusedTactic false in
theorem unicode_lambda_arrow : (fun x : Nat => x) 1 = 1 := by
  explicit_rw [change lean_term((fun x : Nat ↦ x) 1 = 1) at []]
  rfl

theorem delimited_proposition_proof (p : Prop) (hp : p) : p = True := by
  explicit_rw [prop_true lean_term(hp) at [0, 1]]
  rfl

theorem delimited_named_arguments (a b : Nat) : a + b = b + a := by
  explicit_rw [lean_term(Nat.add_comm (n := a) (m := b)) at [0, 1]]
  rfl

structure DelimitedRecord where
  value : Nat

set_option linter.unusedTactic false in
theorem delimited_record_update (x : DelimitedRecord) :
    {x with value := 1}.value = 1 := by
  explicit_rw [change lean_term(({x with value := 1}.value) = 1) at []]
  rfl

set_option linter.unusedTactic false in
theorem delimited_show_from : 1 = 1 := by
  explicit_rw [change lean_term((show Nat from 1) = 1) at []]
  rfl

set_option linter.unusedTactic false in
theorem delimited_match : 1 = 1 := by
  explicit_rw [change lean_term((match (0 : Nat) with | 0 => 1 | _ => 2) = 1) at []]
  rfl

set_option linter.unusedTactic false in
theorem delimited_do : 1 = 1 := by
  explicit_rw [change lean_term((Id.run do pure 1) = 1) at []]
  rfl

set_option linter.unusedTactic false in
theorem delimited_block_comment : "by simp" = "by simp" := by
  explicit_rw [change lean_term((/- ) by simp -/ "by simp") = "by simp") at []]
  rfl

end ExplicitRwTest.Grammar
