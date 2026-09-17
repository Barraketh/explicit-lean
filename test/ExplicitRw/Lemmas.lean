/-
Fixtures for the lemma side of `explicit_rw`: rewriting inside a hypothesis,
rewriting with a local equation hypothesis, a conditional lemma whose side
condition is supplied as an explicit argument, and a lemma whose instance
arguments must be synthesized.

Implicits, universes and instances are recovered by ordinary elaboration and
unification against the subterm at the position; nothing is stored for them and
nothing is searched for.
-/
import ExplicitLean.ExplicitRw
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Logic.IsEmpty.Basic

namespace ExplicitRwTest.Lemmas

/-! ## Rewrite inside a hypothesis

The location is transported with `Eq.mp`; the goal is untouched.
-/

theorem in_hypothesis (a b c : Nat) (h : a = b) (hc : a + c = 0) : b + c = 0 := by
  explicit_rw [h at [0, 1, 0, 1]] at hc
  guard_hyp hc :ₛ b + c = 0
  exact hc

theorem in_hypothesis_conv (a b c : Nat) (h : a = b) (hc : a + c = 0) : b + c = 0 := by
  conv at hc => lhs; arg 1; rw [h]
  exact hc

/-! ## Rewrite with a local equation hypothesis

`h` here is an ordinary local hypothesis, not a global lemma.
-/

theorem local_equation (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by
  explicit_rw [h at [0, 1, 1]]
  guard_target =ₛ f b = f b
  rfl

theorem local_equation_conv (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by
  conv => lhs; arg 1; rw [h]

/-! ## A conditional lemma with an explicitly supplied side-condition proof

`Nat.succ_pred_eq_of_pos : 0 < n → n.pred.succ = n`. The side condition is the
explicit argument `hn`; `explicit_rw` never discharges it by search.
-/

theorem conditional (n : Nat) (hn : 0 < n) : (n - 1) + 1 = n := by
  explicit_rw [Nat.succ_pred_eq_of_pos hn at [0, 1]]
  guard_target =ₛ n = n
  rfl

/--
The `conv` cross-check needs a `show` first: `rw` abstracts occurrences
syntactically, so it does not see `n - 1 + 1` as `n.pred.succ`, while
`explicit_rw` unifies the lemma's left side with the subterm at the given
position up to reducible defeq. This is a real difference between the two, not
a mis-stated position.
-/
theorem conditional_conv (n : Nat) (hn : 0 < n) : (n - 1) + 1 = n := by
  show n.pred.succ = n
  conv => lhs; rw [Nat.succ_pred_eq_of_pos hn]

/-! ## A lemma with instance arguments that must be synthesized

`List.append_nil : l ++ [] = l` carries no instance, but `List.length_append`
and the `HAppend`/`Append` instances in the subterm are resolved by unification
and synthesis during elaboration of the lemma term.
-/

theorem instance_args {α : Type} (l : List α) : (l ++ []).length = l.length := by
  explicit_rw [List.append_nil l at [0, 1, 1]]
  guard_target =ₛ l.length = l.length
  rfl

theorem instance_args_conv {α : Type} (l : List α) : (l ++ []).length = l.length := by
  conv => lhs; arg 1; rw [List.append_nil l]

/--
A lemma stated over an arbitrary `AddCommMonoid`, so the rewrite must synthesize
the instance for the concrete type at the position.
-/
theorem instance_synthesized (a : Nat) : a + 0 + 0 = a := by
  explicit_rw [add_zero a at [0, 1, 0, 1], add_zero a at [0, 1]]
  guard_target =ₛ a = a
  rfl

theorem instance_synthesized_conv (a : Nat) : a + 0 + 0 = a := by
  conv => lhs; arg 1; rw [add_zero a]
  conv => lhs; rw [add_zero a]

/-! ## An iff lemma becomes an equation via `propext` -/

theorem iff_lemma (p : Prop) (hp : p ∧ True) : p := by
  explicit_rw [and_true p at []] at hp
  guard_hyp hp :ₛ p
  exact hp

theorem iff_lemma_conv (p : Prop) (hp : p ∧ True) : p := by
  conv at hp => rw [and_true p]
  exact hp

/-! ## A universe-polymorphic lemma

`List.append_nil` is stated for `{α : Type u}`. The universe level is recovered
by ordinary elaboration against the subterm at the position; nothing about it is
stored in the trace.
-/

universe u

theorem universe_polymorphic {α : Type u} (l : List α) :
    (l ++ []).length = l.length := by
  explicit_rw [List.append_nil l at [0, 1, 1]]
  guard_target =ₛ l.length = l.length
  rfl

theorem universe_polymorphic_conv {α : Type u} (l : List α) :
    (l ++ []).length = l.length := by
  conv => lhs; arg 1; rw [List.append_nil l]

/-- The same lemma at two different universes in one file, to pin that the level
is genuinely inferred per use rather than fixed by the first elaboration. -/
theorem universe_polymorphic_prop (l : List Prop) : (l ++ []).length = l.length := by
  explicit_rw [List.append_nil l at [0, 1, 1]]
  guard_target =ₛ l.length = l.length
  rfl

/-! ## A `Sort*`-polymorphic lemma, from a real `IsEmpty` trace

`not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α` is stated for `{α : Sort u}`. The
universe level is fixed by unifying the lemma's left side with the subterm at
the recorded position, so the same lemma replays at `Sort 0` and at `Type` in
this one file. A level left unassigned after matching is a step-indexed error;
`explicit_rw` never defaults one, because defaulting would make the replay
depend on elaboration order and on the import context.

The first theorem is `call01` of the captured `Mathlib.Logic.IsEmpty.Basic`
traces, replayed with the recorded position and direction.
-/

theorem sort_polymorphic_iff {p : Prop} :
    (¬Nonempty p ∧ True) ↔ (IsEmpty p ∧ True) := by
  explicit_rw [not_nonempty_iff at [0, 1, 0, 1]]
  guard_target =ₛ (IsEmpty p ∧ True) ↔ (IsEmpty p ∧ True)
  rfl

theorem sort_polymorphic_iff_conv {p : Prop} :
    (¬Nonempty p ∧ True) ↔ (IsEmpty p ∧ True) := by
  conv => lhs; arg 1; rw [not_nonempty_iff]

/-- The same lemma under a `∀` binder, at `Type` rather than `Prop`. -/
theorem sort_polymorphic_under_binder : ∀ (α : Type), (¬Nonempty α) ↔ IsEmpty α := by
  explicit_rw [not_nonempty_iff at [1, 0, 1]]
  guard_target =ₛ ∀ (α : Type), IsEmpty α ↔ IsEmpty α
  intro α
  rfl

end ExplicitRwTest.Lemmas
