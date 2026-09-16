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

end ExplicitRwTest.Lemmas
