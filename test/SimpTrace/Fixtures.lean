/-
`simp_trace` fixtures.

Each `simp_trace` call writes its trace JSON to `test/SimpTrace/out/<name>.json`.
`Experiment/check_simp_trace.py` compares each against the expected step
skeleton in `test/SimpTrace/expected/<name>.json`.

Compile with `lake env lean test/SimpTrace/Fixtures.lean` from the repository
root, so the relative `out :=` paths resolve.
-/
import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Group.Basic

namespace ExplicitLean.SimpTrace.Fixtures

/-- A top-level rewrite that closes the goal by `rfl`/`True`. -/
example (a : Nat) : a + 0 = a := by
  simp_trace =>trace "test/SimpTrace/out/top_level_rfl.json"

/-- Two chained rewrites. -/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace [h] =>trace "test/SimpTrace/out/chained.json"

/-- A `←` (reverse) rewrite. -/
example (a b : Nat) (h : b = a) : a + 0 = b := by
  simp_trace [← h] =>trace "test/SimpTrace/out/reverse.json"

/-- A rewrite under a `∀` binder. -/
example (f : Nat → Nat) : ∀ x : Nat, f x + 0 = f x := by
  simp_trace =>trace "test/SimpTrace/out/under_forall.json"

/-- A rewrite under a `fun x =>` binder. -/
example (f : Nat → Nat) : (fun x => f x + 0) = fun x => f x := by
  simp_trace =>trace "test/SimpTrace/out/under_lambda.json"

/-- A rewrite inside a hypothesis. -/
example (a b : Nat) (h : a + 0 = b) : a = b := by
  simp_trace at h =>trace "test/SimpTrace/out/at_hyp.json"
  exact h

/-- `simp [h]` with a local equation. -/
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  simp_trace [h] =>trace "test/SimpTrace/out/local_eq.json"

/-- A conditional lemma whose side condition simp discharged: `Nat.sub_add_cancel`
needs `n ≤ m`, which the discharger proves from the hypothesis `h`. -/
example (m n : Nat) (h : n ≤ m) : m - n + n = m := by
  simp_trace [Nat.sub_add_cancel, h] =>trace "test/SimpTrace/out/conditional.json"

/-- A simproc with a condition it reduces itself (`reduceIte`). -/
example (n : Nat) (h : n = 3) : (if n = 3 then 1 else 2) = 1 := by
  simp_trace [h] =>trace "test/SimpTrace/out/ite.json"

/-- A simproc arithmetic step. -/
example : (2 : Nat) + 3 = 5 := by
  simp_trace =>trace "test/SimpTrace/out/simproc.json"

/-- A definitional step: a reducible definition unfolding. -/
@[reducible] def myId (n : Nat) : Nat := n

example (n : Nat) : myId n = n := by
  simp_trace [myId] =>trace "test/SimpTrace/out/unfold.json"

/-- A definitional step: beta reduction. -/
example (f : Nat → Nat) (n : Nat) : (fun x => f x) n = f n := by
  simp_trace =>trace "test/SimpTrace/out/beta.json"

/-- `+contextual`. -/
example (p q : Prop) : p → (p ∧ q → q) := by
  simp_trace +contextual =>trace "test/SimpTrace/out/contextual.json"

/-- Every parenthesized argument form `simp` accepts must parse, or `simp_trace`
is not substitutable for `simp`. -/
example : (2:Nat) + 2 = 4 := by
  simp_trace (config := { decide := true }) =>trace "test/SimpTrace/out/cfg_paren.json"

example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace (discharger := assumption) [h] =>trace "test/SimpTrace/out/discharger.json"

example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace (disch := assumption) [h] =>trace "test/SimpTrace/out/disch.json"

/-- `+decide` records the decision as an `eq` step, never an unattributed abort. -/
example : (2:Nat) + 2 = 4 := by
  simp_trace +decide =>trace "test/SimpTrace/out/decide.json"

/-- A `-flag` form. -/
example (a : Nat) : a + 0 = a := by
  simp_trace -contextual =>trace "test/SimpTrace/out/minus_flag.json"

/-- `[*]` and `at h ⊢`. -/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace [*] =>trace "test/SimpTrace/out/star_lemmas.json"

example (a b : Nat) (h : a + 0 = b) : a + 0 = b := by
  simp_trace at h ⊢ =>trace "test/SimpTrace/out/at_hyp_goal.json"
  exact h

example (a b : Nat) (h : a + 0 = b) : b + 0 = a := by
  simp_trace at * =>trace "test/SimpTrace/out/at_star.json"
  omega

/-- A shadowed nested binder: the inner `x` shadows the outer one. -/
example (f : Nat → Nat → Nat) :
    (fun x => (fun x => f x (x + 0)) (x + 0)) = (fun x => f x x) := by
  simp_trace =>trace "test/SimpTrace/out/shadowed.json"

/-- A `let`, which simp discharges by zeta reduction. -/
example (a : Nat) : (let y := a + 0; y + 0) = a := by
  simp_trace =>trace "test/SimpTrace/out/zeta.json"

/-- An inaccessible hypothesis: recorded with a `local` object carrying its
user name and context index, never a bare `ctx:` label. -/
example (a b : Nat) : a = b → a + 0 = b := by
  intro _
  simp_trace [*] =>trace "test/SimpTrace/out/inaccessible.json"

/-- A hypothesis that simplifies to `False`, closing by absurdity. -/
example (a : Nat) (h : a ≠ a) : False := by
  simp_trace at h =>trace "test/SimpTrace/out/absurd.json"

/-- Chained `@[reducible]` definitions: exposing the recorded subterm needs a
*sequence* of delta steps at the same position, each recorded separately.
Mathlib routinely stacks these, so a single-reduction probe is not enough. -/
@[reducible] def chain1 (n : Nat) : Nat := n
@[reducible] def chain2 (n : Nat) : Nat := chain1 n
@[reducible] def chain3 (n : Nat) : Nat := chain2 n

example (n : Nat) : chain2 n + 0 = n := by
  simp_trace [chain2, chain1] =>trace "test/SimpTrace/out/chain2.json"

example (n : Nat) : chain3 n + 0 = n := by
  simp_trace [chain3, chain2, chain1] =>trace "test/SimpTrace/out/chain3.json"

/-- An inaccessible hypothesis alongside an accessible local of the *same* base
name.  The step must name `a✝`, never plain `a`: the latter denotes the
accessible `a : ℕ` and would replay against the wrong hypothesis. -/
example (a b : Nat) : a = b → a + 0 = b := by
  intro _
  simp_trace [*] =>trace "test/SimpTrace/out/shadow_inaccessible.json"

/-- A theorem named `with_trace` must still be declarable: the clause keyword is
non-reserved, so importing this module cannot break a Mathlib identifier. -/
theorem with_trace (a : Nat) : a + 0 = a := by simp

example (a : Nat) : a + 0 = a := by
  simp_trace [with_trace] =>trace "test/SimpTrace/out/token_coexist.json"

/-- A call that closes the goal via `True`. -/
example : True := by
  simp_trace =>trace "test/SimpTrace/out/closes_true.json"

/-- `reduceDIte`, the dependent sibling of `reduceIte`.  Its proof is
`dite_cond_eq_true ... (h : c = True)`, one lemma applied, so the amended spec
records it as a `rw` naming that lemma with the condition as a `side`. -/
example (n : Nat) (h : n = 3) :
    (dite (n = 3) (fun _ => 1) (fun _ => 2)) = 1 := by
  simp_trace [h] =>trace "test/SimpTrace/out/dite.json"

/-- A simproc proof headed by a lemma whose condition is *not* a hypothesis.
On `Nat` literals `Nat.reduceEqDiff` fires first; its proof head is
`eq_false_of_decide`, one lemma applied, so this is a `rw` with the decision
procedure as the side close. -/
example : ((1 : Nat) = 2) = False := by
  simp_trace =>trace "test/SimpTrace/out/ctor_eq.json"

/-- `reduceCtorEq` proper: distinct constructors of a user inductive.  Its proof
head is one lemma (`eq_false'`), so the amended spec records a `rw` naming it;
`eq_false'`'s explicit argument is a proof that the constructor equation is
absurd, which the spec's `nofun` close form (fd4419b) describes exactly.
Replay is `exact eq_false' nofun`. -/
inductive FixtureColor where | red | green | blue

example : (FixtureColor.red = FixtureColor.green) = False := by
  simp_trace =>trace "test/SimpTrace/out/ctor_eq_inductive.json"

/-! ### `let` handling under every `zeta` setting (REVIEW-4 defect 1)

The `let` path is where `zeta`, `zetaDelta` and `letToHave` interact.  Under
`zeta := false` the traversal descends into the `let` instead of reducing it,
which is the path that previously produced a wrong position and a leaked `_fvar`.
Both of the reviewer's shapes are fixed here under both settings. -/

/-- Rewrite strictly inside a `let` body, `zeta` on: the `let` is reduced first. -/
example (f : Nat → Nat) (a : Nat) :
    (let x := a; f (x + 0)) = (let x := a; f x) := by
  simp_trace =>trace "test/SimpTrace/out/let_body_zeta_on.json"

/-- A `let` in operand position, `zeta` on. -/
example (a : Nat) : (let x := a; x) + 0 = (let x := a; x) := by
  simp_trace =>trace "test/SimpTrace/out/let_operand_zeta_on.json"

/-- The same with `zeta := false`. -/
example (a : Nat) : (let x := a; x) + 0 = (let x := a; x) := by
  simp_trace (config := { zeta := false })
    =>trace "test/SimpTrace/out/let_operand_zeta_off.json"

/-- `zetaDelta`: a `let`-bound local unfolded because the simp set names it.
This is the configuration of `Mathlib/Logic/Function/Basic.lean:390`, whose
traced copy used to PANIC inside Lean's own matcher with "loose bvar in
expression" — stock `post` had been handed an open term. -/
example (a : Nat) (P : Nat → Prop) (hP : ∀ n, P n) : True := by
  let g : Nat → Nat := fun s => s + 0
  have hg : P (g a) := hP _
  simp_trace only [g] at hg =>trace "test/SimpTrace/out/zeta_delta_at_hyp.json"
  trivial

/-! ### Dependent congruence: the `congr` step kind (spec 3b17247)

`congr` is for the **auto-generated** congruence theorem path
(`Lean.Meta.mkCongrSimp?`, reached from `tryAutoCongrTheorem?`) when the theorem
transports a `CongrArgKind.cast` dependent.  Rewriting the argument by position
alone would then need a cast, so the whole node is recorded as one `congr` step
carrying the argument index and the argument's own steps, positions relative to
it.  Arguments with no cast dependent stay plain `rw` steps. -/

/-- A `cast` whose value argument is rewritten: the proof argument of `cast`
depends on the types, so the auto congruence theorem transports it.  This is the
shape of `Mathlib/Logic/Function/Basic.lean:390`, which used to PANIC. -/
example {α β : Type} (h : α = β) (f : α → α) (a : α) (hfa : f a = a) :
    cast h (f a) = cast h a := by
  simp_trace [hfa] =>trace "test/SimpTrace/out/congr_cast.json"

/-- A nested `cast`: rewriting the innermost value transports two levels of
type-equality proof, so the `congr` step's nested steps sit under a second
`congr`.  This exercises the recursive case of the nested-step validator. -/
example {α β γ : Type} (h₁ : α = β) (h₂ : β = γ) (f : α → α) (a : α)
    (hfa : f a = a) :
    cast h₂ (cast h₁ (f a)) = cast h₂ (cast h₁ a) := by
  simp_trace [hfa] =>trace "test/SimpTrace/out/congr_nested_cast.json"

/-! ### User `@[congr]` theorems (spec 2e73661)

A congruence theorem registered with `@[congr]` and fired through
`trySimpCongrTheorem?` is an ordinary `rw` step naming that theorem, with
`"source": "congr"` and one `side` sub-trace per hypothesis **in order**.  A
hypothesis of implication shape (`c → x = u`) introduces its antecedents first;
their display names are the side trace's `intros`.  Replay is
`rw [ite_congr h₁ h₂ h₃]` with each `hᵢ` proved by its side trace.

This is distinct from the `congr` *kind* above, which is for the auto-generated
`mkCongrSimp?` path with a `CongrArgKind.cast` dependent. -/

/-- `ite_congr` with a contextual hypothesis in a branch: the `then` branch's
hypothesis is `q → a = b`, so its side trace carries `intros`. -/
example (p q : Prop) [Decidable p] [Decidable q] (a b : Nat)
    (hpq : p = q) (hb : q → a = b) :
    (if p then a else a) = (if q then b else a) := by
  simp_trace +contextual [hpq, hb] =>trace "test/SimpTrace/out/user_congr_ite.json"

/-- `dite_congr`: both branches take the condition as a hypothesis, so both
side traces carry `intros`. -/
example (p q : Prop) [Decidable p] [Decidable q] (hpq : p = q)
    (f : p → Nat) (g : ¬p → Nat) (f' : q → Nat) (g' : ¬q → Nat)
    (hf : ∀ h : q, f (hpq ▸ h) = f' h) (hg : ∀ h : ¬q, g (hpq ▸ h) = g' h) :
    dite p f g = dite q f' g' := by
  simp_trace +contextual [hpq, hf, hg]
    =>trace "test/SimpTrace/out/user_congr_dite.json"

/-- `exists_prop_congr`: the body hypothesis is under the existential's
antecedent, so its side trace carries that antecedent in `intros`. -/
example (p q r : Prop) (hpq : p = q) : (∃ _ : p, r) = (∃ _ : q, r) := by
  simp_trace [hpq] =>trace "test/SimpTrace/out/user_congr_exists.json"

end ExplicitLean.SimpTrace.Fixtures
