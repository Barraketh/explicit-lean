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

/-! ### `Iff`-returning simprocs wrap their proof in `propext` (REVIEW-5 2)

`propext : (a ↔ b) → a = b` has one explicit argument and it is a proof, so the
generic `classifyProof` walk used to call `propext` itself the rewriting lemma
and emit `rw [propext]` — a step no replayer can execute. `propext` is plumbing
exactly as `Eq.mpr`/`of_eq_true` are; the rewriting lemma is the *inner* proof's
head, and the rewrite is an iff rewrite, which `rw` performs like any other. -/

def FixtureTag (n : Nat) : Prop := n = n

theorem fixtureTag_iff (n : Nat) : FixtureTag n ↔ True := by
  unfold FixtureTag; simp

open Lean Meta Simp in
/-- A simproc whose proof is `propext (fixtureTag_iff n)`: one lemma applied,
under `propext`. The step must name `fixtureTag_iff`, not `propext`. -/
simproc_decl fixtureTagProc (FixtureTag _) := fun e => do
  let_expr FixtureTag n := e | return .continue
  let pf := mkApp3 (mkConst ``propext) (mkApp (mkConst ``FixtureTag) n)
              (mkConst ``True) (mkApp (mkConst ``fixtureTag_iff) n)
  return .done { expr := mkConst ``True, proof? := pf }

attribute [simp] fixtureTagProc

example (k : Nat) : FixtureTag k := by
  simp_trace =>trace "test/SimpTrace/out/propext_lemma.json"

/- The negative control — a simproc whose `propext` argument is *not* a single
lemma application — is unresolved by design, so it lives in
`UnresolvedFixtures.lean` alongside the other such cases. -/

/-! ### `simp [h]` on a local hypothesis (REVIEW-5 1)

simp records a hypothesis named in the argument list as `Origin.stx` — the
syntax the user wrote — not `Origin.fvar`, which `simp [*]` produces. The spec
is unconditional on both the `local` object and the `prop` flag, so the two
forms must agree. The written syntax still supplies `name` and `dir`, because
only it carries a leading `←`. -/

/-- An equational local hypothesis: carries `local`, no `prop`. -/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace [h] =>trace "test/SimpTrace/out/local_named_eq.json"

/-- A Prop-valued hypothesis used as `p = True`: carries `prop: "true"`. -/
example (p : Prop) (h : p) : p ∧ True := by
  simp_trace [h] =>trace "test/SimpTrace/out/local_named_prop_true.json"

/-- A negated hypothesis used as `p = False`: carries `prop: "false"`. -/
example (p : Prop) (h : ¬p) : (p ∧ True) = False := by
  simp_trace [h] =>trace "test/SimpTrace/out/local_named_prop_false.json"

/-- An inaccessible hypothesis: `name` is the display form `a✝`, and `local`
carries the full hygienic user name, so the two can never be confused. -/
example (a b : Nat) : a = b → a + 0 = b := by
  intro _
  simp_trace [*] =>trace "test/SimpTrace/out/local_named_inaccessible.json"

/-- A reverse-direction hypothesis: `dir` stays `"rev"` while `local` is
resolved, which is why the written syntax is kept for `name`/`dir`. -/
example (a b : Nat) (h : b = a) : a + 0 = b := by
  simp_trace [← h] =>trace "test/SimpTrace/out/local_named_rev.json"

/-- `dreduceIte` (REVIEW-5 4): upstream's `dsimpImpl` ends in
`withInDSimpWithCache`, which sets `Context.inDSimp`. Stock `dreduceIte` reads
that flag and returns `.continue` unless it is set, so a fork that never entered
`withInDSimp` could not reduce an `ite` in `dsimp` mode at all. Here the `Fin`
index is reached through the `dsimp` path, and stock `simp` really does reduce
it to `Fin 3` — the reviewer expected no observable difference, but there is
one. -/
example (f : Nat → Nat) : (∀ x : Fin (if True then 3 else 4), f x.val = f x.val) := by
  simp_trace =>trace "test/SimpTrace/out/dreduce_ite.json"

/-! ### Hypothesis names are resolved from the proof term, not from characters

`resolveStxOrigin` reads the fvar off the simp theorem's stored proof, walking
the wrappers simp adds (`eq_true h`, `And.left h`, ...). A character whitelist
dropped every non-ASCII name, losing `local` and `prop` for names Mathlib uses
constantly (REVIEW-6 1). -/

example (a b : Nat) (h₃ : a = b) : a + 0 = b := by
  simp_trace [h₃] =>trace "test/SimpTrace/out/name_subscript.json"

example (a b : Nat) (hα : a = b) : a + 0 = b := by
  simp_trace [hα] =>trace "test/SimpTrace/out/name_greek.json"

example (a b : Nat) (h' : a = b) : a + 0 = b := by
  simp_trace [h'] =>trace "test/SimpTrace/out/name_prime.json"

/-- A projection of a local: the origin resolves through `And.left` to `hβ`,
so `local` names the hypothesis the projection came from while `name` keeps the
projection syntax the user wrote. -/
example (p q : Prop) (hβ : p ∧ q) : p ∧ True := by
  simp_trace [hβ.1] =>trace "test/SimpTrace/out/name_projection.json"

/-- A Unicode-named inaccessible: `name` is the display form, `local.userName`
the full hygienic name. -/
example (pα : Prop) : pα → pα ∧ True := by
  intro _
  simp_trace [*] =>trace "test/SimpTrace/out/name_unicode_inaccessible.json"

/-! ### Explicit arguments are recorded in `args` (REVIEW-6 2)

A lemma's explicit arguments are what a replayer writes after its name. An
explicit *instance*-typed argument especially cannot be left to synthesis: with
two instances in scope, synthesis may pick a different one than simp used, and
the step would be silently wrong. Every explicit argument is recorded, in the
lemma's own order, and `checkArgsElaborate` confirms `name` applied to them
still elaborates. -/

class FixtureWidget (α : Type) where val : Nat
instance fixtureW1 : FixtureWidget Nat := ⟨1⟩
instance fixtureW2 : FixtureWidget Nat := ⟨99⟩

def FixtureTagE (n : Nat) : Prop := n = n

theorem fixtureTagE_lem (w : FixtureWidget Nat) (n : Nat) : FixtureTagE n = True := by
  unfold FixtureTagE; simp

open Lean Meta Simp in
/-- The simproc passes `fixtureW2` explicitly; `args` must name it, or replay
synthesises `fixtureW1` instead. -/
simproc_decl fixtureTagEProc (FixtureTagE _) := fun e => do
  let_expr FixtureTagE n := e | return .continue
  let pf := mkApp2 (mkConst ``fixtureTagE_lem) (mkConst ``fixtureW2) n
  return .done { expr := mkConst ``True, proof? := pf }

attribute [simp] fixtureTagEProc

example (k : Nat) : FixtureTagE k := by
  simp_trace =>trace "test/SimpTrace/out/args_instance.json"

def FixtureTagT (n : Nat) : Prop := n = n

theorem fixtureTagT_lem (n : Nat) (m : Nat) : FixtureTagT (n + m) = True := by
  unfold FixtureTagT; simp

open Lean Meta Simp in
/-- Two explicit *term* arguments, both subterms of the position: they are
recorded in `args` in the lemma's order, so replay writes
`rw [fixtureTagT_lem a b]` rather than relying on unification to split `a + b`. -/
simproc_decl fixtureTagTProc (FixtureTagT (_ + _)) := fun e => do
  let_expr FixtureTagT s := e | return .continue
  let_expr HAdd.hAdd _ _ _ _ a b := s | return .continue
  let pf := mkApp2 (mkConst ``fixtureTagT_lem) a b
  return .done { expr := mkConst ``True, proof? := pf }

attribute [simp] fixtureTagTProc

example (a b : Nat) : FixtureTagT (a + b) := by
  simp_trace =>trace "test/SimpTrace/out/args_term.json"

/-- `exists_prop_congr`: the body hypothesis is under the existential's
antecedent, so its side trace carries that antecedent in `intros`. Its `side`
traces are in the theorem's signature order — the function hypothesis first —
which is what `rw [exists_prop_congr (fun _ => Iff.rfl) hpq]` needs. -/
example (p q r : Prop) (hpq : p = q) : (∃ _ : p, r) = (∃ _ : q, r) := by
  simp_trace [hpq] =>trace "test/SimpTrace/out/user_congr_exists.json"

/-! ### Quantified and wrapped local hypotheses (REVIEW-7 1, 5)

simp stores a quantified hypothesis's proof under a `.lam` binder and already
applied (`h a`), so reading `getAppFn` alone missed the whole class and the step
lost `local` and `prop`. `proofLocal?` walks binders and applications to the
head fvar. `Eq.symm`/`Iff.symm` wrappers flip `dir`; `Iff.mp`/`Iff.mpr` are not
walked at all, because their last argument is a proof of the iff's *left* side,
not the hypothesis the rewrite is by. -/

example (f g : Nat → Nat) (a : Nat) (h : ∀ x, f x = g x) : f a + 0 = g a := by
  simp_trace [h] =>trace "test/SimpTrace/out/local_forall.json"

/-- A conditional quantified hypothesis: the condition becomes a side trace. -/
example (f g : Nat → Nat) (P : Nat → Prop) (a : Nat) (hp : P a)
    (h : ∀ x, P x → f x = g x) : f a + 0 = g a := by
  simp_trace [h, hp] =>trace "test/SimpTrace/out/local_forall_cond.json"

/-- A ∀-quantified Prop-valued hypothesis: carries `prop: "true"`. -/
example (P : Nat → Prop) (c : Nat) (hp : ∀ x, P x) : P c ∧ True := by
  simp_trace [hp] =>trace "test/SimpTrace/out/local_forall_prop.json"

/-- `h.symm` reverses the equation, so `dir` must be `"rev"` — following
`local` with `dir: "fwd"` would rewrite the opposite way. -/
example (a b : Nat) (h : b = a) : a + 0 = b := by
  simp_trace [h.symm] =>trace "test/SimpTrace/out/local_symm.json"

/-- A nested projection of a conjunction resolves to the hypothesis it came
from, while `name` keeps the projection syntax. -/
example (p q r : Prop) (h : p ∧ q ∧ r) : q ∧ True := by
  simp_trace [h.2.1] =>trace "test/SimpTrace/out/local_proj_nested.json"

/-- A projection of a *quantified* hypothesis' instantiation. -/
example (P Q : Nat → Prop) (c : Nat) (h : ∀ x, P x ∧ Q x) : P c ∧ True := by
  simp_trace [(h c).1] =>trace "test/SimpTrace/out/local_proj_applied.json"

/-! ### Side goals from conditional rewrites (REVIEW-9 1)

Every side goal is the lemma hypothesis's *instantiated type*, `pre` is its pp,
positions inside `steps` are relative to that goal, and `close` comes from the
discharger's actual proof -- `true_intro` only when the goal after the steps is
literally `True`. These three pin the cases that previously reported a close
form the goal did not have. -/

/-- `ite_cond_eq_false`: the side goal is `c = False`, discharged from a
hypothesis, so `close.by` is `assumption:<name>` and not `true_intro`. -/
example (P : Prop) [Decidable P] (a b : Nat) (h : ¬ P) : (if P then a else b) = b := by
  simp_trace [h] =>trace "test/SimpTrace/out/side_ite_cond_false.json"

/-- `dite_cond_eq_false`: same condition shape under a *dependent* `if`, where
the branches bind the condition's proof. -/
example (P : Prop) [Decidable P] (f : P → Nat) (g : ¬P → Nat) (h : ¬ P) :
    (dite P f g) = g h := by
  simp_trace [h] =>trace "test/SimpTrace/out/side_dite_cond_false.json"

/-- A conditional lemma whose side goal is a compound `p = False`: the recorded
steps rewrite each conjunct, and the close is read off the goal *after* those
steps (`False = False`, hence `rfl`) rather than off the last step's `after`
(`False`, which is not a close form at all). -/
example (P Q : Prop) [Decidable (P ∧ Q)] (a b : Nat) (hp : ¬ P) :
    (if P ∧ Q then a else b) = b := by
  simp_trace [hp] =>trace "test/SimpTrace/out/side_cond_eq_false.json"

/-! ### `name` is a name, not written syntax (REVIEW-9 2, 3)

The spec's `name` is "<lemma or hyp name>". Pretty-printing the written syntax
put whole terms there -- `heq_comm (a := a)`, `@forall_eq _ p a` -- which no
generator can emit as a name. `name` now comes from the *resolved* origin, so
it is always a bare constant or a local's display name (plus any projection
suffix, which is part of the name); the arguments the syntax applied travel in
`args`, in explicit binder order, and `dir` keeps a leading `←`. -/

/-- Named-argument syntax: `name` is the bare constant and the named argument
becomes positional in `args`.  Two different types, so `heq_eq_eq` (which needs
one) cannot fire first and `heq_comm` is the rewrite under test. -/
example (α β : Type) (a : α) (b : β) : HEq a b ↔ HEq b a := by
  simp_trace [heq_comm (a := a) (b := b)] =>trace "test/SimpTrace/out/name_named_arg.json"

/-- `@`-syntax supplying arguments positionally.  `forall_eq`'s binders are all
*implicit*, so none of them can be written positionally by a replayer and all
are dropped from `args`; unification recovers them from the subterm.  What
matters here is that `name` is the bare constant, never `@forall_eq _ p a`. -/
example (p : Nat → Prop) (a : Nat) : (∀ x, x = a → p x) ↔ p a := by
  simp_trace [@forall_eq _ p a] =>trace "test/SimpTrace/out/name_at_explicit.json"

end ExplicitLean.SimpTrace.Fixtures
