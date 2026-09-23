/-
Structural navigation and the replay **validator**.

Position reconstruction now comes from the forked traversal
(`ExplicitLean/SimpTrace/Traversal.lean`), so this module does not search for
candidate rewrites: three review rounds showed that search was the source of
critical defects (REVIEW-3 C2's exponential chain search, C1's unattributed
firings and M4's leaked `_fvar` in a bridge target). The validator retains the
exact binder-spine abstraction needed to compare open observations against the
closed expression at a recorded position.

What survives is the safety net the task asks for: after the traversal, replay
the recorded steps structurally from the pre-state term — navigate `pos`, check
the subterm equals `before`, substitute `after` — and require the final term to
equal simp's result.  A mismatch is a hard, loud failure.
-/

module

public meta import Lean
public meta import ExplicitLean.SimpTrace.Types

public meta section

namespace ExplicitLean.SimpTrace

open Lean Meta

/-! ### Navigation

Child indices follow the spec: `app f a` has 0 = f, 1 = a; `lam`/`forallE` have
0 = binder type, 1 = body; `letE` has 0 = type, 1 = value, 2 = body; `mdata` and
`proj` have child 0.
-/

/-- Descend one child.  Returns `none` for an out-of-range index. -/
def childAt? (e : Expr) (i : Nat) : Option Expr :=
  match e, i with
  | .app f _, 0 => some f
  | .app _ a, 1 => some a
  | .lam _ t _ _, 0 => some t
  | .lam _ _ b _, 1 => some b
  | .forallE _ t _ _, 0 => some t
  | .forallE _ _ b _, 1 => some b
  | .letE _ t _ _ _, 0 => some t
  | .letE _ _ v _ _, 1 => some v
  | .letE _ _ _ b _, 2 => some b
  | .mdata _ b, 0 => some b
  | .proj _ _ b, 0 => some b
  | _, _ => none

/-- Does descending into child `i` of `e` cross a binder *node* — one that
raises the de Bruijn level inside the subterm?

Every `lam`/`forallE` body and every `letE` body does, including a
**non-dependent** `forallE` (an arrow `p → q`): although simp introduces no term
variable for it, the `Expr` node is still a binder, so `Expr.abstract` and
`Expr.instantiate` count it.  This is the difference between the two depths the
validator needs: `binderNodes` (this one) says how far the de Bruijn indices are
shifted, while the traversal's own binder stack says how many *term variables*
are actually in scope.  Conflating them shifts every index below an arrow, which
is what made a rewrite under `∀ y, y = a' → y = x` fail validation. -/
def crossesBinder (e : Expr) (i : Nat) : Bool :=
  match e, i with
  | .lam .., 1 => true
  | .forallE .., 1 => true
  | .letE .., 2 => true
  | _, _ => false

/-- Replace the subterm at `pos` with `repl`. -/
partial def replaceAt? (e : Expr) (pos : Pos) (repl : Expr) : Option Expr := do
  if pos.size = 0 then
    return repl
  else
    let i := pos[0]!
    let rest := pos.extract 1 pos.size
    let sub ← childAt? e i
    let sub' ← replaceAt? sub rest repl
    match e, i with
    | .app _ a, 0 => some (.app sub' a)
    | .app f _, 1 => some (.app f sub')
    | .lam n _ b bi, 0 => some (.lam n sub' b bi)
    | .lam n t _ bi, 1 => some (.lam n t sub' bi)
    | .forallE n _ b bi, 0 => some (.forallE n sub' b bi)
    | .forallE n t _ bi, 1 => some (.forallE n t sub' bi)
    | .letE n _ v b nd, 0 => some (.letE n sub' v b nd)
    | .letE n t _ b nd, 1 => some (.letE n t sub' b nd)
    | .letE n t v _ nd, 2 => some (.letE n t v sub' nd)
    | .mdata d _, 0 => some (.mdata d sub')
    | .proj s i' _, 0 => some (.proj s i' sub')
    | _, _ => none

/-- Every position at which `target` occurs in `e`, outermost-first.

A simproc's nested `simp` calls *stock* `simpImpl`, so the events it produces
carry no position of their own -- they all arrive at the diverted frame's root
(`[]`).  Prefixing a constant path onto them would make three rewrites of three
different subterms all claim the same position, which type-checks and then
rewrites the wrong subterm (REVIEW-9 1).  The position has to be recovered from
the one thing those events do carry: the subterm they rewrote.

Structural equality only, and *all* occurrences are returned so the caller can
refuse an ambiguous match rather than pick one. -/
partial def occurrencesOf (e target : Expr) : Array Pos :=
  go e #[] #[]
where
  go (e : Expr) (here : Pos) (acc : Array Pos) : Array Pos :=
    let acc := if e == target then acc.push here else acc
    match e with
    | .app f a => go a (here.push 1) (go f (here.push 0) acc)
    | .lam _ t b _ => go b (here.push 1) (go t (here.push 0) acc)
    | .forallE _ t b _ => go b (here.push 1) (go t (here.push 0) acc)
    | .letE _ t v b _ =>
      go b (here.push 2) (go v (here.push 1) (go t (here.push 0) acc))
    | .mdata _ b => go b (here.push 0) acc
    | .proj _ _ b => go b (here.push 0) acc
    | _ => acc

/-- The single position at which `target` occurs in `e`, or `none` when it does
not occur or occurs more than once.  Ambiguity is a genuine unknown here: the
diverted event does not say which occurrence it rewrote. -/
def uniqueOccurrence? (e target : Expr) : Option Pos :=
  match occurrencesOf e target with
  | #[p] => some p
  | _ => none

/-- Navigate to `pos`, returning the subterm and the number of binder *nodes*
crossed to reach it.  Returns `none` for a position the term does not have. -/
partial def navigate? (e : Expr) (pos : Pos) (depth : Nat := 0) :
    Option (Expr × Nat) := do
  if pos.size = 0 then
    return (e, depth)
  else
    let i := pos[0]!
    let rest := pos.extract 1 pos.size
    let sub ← childAt? e i
    navigate? sub rest (if crossesBinder e i then depth + 1 else depth)

/-! ### Open and closed subterms

The traversal observes a subterm with its enclosing binders instantiated as
*free* variables, while the running term still has loose `bvar`s there. The
events carry path-tagged binder slots, including dummy slots for non-dependent
arrows, so the validator abstracts exactly the binder nodes crossed by that
event position.

`Expr.abstract` is used rather than `Expr.replace`: it accounts for binders
*inside* the subterm, so a variable occurring under a nested binder gets the
right de Bruijn index.  (`Expr.replace` does not, and getting this wrong was
review round 1's shadowed-binder defect.)
-/

/-!
### Comparison modulo proof irrelevance

The validator compares a recorded subterm against the running term structurally.
Plain `==` is too strict in one place: two proofs of the same proposition are
interchangeable, and simp freely replaces one by another — `Classical.choose h`
against `Classical.choose ⋯` is the shape REVIEW-4 found at
`Mathlib/Logic/Function/Basic.lean:848`.  Upstream simp's own `isDefEq` runs with
`proofIrrelevance := true`, so rejecting these would make the validator *less*
faithful than the engine it is checking, not more.

We compare structurally but treat two subterms that are both proofs of
definitionally equal propositions as equal.  Everything else still requires
exact structural equality, so nothing carrying computational content is weakened.
-/

/--
Structural equality with proof subterms compared by their types only.

Proof irrelevance is the one thing simp may change without a step being able to
name it, and upstream's own `isDefEq` runs with `proofIrrelevance := true`.
Instance arguments and binder types are deliberately **not** weakened here: when
a congruence theorem transports them it is because the condition changed, and
that transport is recorded as its own `change` step instead (see
`trySimpCongrTheoremT?`), which keeps the validator exact.
-/
partial def eqUpToProofs (a b : Expr) : MetaM Bool := do
  if a == b then return true
  -- `isProof`/`inferType` throw "unexpected bound variable" on a term with
  -- loose bvars, and the validator reaches exactly such subterms: a `dite`
  -- with dependent branches puts the running term's bvars under the binder we
  -- are comparing beneath.  Proof irrelevance is a *relaxation*, so skipping it
  -- for an open subterm only makes the comparison stricter, never wrong — and
  -- it is what stops four stock-provable `Logic/Basic` calls from crashing
  -- instead of being traced (REVIEW-7 4).
  if !a.hasLooseBVars && !b.hasLooseBVars then
    if (← isProof a) && (← isProof b) then
      let ta ← inferType a
      let tb ← inferType b
      -- Both sides are proofs, so proof irrelevance applies as soon as the
      -- propositions agree.  They can differ *syntactically* because a proof is
      -- transported along a rewrite the step itself performed — `by_cases h : p`
      -- turns `p` into `True` in the running term while the recorded proof
      -- still has type `p` — so the comparison must see through the same
      -- unfolding simp's own `isDefEq` does, not only reducible.
      if ← withReducible <| isDefEq ta tb then return true
      if ← withDefault <| isDefEq ta tb then return true
  match a, b with
  | .mdata _ b₁, _ => eqUpToProofs b₁ b
  | _, .mdata _ b₂ => eqUpToProofs a b₂
  | .app f₁ a₁, .app f₂ a₂ => eqUpToProofs f₁ f₂ <&&> eqUpToProofs a₁ a₂
  -- Introduce a real local when descending under a binder, so the bodies are
  -- closed and `isProof` can run on them.  Without this a proof argument under
  -- a `dite`'s dependent binder (`s h` against an elided `s ⋯`) cannot be
  -- compared at all — and calling `isProof` on the open body instead throws
  -- "unexpected bound variable", which crashed four stock-provable
  -- `Logic/Basic` calls (REVIEW-7 4).
  | .lam n t₁ b₁ bi, .lam _ t₂ b₂ _ =>
    eqUpToProofs t₁ t₂ <&&>
      withLocalDecl n bi t₁ fun x =>
        eqUpToProofs (b₁.instantiate1 x) (b₂.instantiate1 x)
  | .forallE n t₁ b₁ bi, .forallE _ t₂ b₂ _ =>
    eqUpToProofs t₁ t₂ <&&>
      withLocalDecl n bi t₁ fun x =>
        eqUpToProofs (b₁.instantiate1 x) (b₂.instantiate1 x)
  | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ =>
    eqUpToProofs t₁ t₂ <&&> eqUpToProofs v₁ v₂ <&&> eqUpToProofs b₁ b₂
  | .proj s₁ i₁ b₁, .proj s₂ i₂ b₂ =>
    if s₁ == s₂ && i₁ == i₂ then eqUpToProofs b₁ b₂ else return false
  | _, _ => return false

/-- Structural equality that accepts **any** two proof subterms as equal.

Weaker than `eqUpToProofs`, which requires their propositions to agree.  Used
only to tell a genuinely wrong trace from one whose sole difference is a proof
simp transported along a rewrite of the proposition that proof is about; the
latter is classified, the former is fatal. -/
partial def eqIgnoringProofs (a b : Expr) : MetaM Bool := do
  if a == b then return true
  if !a.hasLooseBVars && !b.hasLooseBVars then
    if (← isProof a) && (← isProof b) then return true
  match a, b with
  | .mdata _ b₁, _ => eqIgnoringProofs b₁ b
  | _, .mdata _ b₂ => eqIgnoringProofs a b₂
  | .app f₁ a₁, .app f₂ a₂ => eqIgnoringProofs f₁ f₂ <&&> eqIgnoringProofs a₁ a₂
  | .lam n t₁ b₁ bi, .lam _ t₂ b₂ _ =>
    eqIgnoringProofs t₁ t₂ <&&>
      withLocalDecl n bi t₁ fun x =>
        eqIgnoringProofs (b₁.instantiate1 x) (b₂.instantiate1 x)
  | .forallE n t₁ b₁ bi, .forallE _ t₂ b₂ _ =>
    eqIgnoringProofs t₁ t₂ <&&>
      withLocalDecl n bi t₁ fun x =>
        eqIgnoringProofs (b₁.instantiate1 x) (b₂.instantiate1 x)
  | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ =>
    eqIgnoringProofs t₁ t₂ <&&> eqIgnoringProofs v₁ v₂ <&&> eqIgnoringProofs b₁ b₂
  | .proj s₁ i₁ b₁, .proj s₂ i₂ b₂ =>
    if s₁ == s₂ && i₁ == i₂ then eqIgnoringProofs b₁ b₂ else return false
  | _, _ => return false

/--
Abstract the traversal-introduced free variables of `target` so it matches the
open subterm sitting at a position under `binderNodes` binder nodes.

`binderSpine` records every binder body crossed in traversal order, including
non-dependent arrows as dummy slots. `bodyPos` ties each slot to the path that
crossed it, so events at a rebuilt ancestor do not accidentally use variables
opened only in one of its descendants.

`Expr.abstract` is used rather than `Expr.replace`: it accounts for binders
*inside* `target`, so a variable occurring under a nested binder gets the right
de Bruijn index.  (`Expr.replace` does not, and getting that wrong was review
round 1's shadowed-binder defect.)
-/
def abstractSimpFVars (target : Expr) (binderSpine : Array BinderSlot)
    (eventPos : Pos) (binderNodes : Nat) : MetaM Expr := do
  let slots := binderSpine.filter fun slot =>
    let bodyPos := match slot with
      | .fvar p _ | .dummy p => p
    bodyPos.size <= eventPos.size && eventPos.extract 0 bodyPos.size == bodyPos
  unless slots.size == binderNodes do
    throwError "simp_trace: binder-spine mismatch at {eventPos}: position crosses {binderNodes} binder node(s), recorder captured {slots.size}"
  let scope ← slots.mapM fun slot => do
    match slot with
    | .fvar _ id => pure (.fvar id)
    | .dummy _ => return .fvar (← mkFreshFVarId)
  return target.abstract scope

end ExplicitLean.SimpTrace
