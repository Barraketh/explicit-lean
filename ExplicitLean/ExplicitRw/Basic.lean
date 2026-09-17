module
prelude

public meta import Lean.Meta.Basic
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Tactic.Replace
public meta import Lean.Meta.Tactic.Assert
public meta import Lean.Meta.WHNF
public meta import Lean.Meta.SynthInstance
public meta import Lean.Meta.Transform

public meta section

/-!
# `explicit_rw` core: positional rewriting without search

This module implements navigation to a `SubExpr.Pos`-style child-index path and
replacement of the subterm found there, rebuilding a congruence proof back to
the root.

Nothing here calls `Lean.Meta.Simp` or any member of the simp family. The
rewriting primitives used are the ordinary congruence lemmas (`congrArg`,
`congrFun`, `funext`, `forall_congr`, `propext`) plus `Eq.mpr` / `Eq.mp` to
transport the goal or a hypothesis, exactly as a hand-written `rw` proof would.

Positions follow `tracking/SIMP-TRACE-SPEC.md`: for `app f a`, `0 = f` and
`1 = a`; for `lam` / `forallE`, `0 = binder type` and `1 = body`; `mdata` and
`proj` have child `0`. `[]` is the whole location. Crossing a `lam` / `forallE`
body introduces that binder as a local constant for the duration of the step.
-/

namespace ExplicitLean.ExplicitRw

open Lean Meta

/-- A position is a list of raw child indices, outermost first. -/
abbrev Pos := List Nat

/-- Render a position the way the surface syntax writes it. -/
def Pos.render (p : Pos) : String :=
  "[" ++ String.intercalate ", " (p.map toString) ++ "]"

/--
The result of transforming a subterm: the new subterm, and an optional proof
that the old subterm equals the new one. `none` means the replacement is
definitional (`beta`, `unfold`, ...) and needs no proof term.
-/
structure Replacement where
  /-- The subterm after the step. -/
  newExpr : Expr
  /-- Proof of `old = new`, or `none` when the two are definitionally equal. -/
  proof? : Option Expr
  deriving Inhabited

/-- A definitional replacement: no proof obligation beyond defeq. -/
def Replacement.defeq (e : Expr) : Replacement := { newExpr := e, proof? := none }

/-- A propositional replacement carrying an `Eq` proof. -/
def Replacement.eq (e : Expr) (h : Expr) : Replacement := { newExpr := e, proof? := some h }

/-- Errors raised by a single step, tagged with the step index by the caller. -/
def stepError {m : Type → Type} [Monad m] [MonadError m] {α : Type} (idx : Nat) (msg : MessageData) : m α :=
  throwError "explicit_rw: step {idx + 1}: {msg}"

/--
Compose a congruence proof for `app f a` from optional proofs of `f = f'` and
`a = a'`. Returns `none` when both children were definitional, so that a purely
definitional step never manufactures a proof term.
-/
private def congrApp (pos : Pos) (f a : Expr) (hf? ha? : Option Expr) :
    MetaM (Option Expr) := do
  match hf?, ha? with
  | none, none => return none
  | some hf, none =>
    -- `f = f'` gives `f a = f' a` by `congrFun`.
    return some (← mkCongrFun hf a)
  | none, some ha =>
    -- `a = a'` gives `f a = f a'` by `congrArg`, which needs `f` non-dependent:
    -- otherwise `f a` and `f a'` have different types and the rewrite would need
    -- a cast. Check first, so the refusal reads like the other dependent-position
    -- errors instead of leaking an `AppBuilder` message.
    checkNonDependent pos f
    return some (← mkCongrArg f ha)
  | some hf, some ha =>
    checkNonDependent pos f
    return some (← mkCongr hf ha)
where
  /-- Refuse a dependent function, whose congruence would need a cast. -/
  checkNonDependent (pos : Pos) (f : Expr) : MetaM Unit := do
    let fType ← whnf (← inferType f)
    if let .forallE _ _ body _ := fType then
      if body.hasLooseBVars then
        throwError "position {Pos.render pos} rewrites an argument of a dependent \
          function, whose result type mentions that argument; rebuilding the term \
          would need a cast, which `explicit_rw` does not build. Only definitional \
          steps are supported there.\nFunction:{indentExpr f}\nof type:{indentExpr fType}"

/--
Navigate `e` along `pos` and apply `k` to the subterm found there, then rebuild
`e` with a congruence proof back to the root.

`k` receives the subterm (with binders crossed on the way already present in the
local context as free variables). It returns a `Replacement`.

Failure to follow a child index is reported through `onBadPos`, which names the
offending prefix and the kind of expression that could not be descended into.
-/
partial def rewriteAt {m : Type → Type} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    [MonadError m] (e : Expr) (pos : Pos)
    (k : Expr → m Replacement)
    (onBadPos : Pos → Nat → Expr → m Replacement) : m Replacement := do
  go e pos []
where
  go (e : Expr) (rest : Pos) (seen : Pos) : m Replacement := do
    match rest with
    | [] => k e
    | i :: rest' =>
      let seen' := seen ++ [i]
      match e with
      | .app f a =>
        match i with
        | 0 =>
          let r ← go f rest' seen'
          let newE := .app r.newExpr a
          let p? ← (congrApp seen' f a r.proof? none : MetaM _)
          return { newExpr := newE, proof? := p? }
        | 1 =>
          let r ← go a rest' seen'
          let newE := .app f r.newExpr
          let p? ← (congrApp seen' f a none r.proof? : MetaM _)
          return { newExpr := newE, proof? := p? }
        | _ => onBadPos seen i e
      | .mdata d b =>
        -- `mdata` has a single child `0`; the spec's index is consumed here.
        if i == 0 then
          let r ← go b rest' seen'
          return { newExpr := .mdata d r.newExpr, proof? := r.proof? }
        else
          onBadPos seen i e
      | .proj s idx b =>
        if i == 0 then
          let r ← go b rest' seen'
          match r.proof? with
          | none => return { newExpr := .proj s idx r.newExpr, proof? := none }
          | some _ =>
            throwError "position {Pos.render seen'} rewrites the structure argument of \
              a projection `{e}`; a propositional rewrite there needs a congruence \
              lemma this tactic does not build. Use a definitional step, or rewrite \
              at a different position."
        else
          onBadPos seen i e
      | .lam n ty body bi =>
        match i with
        | 0 =>
          let r ← go ty rest' seen'
          match r.proof? with
          | none => return { newExpr := .lam n r.newExpr body bi, proof? := none }
          | some _ =>
            throwError "position {Pos.render seen'} rewrites the binder type of a \
              lambda; that is a dependent position requiring a cast. Only \
              definitional steps are supported there."
        | 1 =>
          withLocalDecl n bi ty fun x => do
            let r ← go (body.instantiate1 x) rest' seen'
            let newBody ← (mkLambdaFVars #[x] r.newExpr : MetaM _)
            match r.proof? with
            | none => return { newExpr := newBody, proof? := none }
            | some h =>
              -- `∀ x, body x = body' x` gives `(fun x => body x) = fun x => body' x`.
              let hAll ← (mkLambdaFVars #[x] h : MetaM _)
              return { newExpr := newBody, proof? := some (← (mkFunExt hAll : MetaM _)) }
        | _ => onBadPos seen i e
      | .forallE n ty body bi =>
        match i with
        | 0 =>
          let r ← go ty rest' seen'
          match r.proof? with
          | none => return { newExpr := .forallE n r.newExpr body bi, proof? := none }
          | some h =>
            -- A non-dependent arrow `p → q` is safe: `implies_congr_left` rewrites
            -- the domain without touching `q`. A genuinely dependent `∀ x : p, q x`
            -- would need to transport `q` along the domain equality, which is a
            -- cast this tactic deliberately does not build.
            if body.hasLooseBVars then
              throwError "position {Pos.render seen'} rewrites the domain of a \
                dependent `∀`, whose body mentions the bound variable; rebuilding \
                that needs a cast of the body along the domain equality, which \
                `explicit_rw` does not build. Only definitional steps are supported \
                there."
            unless ← (isProp ty : MetaM _) do
              throwError "position {Pos.render seen'} rewrites the domain of an \
                arrow whose domain is not a `Prop`; `implies_congr_left` does not \
                apply."
            -- `q` is not determined by `h`, so name it explicitly.
            let p ← (mkAppOptM ``implies_congr_left #[none, none, body, h] : MetaM _)
            return { newExpr := .forallE n r.newExpr body bi, proof? := some p }
        | 1 =>
          withLocalDecl n bi ty fun x => do
            let r ← go (body.instantiate1 x) rest' seen'
            let newAll ← (mkForallFVars #[x] r.newExpr : MetaM _)
            match r.proof? with
            | none => return { newExpr := newAll, proof? := none }
            | some h =>
              unless ← (isProp (body.instantiate1 x) : MetaM _) do
                throwError "position {Pos.render seen'} rewrites the body of a \
                  `∀` whose body is not a `Prop`; `forall_congr` does not apply."
              let hAll ← (mkLambdaFVars #[x] h : MetaM _)
              return { newExpr := newAll, proof? := some (← (mkForallCongr hAll : MetaM _)) }
        | _ => onBadPos seen i e
      | .letE n ty val body nonDep =>
        match i with
        | 0 =>
          let r ← go ty rest' seen'
          match r.proof? with
          | none => return { newExpr := .letE n r.newExpr val body nonDep, proof? := none }
          | some _ =>
            throwError "position {Pos.render seen'} rewrites the type of a `let`; \
              only definitional steps are supported there."
        | 1 =>
          let r ← go val rest' seen'
          match r.proof? with
          | none => return { newExpr := .letE n ty r.newExpr body nonDep, proof? := none }
          | some _ =>
            throwError "position {Pos.render seen'} rewrites the value of a `let`; \
              only definitional steps are supported there."
        | 2 =>
          -- Open the `let` with a local declaration, so the bound variable is
          -- abstracted *by identity* on the way out. Abstracting by value would
          -- both destroy the `let` when the value is closed and capture
          -- unrelated occurrences of the value when it is a free variable;
          -- either one silently changes the term shape that later recorded
          -- positions are written against. The `let` is destroyed only by an
          -- explicit `zeta` step.
          withLetDecl n ty val fun x => do
            let r ← go (body.instantiate1 x) rest' seen'
            -- `usedLetOnly := false`: keep the binder even when the rewritten
            -- body no longer mentions it, so that a `let` is removed only by an
            -- explicit `zeta` step and later recorded positions stay valid.
            let newE ← (mkLetFVars (usedLetOnly := false) #[x] r.newExpr : MetaM _)
            match r.proof? with
            | none => return { newExpr := newE, proof? := none }
            | some h =>
              -- The proof mentions the `let`-bound local, which does not occur
              -- in the statement `oldLet = newLet`: both sides bind it
              -- themselves. Zeta-substituting the local out of the proof gives a
              -- proof of the same equation in the outer context, because
              -- `let x := v; b` is definitionally `b[v/x]`.
              let hClosed := (← (instantiateMVars h : MetaM _)).replaceFVar x val
              if hClosed.containsFVar x.fvarId! then
                throwError "position {Pos.render seen'} rewrites a `let` body in a \
                  way whose proof still mentions the bound variable; `explicit_rw` \
                  does not build the cast this would need."
              return { newExpr := newE, proof? := some hClosed }
        | _ => onBadPos seen i e
      | _ => onBadPos seen i e

/-- Describe an expression's head for error messages, without pretty-printing it. -/
def describeHead : Expr → String
  | .app .. => "an application (children 0 = function, 1 = argument)"
  | .lam .. => "a lambda (children 0 = binder type, 1 = body)"
  | .forallE .. => "a `∀` (children 0 = domain, 1 = body)"
  | .letE .. => "a `let` (children 0 = type, 1 = value, 2 = body)"
  | .mdata .. => "metadata (child 0)"
  | .proj .. => "a projection (child 0)"
  | .const .. => "a constant (no children)"
  | .fvar .. => "a free variable (no children)"
  | .bvar .. => "a bound variable (no children)"
  | .mvar .. => "a metavariable (no children)"
  | .sort .. => "a sort (no children)"
  | .lit .. => "a literal (no children)"

/-- The standard "no such child" failure, phrased so the trace author can fix the path. -/
def badPosError {m : Type → Type} [Monad m] [MonadError m]
    (idx : Nat) (full : Pos) (prefixPos : Pos) (child : Nat) (e : Expr) : m Replacement :=
  stepError idx m!"position {Pos.render full} does not exist: the subterm at prefix \
    {Pos.render prefixPos} is {describeHead e}, so it has no child {child}.\n\
    Subterm:{indentExpr e}"

/--
Assign every still-unassigned metavariable in `mvars` by instance synthesis, and
fail if any remains. `explicit_rw` never leaves a lemma's argument to be guessed
later: a leftover metavariable means the recorded position or lemma was wrong.
-/
def closeLemmaMVars (idx : Nat) (lemmaStx : MessageData) (mvars : Array Expr) : MetaM Unit := do
  -- First give instance arguments a chance: elaboration postpones them.
  for m in mvars do
    let m := ← instantiateMVars m
    if let .mvar mid := m then
      unless ← mid.isAssigned do
        let ty ← instantiateMVars (← mid.getType)
        if (← isClass? ty).isSome then
          match ← trySynthInstance ty with
          | .some val => mid.assign val
          | _ => pure ()
  for m in mvars do
    let m ← instantiateMVars m
    if let .mvar mid := m then
      unless ← mid.isAssigned do
        let ty ← instantiateMVars (← mid.getType)
        stepError idx m!"lemma {lemmaStx} still has an unassigned argument of type\
          {indentExpr ty}\nafter matching at the given position. Supply it as an \
          explicit argument, or fix the position. `explicit_rw` never searches for it."

/--
Split an equation-or-iff proof into `(lhs, rhs, proofOfEq)`. An `Iff` is turned
into an `Eq` with `propext`, exactly as a hand-written proof would.
-/
def asEquation (idx : Nat) (lemmaStx : MessageData) (proof type : Expr) :
    MetaM (Expr × Expr × Expr) := do
  let type ← instantiateMVars type
  if let some (_, lhs, rhs) := type.eq? then
    return (lhs, rhs, proof)
  if let some (lhs, rhs) := type.iff? then
    return (lhs, rhs, ← mkPropExt proof)
  -- `whnfR` lets through definitional wrappers such as `Ne` unfolding, matching `rw`.
  let type' ← whnfR type
  if let some (_, lhs, rhs) := type'.eq? then
    return (lhs, rhs, proof)
  if let some (lhs, rhs) := type'.iff? then
    return (lhs, rhs, ← mkPropExt proof)
  stepError idx m!"lemma {lemmaStx} does not prove an equation or an iff; its type is\
    {indentExpr type}"

end ExplicitLean.ExplicitRw
