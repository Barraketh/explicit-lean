module
prelude

public meta import ExplicitLean.ExplicitRw.Basic
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.Intro
public meta import Lean.Parser.Tactic

public meta section

/-!
# The `explicit_rw` tactic

`explicit_rw` replays a recorded simp trace positionally, with no search.

```
explicit_rw [foo at [1, 1], ← bar at [], baz a b at [0, 1, 1],
             unfold f at [1], beta at [1, 1], eq (2 + 3 = 5) by rfl at [1]] at h
```

Each step names a position (a `SubExpr.Pos` child-index list, see
`tracking/SIMP-TRACE-SPEC.md`), navigates to exactly that subterm, and replaces
it. Steps apply in order; each position is relative to the result of the
previous step. There is no fallback, no search and no retry at other positions:
every failure names the step index and the reason.

## Step forms

| Form                              | Meaning                                         |
| --------------------------------- | ----------------------------------------------- |
| `e at [..]`                       | rewrite left-to-right with the equation/iff `e`  |
| `← e at [..]`                     | rewrite right-to-left                            |
| `unfold c at [..]`                | delta-unfold the constant `c` (definitional)     |
| `beta at [..]`                    | beta-reduce the subterm (definitional)           |
| `eta at [..]`                     | eta-reduce the subterm (definitional)            |
| `proj at [..]`                    | reduce a structure projection (definitional)     |
| `change t at [..]`                | replace by the defeq term `t` (definitional)     |
| `eq (lhs = rhs) by tac at [..]`   | prove the equation with `tac`, then rewrite      |

`e` is an ordinary term, so explicit arguments (`baz a b`), local hypotheses and
side-condition proofs are written as usual and elaborated as usual: implicits,
universes and instances are recovered by elaboration and unification.

Positions are raw child indices, *not* `conv`'s `arg n` numbering: `conv`'s
`arg` counts explicit arguments, while `0`/`1` here are the `fn`/`arg` children
of `Expr.app`, so `f a b` has `b` at `[1]` and `a` at `[0, 1]`.

## Closing form

`explicit_rw [...] then rfl` runs `rfl` on the remaining goal after the last
step; `then exact e` and `then tac` work likewise for any tactic sequence. This
is exactly sugar for writing the tactic on the next line, kept so a rendered
trace is a single tactic. Omit it to leave the goal open.

## No simp

Nothing in this tactic calls, imports for use, or expands to `Lean.Meta.Simp` or
any simp-family tactic. `Experiment/check_no_simp_family.py` enforces that.
-/

namespace ExplicitLean.ExplicitRw

open Lean Elab Tactic Meta

/-- `at [0, 1, 1]` — the position a step applies at. `at []` is the whole location. -/
syntax explicitRwPos := " at " "[" num,* "]"

/-- A lemma rewrite, forwards or backwards: `foo a b at [1]`, `← bar at []`. -/
syntax explicitRwRw := ("← ")? term explicitRwPos

/-- `unfold f at [1]` — delta-unfold one constant, definitionally. -/
syntax explicitRwUnfold := "unfold " ident explicitRwPos

/-- `beta at [1]`, `eta at [1]`, `proj at [1]` — silent definitional reductions. -/
syntax explicitRwRed := ("beta" <|> "eta" <|> "proj") explicitRwPos

/-- `change t at [1]` — last-resort definitional replacement, checked by defeq. -/
syntax explicitRwChange := "change " term explicitRwPos

/-- `eq (2 + 3 = 5) by rfl at [1]` — an equation proved by an ordinary tactic. -/
syntax explicitRwEq := "eq " term " by " Lean.Parser.Tactic.tacticSeq explicitRwPos

/-- One step of an `explicit_rw` trace. -/
syntax explicitRwStep :=
  explicitRwUnfold <|> explicitRwRed <|> explicitRwChange <|> explicitRwEq <|> explicitRwRw

/-- Optional closing tactic: `explicit_rw [...] then rfl`. -/
syntax explicitRwClose := " then " Lean.Parser.Tactic.tacticSeq

/--
Replay a recorded simp trace positionally, with no search.

Each step names a `SubExpr.Pos` child-index path and the rewrite to perform
there. See the module documentation for the step forms.
-/
syntax (name := explicitRw) "explicit_rw " "[" explicitRwStep,* "]"
  (Lean.Parser.Tactic.location)? (explicitRwClose)? : tactic

namespace Impl

/-- Parse the child-index list out of an `explicitRwPos` node. -/
def parsePos (stx : Syntax) : Pos :=
  stx[2].getSepArgs.toList.map fun s => (s.isNatLit?.getD 0)

/-- Which location a step sequence applies to: the goal, or one hypothesis. -/
abbrev Target := Option FVarId

/--
Elaborate a term to a proof of an equation or iff, returning `lhs`, `rhs` and a
proof of `lhs = rhs`, together with the metavariables introduced for the
lemma's own arguments so the caller can insist they all get assigned.
-/
def elabEquation (idx : Nat) (stx : Term) : TacticM (Expr × Expr × Expr × Array Expr) := do
  let lemmaMsg := m!"`{stx}`"
  let proof ← Term.withSynthesize (postpone := .no) do
    Term.elabTerm stx none
  let proof ← instantiateMVars proof
  let type ← instantiateMVars (← inferType proof)
  -- Open the lemma's own leading binders as metavariables, so that matching the
  -- position determines them by unification rather than by search.
  let (mvars, _, type') ← forallMetaTelescopeReducing type
  let proof' := mkAppN proof mvars
  let (lhs, rhs, eqProof) ← asEquation idx lemmaMsg proof' type'
  -- Metavariables can also enter through elaboration of the written term itself
  -- (an implicit argument the syntax leaves open), not only through the
  -- telescope above. Collect both so none can escape into the goal.
  let fromTerm := (← instantiateMVars proof).collectMVars {} |>.result
  let fromType := (← instantiateMVars type).collectMVars {} |>.result
  let extra := (fromTerm ++ fromType).map Expr.mvar
  return (lhs, rhs, eqProof, mvars ++ extra)

/-- Run a rewrite step at `pos` inside `e`. -/
def runRwStep (idx : Nat) (e : Expr) (pos : Pos) (stx : Term) (symm : Bool) :
    TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let (lhs, rhs, eqProof, mvars) ← elabEquation idx stx
      let (source, target) := if symm then (rhs, lhs) else (lhs, rhs)
      unless ← isDefEq source sub do
        stepError idx m!"lemma `{stx}` does not match the subterm at \
          position {Pos.render pos}.\nExpected{indentExpr (← instantiateMVars source)}\n\
          but the subterm is{indentExpr sub}"
      closeLemmaMVars idx m!"`{stx}`" mvars
      let eqProof ← instantiateMVars eqProof
      let target ← instantiateMVars target
      let h ← if symm then mkEqSymm eqProof else pure eqProof
      return Replacement.eq target h)
    (fun pfx child sub => badPosError idx pos pfx child sub)

/-- Run a definitional step at `pos` inside `e`, using `reduce` on the subterm. -/
def runDefeqStep (idx : Nat) (e : Expr) (pos : Pos) (what : String)
    (reduce : Expr → TacticM Expr) : TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let newSub ← reduce sub
      unless ← isDefEq sub newSub do
        stepError idx m!"{what} at position {Pos.render pos} produced a term that is \
          not definitionally equal to the original.\nBefore{indentExpr sub}\n\
          After{indentExpr newSub}"
      return Replacement.defeq newSub)
    (fun pfx child sub => badPosError idx pos pfx child sub)

/-- Delta-unfold exactly the constant `c` at the head of `sub`. -/
def unfoldConst (idx : Nat) (c : Name) (sub : Expr) : TacticM Expr := do
  unless (← getEnv).contains c do
    stepError idx m!"`unfold {c}` names a constant that does not exist."
  match ← withReducible (unfoldDefinition? sub) with
  | some e =>
    unless sub.getAppFn.constName? == some c do
      stepError idx m!"`unfold {c}` was applied where the head constant is \
        `{sub.getAppFn}`."
    return e
  | none =>
    -- `unfoldDefinition?` fails for non-recursive plain definitions under
    -- `withReducible`; retry at default transparency, still delta only.
    match ← unfoldDefinition? sub with
    | some e =>
      unless sub.getAppFn.constName? == some c do
        stepError idx m!"`unfold {c}` was applied where the head constant is \
          `{sub.getAppFn}`."
      return e
    | none =>
      stepError idx m!"`unfold {c}` cannot unfold the subterm at this position; \
        its head is `{sub.getAppFn}` and it has no delta-reduction."

/-- Eta-reduce `fun x => f x` to `f`, failing when the subterm is not an eta-redex. -/
def etaReduce (idx : Nat) (sub : Expr) : TacticM Expr := do
  let r := sub.eta
  if r == sub then
    stepError idx m!"`eta` at this position: the subterm is not an eta-redex."
  return r

/-- Reduce a structure projection applied to a constructor application. -/
def projReduce (idx : Nat) (sub : Expr) : TacticM Expr := do
  match ← withReducible (whnfCore sub) with
  | r =>
    if r == sub then
      stepError idx m!"`proj` at this position: the subterm does not reduce."
    return r

/-- Apply one parsed step to the current expression. -/
def runStep (idx : Nat) (e : Expr) (stx : TSyntax ``explicitRwStep) : TacticM Replacement := do
  let stx := stx.raw[0]
  match stx.getKind with
  | ``explicitRwUnfold =>
    let pos := parsePos stx[2]
    let c ← realizeGlobalConstNoOverloadWithInfo stx[1]
    runDefeqStep idx e pos s!"`unfold {c}`" (unfoldConst idx c)
  | ``explicitRwRed =>
    let pos := parsePos stx[1]
    let kind := stx[0].getAtomVal
    match kind with
    | "beta" => runDefeqStep idx e pos "`beta`" fun sub => do
        let r := sub.headBeta
        if r == sub then
          stepError idx m!"`beta` at this position: the subterm is not a beta-redex."
        return r
    | "eta" => runDefeqStep idx e pos "`eta`" (etaReduce idx)
    | _ => runDefeqStep idx e pos "`proj`" (projReduce idx)
  | ``explicitRwChange =>
    let pos := parsePos stx[2]
    let target : Term := ⟨stx[1]⟩
    runDefeqStep idx e pos s!"`change {target}`" fun sub => do
      let ty ← inferType sub
      let newSub ← Term.withSynthesize (postpone := .no) do
        Term.elabTermEnsuringType target ty
      instantiateMVars newSub
  | ``explicitRwEq =>
    let pos := parsePos stx[4]
    let eqStx : Term := ⟨stx[1]⟩
    let byStx : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨stx[3]⟩
    -- Prove the stated equation with the named ordinary tactic, then rewrite.
    rewriteAt e pos
      (fun sub => do
        let eqType ← Term.withSynthesize (postpone := .no) do
          Term.elabType eqStx
        let eqType ← instantiateMVars eqType
        let some (_, lhs, rhs) := eqType.eq?
          | stepError idx m!"`eq {eqStx}` must state an equation `lhs = rhs`; it states\
              {indentExpr eqType}"
        unless ← isDefEq lhs sub do
          stepError idx m!"`eq {eqStx}`: its left-hand side does not match the subterm \
            at position {Pos.render pos}.\nExpected{indentExpr lhs}\n\
            but the subterm is{indentExpr sub}"
        let goal ← mkFreshExprSyntheticOpaqueMVar eqType
        let remaining ← Tactic.run goal.mvarId! (evalTactic byStx)
        unless remaining.isEmpty do
          stepError idx m!"`eq {eqStx} by ...`: the closing tactic left \
            {remaining.length} goal(s) open."
        let h ← instantiateMVars goal
        return Replacement.eq (← instantiateMVars rhs) h)
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwRw =>
    let symm := !stx[0].isNone
    let term : Term := ⟨stx[1]⟩
    let pos := parsePos stx[2]
    runRwStep idx e pos term symm
  | k => throwError "explicit_rw: internal error: unexpected step kind `{k}`"

/-- Apply every step in order to the expression at `target`, rebuilding the goal. -/
def runSteps (steps : Array (TSyntax ``explicitRwStep)) (target : Target) : TacticM Unit := do
  for h : idx in [0 : steps.size] do
    let stx := steps[idx]
    let goal ← getMainGoal
    goal.withContext do
      let e ← match target with
        | none => instantiateMVars (← goal.getType)
        | some fvarId => instantiateMVars (← fvarId.getType)
      let r ← runStep idx e stx
      let newE ← instantiateMVars r.newExpr
      match target with
      | none =>
        match r.proof? with
        | none => replaceMainGoal [← goal.replaceTargetDefEq newE]
        | some h => replaceMainGoal [← goal.replaceTargetEq newE (← instantiateMVars h)]
      | some fvarId =>
        match r.proof? with
        | none =>
          let res ← goal.replaceLocalDeclDefEq fvarId newE
          replaceMainGoal [res]
        | some h =>
          -- `Eq.mp h hyp : newType` transports the hypothesis forwards.
          let h ← instantiateMVars h
          let newProof ← mkEqMP h (mkFVar fvarId)
          let res ← goal.replace fvarId newProof newE
          replaceMainGoal [res.mvarId]

end Impl

open Impl in
@[tactic explicitRw]
def evalExplicitRw : Tactic := fun stx => do
  let steps := stx[2].getSepArgs.map fun s => (⟨s⟩ : TSyntax ``explicitRwStep)
  let locStx := stx[4]
  let closeStx := stx[5]
  -- Resolve the location: the goal, or exactly one hypothesis.
  let target ← do
    if locStx.isNone then
      pure (none : Target)
    else
      match expandLocation locStx[0] with
      | .targets hyps goalToo =>
        if goalToo || hyps.size != 1 then
          throwError "explicit_rw: a trace applies to exactly one location: either the \
            goal, or `at h` for a single hypothesis."
        let fvarId ← getFVarId hyps[0]!
        pure (some fvarId : Target)
      | .wildcard =>
        throwError "explicit_rw: `at *` is not supported: positions are relative to one \
          location. Write one `explicit_rw` per location."
  runSteps steps target
  unless closeStx.isNone do
    match target with
    | none => evalTactic closeStx[0][1]
    | some _ =>
      throwError "explicit_rw: the `then` closing form applies to the goal, but this \
        trace rewrites a hypothesis. Write the closing tactic on the next line."

end ExplicitLean.ExplicitRw
