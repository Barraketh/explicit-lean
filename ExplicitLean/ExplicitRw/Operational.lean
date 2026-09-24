module
prelude

public meta import ExplicitLean.ExplicitRw.Tactic
public meta import ExplicitLean.ExplicitRw.LocalHandles
public meta import Lean.Meta.Eqns

public meta section

/-!
# Operational rewrite steps

This is a closed, readable source form for one exact non-simproc rewrite
operation.  A global rule names its declaration; a local rule names either a
local identifier or an exact `local_ref` context index.  Each step also names
its direction, recorded pre/post phase, variant, extra-argument count, and raw
expression-child path.

The interpreter delegates equation matching, instance synthesis, side-goal
discharge, and positional congruence rebuilding to existing `ExplicitRw.Impl`
primitives. Variants are identity metadata, equation origins resolve through
Lean's exact declaration/index table, and `extra n` extends the raw path by `n`
function-child steps. It never calls `Lean.Meta.Simp`, discovers a rule, or
searches another path. Side goals use the existing closed side-proof grammar.
A `simproc` marker is recognized only to produce a direct rejection; it is
never executed or reconstructed.

The `with [...]` and `then ...` proof operations are term-free: `rfl`,
`true_intro`, `assumption h`, and `assumption local_ref n`.

Examples:

```
explicit_rw_v2 [rule Nat.add_zero variant 0 phase pre fwd extra 0 at [0, 1] with []]
explicit_rw_v2 [equation myDef index 0 variant 1 phase dpre fwd extra 0 at [0, 1] with []]
explicit_rw_v2 [local local_ref 4 variant 0 phase dpost rev extra 0 at [1] with []]
explicit_rw_v2 [beta at [0], instantiate at [1], iota at [2], proj at [3], zeta at [4]]
```
-/

namespace ExplicitLean.ExplicitRw

open Lean Elab Tactic Meta

namespace Operational

private def parsePos (stx : Syntax) : Pos :=
  Impl.parsePos stx

private def validateRuleMetadata
    (idx : Nat) (phaseStx directionStx : Syntax) :
    TacticM Bool := do
  -- The selected declaration/equation identity is authoritative. Variants
  -- distinguish recorder provenance but do not trigger simp-table lookup.
  let phaseName := phaseStx.getId.toString
  unless phaseName == "pre" || phaseName == "post" ||
      phaseName == "dpre" || phaseName == "dpost" do
    stepError idx m!"rewrite phase must be `pre`, `post`, `dpre`, or `dpost`, got `{phaseName}`."
  -- The direction parser is an alternation, so its token is one child below
  -- the anonymous choice node.
  let directionName := directionStx[0].getAtomVal
  unless directionName == "fwd" || directionName == "rev" do
    stepError idx m!"rewrite direction must be `fwd` or `rev`, got `{directionName}`."
  return directionName == "rev"

private def withExtra (pos : Pos) (extraStx : Syntax) : Pos :=
  pos ++ List.replicate (extraStx.isNatLit?.getD 0) 0

private def sideProofs (withStx : Syntax) : Array Syntax :=
  withStx[2].getSepArgs

private def lowerProof (stx : Syntax) : TacticM Syntax := do
  match stx.getKind with
  | ``explicitRwOperationalProofRfl =>
    return (← `(explicitRwSideTac| rfl)).raw
  | ``explicitRwOperationalProofTrueIntro =>
    return (← `(explicitRwSideTac| close [True.intro])).raw
  | ``explicitRwOperationalProofAssumption => do
    let hyp : Ident := ⟨stx[1]⟩
    let _ ← getFVarId hyp.raw
    return (← `(explicitRwSideTac| exact $hyp:ident)).raw
  | ``explicitRwOperationalProofAssumptionRef => do
    let localIndex : TSyntax `num := ⟨stx[2]⟩
    return (← `(explicitRwSideTac| exact local_ref $localIndex:num)).raw
  | ``explicitRwOperationalProofNested =>
    -- The nested v2 grammar is already closed. Preserve it for
    -- `Impl.runSideProofOn`, which runs it against exactly the premise goal.
    return stx
  | k => throwError "explicit_rw_v2: internal error: unknown closed proof operation `{k}`"

private def lowerProofs (withStx : Syntax) : TacticM (Array Syntax) :=
  (sideProofs withStx).mapM lowerProof

private def ruleConclusionMatchesProp (idx : Nat) (term : Term) (sub : Expr) :
    TacticM (Option Bool) := do
  -- This inspects only the named theorem's type. Opening its binders lets the
  -- exact selected proposition determine ordinary parameters; assignments
  -- made by this classification probe are discarded.
  let proof ←
    if let some name ← Impl.resolveBareConst? term then
      let info ← getConstInfo name
      let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      pure (mkConst name levels)
    else
      Impl.elabStrict (some idx) "the named proposition rule" term
        (allowMVars := true) (synthesize := false)
  let proofType ← inferType proof
  let (_, _, conclusion) ← forallMetaTelescope proofType
  withoutModifyingMCtx do
    let subType ← inferType sub
    let subIsBool ← isDefEq subType (mkConst ``Bool)
    let proposition? ←
      if subIsBool then
        some <$> mkAppM ``Eq #[sub, mkConst ``true]
      else if ← isProp sub then
        pure (some sub)
      else
        pure none
    let some proposition := proposition? | return none
    if ← isDefEq conclusion proposition then return some true
    if ← isDefEq conclusion (mkApp (mkConst ``Not) proposition) then return some false
    return none

private def runPropRule (idx : Nat) (e : Expr) (pos : Pos) (term : Term)
    (truth : Bool) (sideTacs : Array Syntax) : TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let (proof, mvars) ← Impl.elabProposition idx term sub truth
      synthesizeInstanceMVars idx m!"`{term}`" mvars sub
      let propMVars ← unassignedRewritePropMVars mvars
      if sideTacs.size > propMVars.size then
        stepError idx m!"the `with` clause supplies {sideTacs.size} proof(s) but proposition rule \
          `{term}` has {propMVars.size} undetermined hypothesis(es) at this position."
      for h : i in [0 : sideTacs.size] do
        let .mvar mid := ← instantiateMVars propMVars[i]! | pure ()
        Impl.runSideProofOn idx (some i) sideTacs[i] mid
      closeLemmaMVars idx m!"`{term}`" mvars
      let proof ← instantiateMVars proof
      let subType ← inferType sub
      let subIsBool ← isDefEq subType (mkConst ``Bool)
      let (replacement, equality) ←
        if subIsBool then
          if truth then
            pure (mkConst ``true, proof)
          else
            pure (mkConst ``false, ← mkAppM ``Bool.of_not_eq_true #[proof])
        else
          let equality ←
            if truth then mkAppM ``eq_true #[proof] else mkAppM ``eq_false #[proof]
          pure (if truth then mkConst ``True else mkConst ``False, equality)
      Impl.checkNoLevelMVars idx m!"`{term}`" #[equality]
      return Replacement.eq replacement equality)
    (fun pfx child sub => badPosError idx pos pfx child sub)

private def runNamedRule (idx : Nat) (e : Expr) (pos : Pos) (term : Term)
    (reverse : Bool) (sideTacs : Array Syntax) : TacticM Replacement := do
  let isPropRef ← IO.mkRef (none : Option Bool)
  let _ ← rewriteAt e pos
    (fun sub => do
      isPropRef.set (← ruleConclusionMatchesProp idx term sub)
      return Replacement.defeq sub)
    (fun pfx child sub => badPosError idx pos pfx child sub)
  if let some truth := ← isPropRef.get then
    if reverse then
      stepError idx m!"a proposition-valued rule is only supported in the forward direction."
    runPropRule idx e pos term truth sideTacs
  else
    Impl.runRwStep idx e pos term reverse sideTacs

mutual

private partial def runOne (idx : Nat) (e : Expr) (step : Syntax) : TacticM Replacement := do
  match step.getKind with
  | ``explicitRwOperationalRule => do
    let reverse ← validateRuleMetadata idx step[5] step[6]
    let sideTacs ← lowerProofs step[10]
    let decl : Ident := ⟨step[1]⟩
    -- Resolve as a global constant up front.  In particular, `rule h` cannot
    -- silently switch to a local variable when a declaration is missing.
    let _ ← realizeGlobalConstNoOverloadWithInfo decl
    let termStx ← `(explicitRwTerm| $decl:ident)
    let term ← Impl.toTerm termStx.raw
    runNamedRule idx e (withExtra (parsePos step[9]) step[8]) term reverse sideTacs
  | ``explicitRwOperationalSource => do
    let reverse ← validateRuleMetadata idx step[5] step[6]
    let sideTacs ← lowerProofs step[10]
    let term ← Impl.toTerm step[1]
    runNamedRule idx e (withExtra (parsePos step[9]) step[8]) term reverse sideTacs
  | ``explicitRwOperationalEquation => do
    let reverse ← validateRuleMetadata idx step[7] step[8]
    let sideTacs ← lowerProofs step[12]
    let decl : Ident := ⟨step[1]⟩
    let declaration ← realizeGlobalConstNoOverloadWithInfo decl
    let some equations ← getEqnsFor? declaration
      | stepError idx m!"declaration `{declaration}` has no equation theorems."
    let equationIndex := step[3].isNatLit?.getD 0
    let some theoremName := equations[equationIndex]?
      | stepError idx m!"equation index {equationIndex} is out of range for `{declaration}`."
    let theoremIdent : Ident := ⟨mkIdent theoremName⟩
    let termStx ← `(explicitRwTerm| $theoremIdent:ident)
    let term ← Impl.toTerm termStx.raw
    runNamedRule idx e
      (withExtra (parsePos step[11]) step[10]) term reverse sideTacs
  | ``explicitRwOperationalLocal => do
    let reverse ← validateRuleMetadata idx step[5] step[6]
    let sideTacs ← lowerProofs step[10]
    let hyp : Ident := ⟨step[1]⟩
    -- `getFVarId` elaborates precisely the identifier and rejects a global
    -- theorem here.  The resulting source term still carries the readable
    -- local identity; no type- or target-based context search is performed.
    let _ ← getFVarId hyp.raw
    let termStx ← `(explicitRwTerm| $hyp:ident)
    let term ← Impl.toTerm termStx.raw
    runNamedRule idx e (withExtra (parsePos step[9]) step[8]) term reverse sideTacs
  | ``explicitRwOperationalLocalRef => do
    let reverse ← validateRuleMetadata idx step[6] step[7]
    let sideTacs ← lowerProofs step[11]
    let localIndex : TSyntax `num := ⟨step[2]⟩
    let termStx ← `(explicitRwTerm| local_ref $localIndex:num)
    let term ← Impl.toTerm termStx.raw
    runNamedRule idx e (withExtra (parsePos step[10]) step[9]) term reverse sideTacs
  | ``explicitRwOperationalBeta => do
    let pos := parsePos step[1]
    Impl.runDefeqStep idx e pos m!"`beta`" fun sub => do
      let reduced := sub.headBeta
      if reduced == sub then
        stepError idx m!"`beta` at this position: the subterm is not a beta-redex."
      return reduced
  | ``explicitRwOperationalInstantiate => do
    let pos := parsePos step[1]
    -- `instantiateMVars` is itself a recorded simplifier operation. Replaying
    -- it at the exact recorded node preserves that operational boundary; it
    -- does not search for a redex or choose a theorem.
    Impl.runDefeqStep idx e pos m!"`instantiate`" instantiateMVars
  | ``explicitRwOperationalIota => do
    let pos : TSyntax ``ExplicitLean.ExplicitRw.explicitRwPos := ⟨step[1]⟩
    let legacyStep ← `(explicitRwStep| iota $pos)
    Impl.runStep idx e legacyStep.raw
  | ``explicitRwOperationalProj => do
    let pos : TSyntax ``ExplicitLean.ExplicitRw.explicitRwPos := ⟨step[1]⟩
    let legacyStep ← `(explicitRwStep| proj $pos)
    Impl.runStep idx e legacyStep.raw
  | ``explicitRwOperationalZeta => do
    let pos : TSyntax ``ExplicitLean.ExplicitRw.explicitRwPos := ⟨step[1]⟩
    let legacyStep ← `(explicitRwStep| zeta $pos)
    Impl.runStep idx e legacyStep.raw
  | ``explicitRwOperationalUnfold => do
    let c ← realizeGlobalConstNoOverloadWithInfo step[1]
    let pos := parsePos step[2]
    Impl.runDefeqStep idx e pos m!"`unfold {c}`" (Impl.unfoldConst idx c)
  | ``explicitRwOperationalCached => do
    let steps := step[2].getSepArgs
    if steps.isEmpty then
      stepError idx m!"a changed simp cache result must name its producing operations."
    let pos := parsePos step[4]
    rewriteAt e pos
      (fun sub => runOperationsAt steps sub)
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwOperationalSimproc =>
    throwError "explicit_rw_v2: simproc `{step[1].getId}` is not a rewrite-rule operation."
  | k =>
    throwError "explicit_rw_v2: internal error: unexpected operation kind `{k}`"

private partial def runOperationsAt (steps : Array Syntax) (e : Expr) : TacticM Replacement := do
  let mut current := e
  let mut proof? : Option Expr := none
  for h : idx in [0 : steps.size] do
    let step := steps[idx]
    let replacement ←
      try
        runOne idx current step
      catch ex => do
        let msg ← ex.toMessageData.toString
        if msg.startsWith "explicit_rw_v2:" then
          throw ex
        else if msg.startsWith "explicit_rw:" then
          throwError "explicit_rw_v2:{msg.drop 12}"
        else
          throwError "explicit_rw_v2: step {idx + 1}: {msg}"
    let newE ← instantiateMVars replacement.newExpr
    match proof?, replacement.proof? with
    | none, p => proof? := p
    | some p, none => pure ()
    | some p, some q => proof? := some (← mkEqTrans p (← instantiateMVars q))
    current := newE
  return { newExpr := current, proof? := proof? }

end

private structure Target where
  fvarId : FVarId

private def runOperations (steps : Array Syntax) (target : Option Target)
    (closeLocalFalse : Bool) :
    TacticM (Option Target) := do
  let goal ← getMainGoal
  goal.withContext do
    let initial ← match target with
      | none => instantiateMVars (← goal.getType)
      | some target => instantiateMVars (← target.fvarId.getType)
    let replacement ← runOperationsAt steps initial
    let newExpr ← instantiateMVars replacement.newExpr
    if closeLocalFalse then
      let some target := target
        | throwError "explicit_rw_v2: `false_elim` requires a hypothesis location."
      unless newExpr.isFalse do
        throwError "explicit_rw_v2: `false_elim` expected the selected hypothesis to simplify to False."
      let falseProof ← match replacement.proof? with
        | none => pure (mkFVar target.fvarId)
        | some proof => mkEqMP (← instantiateMVars proof) (mkFVar target.fvarId)
      goal.assign (← mkFalseElim (← goal.getType) falseProof)
      replaceMainGoal []
      return none
    match target, replacement.proof? with
    | none, none =>
      replaceMainGoal [← goal.replaceTargetDefEq newExpr]
      return none
    | none, some proof =>
      replaceMainGoal [← goal.replaceTargetEq newExpr (← instantiateMVars proof)]
      return none
    | some target, none =>
      replaceMainGoal [← goal.replaceLocalDeclDefEq target.fvarId newExpr]
      return some target
    | some target, some proof =>
      let proof ← instantiateMVars proof
      let newProof ← mkEqMP proof (mkFVar target.fvarId)
      let result ← goal.replace target.fvarId newProof newExpr
      replaceMainGoal [result.mvarId]
      return some { target with fvarId := result.fvarId }

private def resolveTarget (locStx : Syntax) : TacticM (Option Target) := do
  if locStx.isNone then return none
  let loc := locStx[0]
  match loc.getKind with
  | ``explicitRwOperationalLocationIdent => do
    let fvarId ← getFVarId loc[1]
    return some { fvarId }
  | ``explicitRwOperationalLocationRef =>
    let index ← Impl.checkedHandle loc[2] "location local_ref index"
    return some { fvarId := (← Impl.indexedLocalDecl index).fvarId }
  | kind =>
    throwError "explicit_rw_v2: internal error: unknown location `{kind}`."

private def runTerminal (stx : Syntax) (target : Option Target) : TacticM Unit := do
  let close := stx[0]
  match close.getKind with
  | ``explicitRwOperationalClose =>
    if target.isSome then
      throwError "explicit_rw_v2: this terminal operation applies only to the goal, not a hypothesis."
    let closer ← lowerProof close[1]
    Impl.runCloser closer
  | kind =>
    throwError "explicit_rw_v2: internal error: unknown terminal operation `{kind}`."

private def isFalseElimTerminal (stx : Syntax) : Bool :=
  !stx.isNone && stx[0].getKind == ``explicitRwOperationalCloseFalseElim

end Operational

@[tactic explicitRwOperational]
public meta def evalExplicitRwOperational : Tactic := fun stx => do
  let steps := stx[2].getSepArgs
  let target ← Operational.resolveTarget stx[4]
  let closeLocalFalse := Operational.isFalseElimTerminal stx[5]
  let target ← Operational.runOperations steps target closeLocalFalse
  unless stx[5].isNone do
    unless closeLocalFalse do
      Operational.runTerminal stx[5] target

end ExplicitLean.ExplicitRw
