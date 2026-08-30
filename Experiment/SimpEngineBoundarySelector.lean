import ExplicitLean.SimpEngine.Boundary.Selector
import Lean.Elab.Tactic.Basic

open Lean Meta Elab Tactic

namespace ExplicitLean.SimpEngine.Boundary.SelectorProbe

private def assertChanged (before after : BoundaryStateFingerprint) (label : String) :
    TacticM Unit := do
  unless before != after do
    throwError s!"boundary selector failed to observe {label}"

elab "check_boundary_selector_state" : tactic => withMainContext do
  let core ← getThe Core.State
  let metaState ← getThe Meta.State
  let term ← getThe Lean.Elab.Term.State
  let mctx ← getMCtx
  try
    let goals ← getGoals
    let stable ← boundaryProofStateFingerprint goals
    let stableAgain ← boundaryProofStateFingerprint goals
    unless stable == stableAgain do
      throwError "boundary selector changed for an unchanged state"
    unless (stable.metavariableContextFingerprint.splitOn "selector-state-v1").length == 1 do
      throwError "boundary selector exposed its unhashed routing-state payload"

    let fresh ← mkFreshExprMVar (some (mkConst ``Nat))
    let freshId := fresh.mvarId!
    let assignmentGoals := freshId :: goals
    let beforeAssignment ← boundaryProofStateFingerprint assignmentGoals
    freshId.assign (mkNatLit 0)
    let afterAssignment ← boundaryProofStateFingerprint assignmentGoals
    assertChanged beforeAssignment afterAssignment "an expression assignment"
    unless afterAssignment == stable do
      throwError "boundary selector retained a stale assigned tactic goal"

    let freshLevel ← mkFreshLevelMVar
    let freshLevelId := freshLevel.mvarId!
    let levelCarrier ← mkFreshExprMVar (some (mkSort freshLevel))
    let levelGoals := levelCarrier.mvarId! :: goals
    let beforeLevelAssignment ← boundaryProofStateFingerprint levelGoals
    assignLevelMVar freshLevelId .zero
    let afterLevelAssignment ← boundaryProofStateFingerprint levelGoals
    assertChanged beforeLevelAssignment afterLevelAssignment "a universe assignment"

    let synthetic ← mkFreshExprMVar (some (mkConst ``Nat))
      (kind := MetavarKind.syntheticOpaque)
    let syntheticId := synthetic.mvarId!
    let syntheticDecl : Lean.Elab.Term.SyntheticMVarDecl := {
      stx := Syntax.missing
      kind := .postponed {
        declName? := none
        options := {}
        openDecls := []
        macroStack := []
        errToSorry := false
        levelNames := []
        fixedTermElabs := #[]
      }
    }
    let termWithPending := {
      term with
      syntheticMVars := term.syntheticMVars.insert syntheticId syntheticDecl
      pendingMVars := syntheticId :: term.pendingMVars
    }
    let beforePending ← boundaryProofStateFingerprintWithTerm goals term
    let afterPending ← boundaryProofStateFingerprintWithTerm goals termWithPending
    assertChanged beforePending afterPending "a pending synthetic metavariable"

    let activeContext : Lean.Elab.Term.SavedContext := {
      declName? := none
      options := {}
      openDecls := []
      macroStack := []
      errToSorry := false
      levelNames := []
      fixedTermElabs := #[]
    }
    let pendingTacticDecl (payload : Syntax) :
        Lean.Elab.Term.SyntheticMVarDecl := {
      stx := Syntax.missing
      kind := .tactic payload activeContext .term false
    }
    let pendingTacticA := {
      termWithPending with
      syntheticMVars := termWithPending.syntheticMVars.insert syntheticId
        (pendingTacticDecl (.atom .none "A"))
    }
    let pendingTacticB := {
      termWithPending with
      syntheticMVars := termWithPending.syntheticMVars.insert syntheticId
        (pendingTacticDecl (.atom .none "B"))
    }
    let tacticA ← boundaryProofStateFingerprintWithTerm goals pendingTacticA
    let tacticB ← boundaryProofStateFingerprintWithTerm goals pendingTacticB
    assertChanged tacticA tacticB "a pending tactic syntax payload"

    let nestedPayload (rawValue : String) (namespaceName : Name) : Syntax :=
      .node .none `selectorTest #[
        .node .none `nested #[
          .ident .none rawValue.toRawSubstring' `payload
            [.namespace namespaceName]]]
    let nestedA := {
      termWithPending with
      syntheticMVars := termWithPending.syntheticMVars.insert syntheticId
        (pendingTacticDecl (nestedPayload "alpha" `First))
    }
    let nestedIdentChanged := {
      termWithPending with
      syntheticMVars := termWithPending.syntheticMVars.insert syntheticId
        (pendingTacticDecl (nestedPayload "beta" `First))
    }
    let nestedPreresolvedChanged := {
      termWithPending with
      syntheticMVars := termWithPending.syntheticMVars.insert syntheticId
        (pendingTacticDecl (nestedPayload "alpha" `Second))
    }
    let nestedAFingerprint ← boundaryProofStateFingerprintWithTerm goals nestedA
    let nestedIdentFingerprint ←
      boundaryProofStateFingerprintWithTerm goals nestedIdentChanged
    let nestedPreresolvedFingerprint ←
      boundaryProofStateFingerprintWithTerm goals nestedPreresolvedChanged
    assertChanged nestedAFingerprint nestedIdentFingerprint
      "a nested pending tactic identifier payload"
    assertChanged nestedAFingerprint nestedPreresolvedFingerprint
      "a nested pending tactic preresolved payload"

    let delayed ← mkFreshExprMVar (some (mkConst ``Nat))
    let delayedId := delayed.mvarId!
    let delayedPending ← mkFreshExprMVar (some (mkConst ``Nat))
      (kind := MetavarKind.syntheticOpaque)
    assignDelayedMVar delayedId #[] delayedPending.mvarId!
    let delayedTarget ← mkEq delayed (mkNatLit 0)
    let delayedCarrier ← mkFreshExprMVar (some delayedTarget)
    let delayedGoals := delayedCarrier.mvarId! :: goals
    let beforeDelayedMetadata ← boundaryProofStateFingerprint delayedGoals
    let delayedDecl ← delayedId.getDecl
    modifyMCtx fun mctx => { mctx with
      decls := mctx.decls.insert delayedId
        { delayedDecl with depth := delayedDecl.depth + 1 } }
    let afterDelayedMetadata ← boundaryProofStateFingerprint delayedGoals
    assertChanged beforeDelayedMetadata afterDelayedMetadata
      "reachable delayed-root declaration metadata"

    let activeGoal ← getMainGoal
    let activeDecl (context : Lean.Elab.Term.SavedContext) :
        Lean.Elab.Term.SyntheticMVarDecl := {
      stx := Syntax.missing
      kind := .tactic Syntax.missing context .term false
    }
    let activeTerm := {
      term with
      syntheticMVars := term.syntheticMVars.insert activeGoal (activeDecl activeContext)
    }
    let changedActiveTerm := {
      activeTerm with
      syntheticMVars := activeTerm.syntheticMVars.insert activeGoal
        (activeDecl { activeContext with errToSorry := true })
    }
    let beforeActiveWrapper ← boundaryProofStateFingerprintWithTerm goals activeTerm
    let afterActiveWrapper ← boundaryProofStateFingerprintWithTerm goals changedActiveTerm
    unless beforeActiveWrapper == afterActiveWrapper do
      throwError "boundary selector observed already-running tactic wrapper metadata"

    let postponed : Lean.Meta.PostponedEntry := {
      ref := Syntax.missing
      lhs := .zero
      rhs := .zero
      ctx? := none
    }
    let beforePostponed ← boundaryProofStateFingerprintWithTerm goals term
    modifyThe Meta.State fun state => { state with postponed := state.postponed.push postponed }
    let afterPostponed ← boundaryProofStateFingerprintWithTerm goals term
    unless beforePostponed == afterPostponed do
      throwError "boundary selector observed continuation-only postponed work"
  finally
    modifyThe Core.State fun _ => core
    modifyThe Meta.State fun _ => metaState
    modifyThe Lean.Elab.Term.State fun _ => term
    modifyMCtx fun _ => mctx

end ExplicitLean.SimpEngine.Boundary.SelectorProbe

theorem selectorStateHardeningProbe (P : Prop) (h : P) : P := by
  check_boundary_selector_state
  exact h

#eval IO.println "SIMP_ENGINE_BOUNDARY_SELECTOR ok"
