module

public meta import ExplicitLean.SimpEngine

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

syntax simpEngineRecordingArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?

syntax (name := simpEngineRecording)
  "simp_engine_recording" simpEngineRecordingArgs : tactic

syntax (name := simpEngineObserve)
  "simp_engine_observe" simpEngineRecordingArgs : tactic

syntax dsimpEngineRecordingArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? (location)?

syntax (name := dsimpEngineObserve)
  "dsimp_engine_observe" dsimpEngineRecordingArgs : tactic

end Lean.Parser.Tactic

namespace ExplicitLean.SimpEngine.Recording

private def assertRecordedEquivalent (reference recorded : Simp.Result)
    (referenceState recordedState : Simp.State) : MetaM Unit := do
  unless Expr.equal reference.expr recorded.expr do
    throwError "record_mode_mismatch: expression"
  unless reference.proof?.isSome == recorded.proof?.isSome do
    throwError "record_mode_mismatch: proof presence"
  unless reference.cache == recorded.cache do
    throwError "record_mode_mismatch: result cache flag"
  unless referenceState.numSteps == recordedState.numSteps &&
      referenceState.cache.toList.length == recordedState.cache.toList.length &&
      referenceState.congrCache.size == recordedState.congrCache.size &&
      referenceState.dsimpCache.size == recordedState.dsimpCache.size do
    throwError "record_mode_mismatch: simplifier state"

private def logRecording (recording : Simp.Engine.Recording) : TacticM Unit := do
  let branches := String.intercalate "," recording.coveredBranches.toList
  logInfo m!"SIMP_ENGINE_RECORDING branches={branches} events={recording.program.events.size} structural={recording.program.structural.size} simprocs={recording.simprocs.size} deferred={repr recording.deferred}"

def proofPresence (result : Simp.Result) : Simp.Engine.ProofPresence :=
  if result.proof?.isSome then .explicit else .definitional

def localRef (localDecl : LocalDecl) : MetaM Simp.Engine.LocalRef := do
  return {
    contextIndex := localDecl.index
    binderDepth := (← getLCtx).numIndices
    typeFingerprint := ← Simp.Engine.exprFingerprintHash localDecl.type
    valueFingerprint := ← localDecl.value?.mapM Simp.Engine.exprFingerprintHash
  }

def recordExpression (expression : Expr) (ctx : Simp.Context)
    (methods : Simp.Engine.Methods) (stats : Simp.Stats) :
    MetaM (Simp.Result × Simp.Stats × Simp.Engine.Recording) := do
  let initialMeta ← Meta.saveState
  let (reference, referenceState) ←
    Simp.Engine.mainCore expression ctx { stats with } (methods := methods)
  let referenceMeta ← Meta.saveState
  initialMeta.restore
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression ctx { stats with } (methods := methods)
  assertRecordedEquivalent reference recorded referenceState recordedState
  referenceMeta.restore
  return (reference, { referenceState with }, recording)

structure RecordedGoal where
  result? : Option (Array FVarId × MVarId)
  subjects : Array Simp.Engine.SubjectProgram
  branches : Array String
  deriving Inhabited

/-- The goal/hypothesis transport layer of `Meta.simpGoal`, with each engine
    execution replaced by a schema-16 recording execution. -/
def recordGoal (mvarId : MVarId) (ctx : Simp.Context)
    (methods : Simp.Engine.Methods) (simplifyTarget : Bool)
    (fvarIdsToSimp : Array FVarId) : MetaM RecordedGoal := mvarId.withContext do
  mvarId.checkNotAssigned `simp_engine_recording
  let mut mvarIdNew := mvarId
  let mut toAssert := #[]
  let mut replaced := #[]
  let mut stats : Simp.Stats := {}
  let mut subjects := #[]
  let mut branches := #[]
  for fvarId in fvarIdsToSimp do
    let localDecl ← fvarId.getDecl
    let subjectRef ← localRef localDecl
    let type ← instantiateMVars localDecl.type
    let subjectCtx := ctx.setSimpTheorems <|
      ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId)
    let (result, statsNew, recording) ← recordExpression type subjectCtx methods stats
    stats := statsNew
    branches := branches ++ recording.coveredBranches
    let terminal :=
      if result.expr.isFalse then
        Simp.Engine.SubjectTerminal.localFalse (proofPresence result)
      else if result.proof?.isNone then
        .localDefEqReplace
      else
        .localAssertClear (proofPresence result)
    subjects := subjects.push {
      subject := .local subjectRef
      initialFingerprint := recording.program.initialFingerprint
      program := recording.program
      terminal
      deferred := recording.deferred
      simprocs := recording.simprocs
    }
    match result.proof? with
    | some _ =>
        match (← applySimpResult mvarIdNew (mkFVar fvarId) type result) with
        | none => return { result? := none, subjects, branches }
        | some (value, type) =>
            toAssert := toAssert.push {
              userName := localDecl.userName, type := type, value := value }
    | none =>
        if result.expr.isFalse then
          mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
          return { result? := none, subjects, branches }
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId result.expr
        replaced := replaced.push fvarId
  if simplifyTarget then
    let (target, result, statsNew, recording) ← mvarIdNew.withContext do
      let target ← instantiateMVars (← mvarIdNew.getType)
      let (result, statsNew, recording) ← recordExpression target ctx methods stats
      return (target, result, statsNew, recording)
    stats := statsNew
    branches := branches ++ recording.coveredBranches
    let terminal := if result.expr.isTrue then
      Simp.Engine.SubjectTerminal.targetTrue (proofPresence result)
    else
      .targetTransport (proofPresence result)
    subjects := subjects.push {
      subject := .target
      initialFingerprint := recording.program.initialFingerprint
      program := recording.program
      terminal
      deferred := recording.deferred
      simprocs := recording.simprocs
    }
    if result.expr.isTrue then
      mvarIdNew.withContext do
        match result.proof? with
        | some proof => mvarIdNew.assign (← mkOfEqTrue proof)
        | none => mvarIdNew.assign (mkConst ``True.intro)
      return { result? := none, subjects, branches }
    let next ← mvarIdNew.withContext do
      applySimpResultToTarget mvarIdNew target result
    mvarIdNew := next
  let (fvarIdsNew, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
  mvarIdNew := mvarIdNew'
  let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
  mvarIdNew ← mvarIdNew.tryClearMany toClear
  if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
    throwError "`simp` made no progress"
  return { result? := some (fvarIdsNew, mvarIdNew), subjects, branches }

def locationSubjects (location : Location) : TacticM (Array FVarId × Bool) := do
  match location with
  | .targets hyps simplifyTarget =>
      return (← getFVarIds hyps, simplifyTarget)
  | .wildcard =>
      return (← (← getMainGoal).getNondepPropHyps, true)

def goalsAfter (tail : List MVarId)
    (result? : Option (Array FVarId × MVarId)) : List MVarId :=
  match result? with
  | none => tail
  | some (_, goal) => goal :: tail

private def logCertificate (certificate : Simp.Engine.Certificate)
    (branches : Array String) (occurrenceId? : Option String := none) : TacticM Unit := do
  let eventCount := certificate.subjects.foldl (init := (0 : Nat)) fun count subject =>
    count + subject.program.events.size
  let structuralCount := certificate.subjects.foldl (init := (0 : Nat)) fun count subject =>
    count + subject.program.structural.size
  let simprocCount := certificate.subjects.foldl (init := (0 : Nat)) fun count subject =>
    count + subject.simprocs.size
  let deferredCount := certificate.subjects.foldl (init := (0 : Nat)) fun count subject =>
    if subject.deferred.isSome then count + 1 else count
  let occurrence := occurrenceId?.map (fun id => s!" occurrence={id}") |>.getD ""
  logInfo m!"SIMP_ENGINE_RECORDING{occurrence} branches={String.intercalate "," branches.toList} events={eventCount} structural={structuralCount} simprocs={simprocCount} deferredSubjects={deferredCount} subjects={certificate.subjects.size}"

structure TacticRecording where
  ctx : Simp.Context
  certificate : Simp.Engine.Certificate
  branches : Array String
  fvarIds : Array FVarId
  simplifyTarget : Bool

/-- Record and validate one tactic execution. When `commitReference` is true,
    leave the verified upstream result in the tactic state; otherwise restore
    the post-context initial state so the returned certificate can be replayed. -/
def recordCertificate (simpStx : Syntax) (commitReference : Bool := false)
    (onReferenceFailure : TacticM Unit := pure ()) : TacticM TacticRecording := do
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  let (fvarIds, simplifyTarget) ← locationSubjects (expandOptLocation simpStx[5])
  let initialMeta ← Meta.saveState
  let initialGoals ← getGoals
  let mainGoal := initialGoals.head!
  let tail := initialGoals.tail
  let initialState ← Simp.Engine.proofStateFingerprint initialGoals
  let (certificate, branches) ← dischargeWrapper.with fun discharge? => do
    let (referenceResult, _) ← try
      Meta.simpGoal mainGoal ctx
        (simprocs := simprocs) (discharge? := discharge?)
        (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIds)
    catch error =>
      onReferenceFailure
      throw error
    let referenceGoals := goalsAfter tail referenceResult
    setGoals referenceGoals
    let referenceFinal ← Simp.Engine.proofStateFingerprint referenceGoals
    let referenceMeta ← Meta.saveState
    initialMeta.restore
    setGoals initialGoals
    let methods := match discharge? with
      | none => Simp.Engine.mkDefaultMethodsCore simprocs
      | some discharge => Simp.Engine.mkMethods simprocs discharge
          (wellBehavedDischarge := false)
    let recorded ← recordGoal mainGoal ctx methods simplifyTarget fvarIds
    let recordedGoals := goalsAfter tail recorded.result?
    setGoals recordedGoals
    let finalState ← Simp.Engine.proofStateFingerprint recordedGoals
    let certificate : Simp.Engine.Certificate := {
      config := ← Simp.Engine.replayConfigOfContext ctx
      subjects := recorded.subjects
      initialState
      finalState
    }
    unless referenceFinal == certificate.finalState do
      throwError "record_mode_mismatch: final proof state"
    if commitReference then
      referenceMeta.restore
      setGoals referenceGoals
    else
      initialMeta.restore
      setGoals initialGoals
    return (certificate, recorded.branches)
  return { ctx, certificate, branches, fvarIds, simplifyTarget }

private def recordTactic (simpStx : Syntax) (occurrenceId? : Option String := none) : TacticM Unit := do
  let recording ← recordCertificate simpStx (commitReference := true)
  logCertificate recording.certificate recording.branches occurrenceId?

private def recordObservation (simpStx : Syntax) (target : Expr) : TacticM Unit := do
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  let initialMeta ← Meta.saveState
  let initialGoals ← getGoals
  let recording ← dischargeWrapper.with fun discharge? => do
    let methods := match discharge? with
      | none => Simp.Engine.mkDefaultMethodsCore simprocs
      | some discharge => Simp.Engine.mkMethods simprocs discharge
          (wellBehavedDischarge := false)
    let (_, _, recording) ← recordExpression target ctx methods {}
    return recording
  initialMeta.restore
  setGoals initialGoals
  logRecording recording

private def recordDSimpTarget (dsimpStx : Syntax) (target : Expr) : TacticM Unit := do
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext dsimpStx (eraseLocal := false)
  let initialMeta ← Meta.saveState
  let initialGoals ← getGoals
  let recording ← dischargeWrapper.with fun discharge? => do
    let methods := match discharge? with
      | none => Simp.Engine.mkDefaultMethodsCore simprocs
      | some discharge => Simp.Engine.mkMethods simprocs discharge
          (wellBehavedDischarge := false)
    let (reference, referenceState) ← Simp.Engine.dsimpMainCore target ctx (methods := methods)
    initialMeta.restore
    setGoals initialGoals
    let (recorded, recordedState, recording) ←
      Simp.Engine.dsimpMainCoreRecording target ctx (methods := methods)
    assertRecordedEquivalent { expr := reference } { expr := recorded }
      referenceState recordedState
    return recording
  initialMeta.restore
  setGoals initialGoals
  logRecording recording

elab_rules : tactic
  | `(tactic| simp_engine_recording $args:simpEngineRecordingArgs) => withMainContext do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordTactic inner
  | `(tactic| simp_engine_observe $args:simpEngineRecordingArgs) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordObservation inner target
  | `(tactic| dsimp_engine_observe $args:dsimpEngineRecordingArgs) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let inner := mkNode ``Lean.Parser.Tactic.dsimp #[
        mkAtom "dsimp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordDSimpTarget inner target

end ExplicitLean.SimpEngine.Recording
