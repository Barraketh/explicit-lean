module

public meta import ExplicitLean.SimpEngine.Recording

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

syntax simpEngineReplayArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?

syntax (name := simpEngineReplay)
  "simp_engine_replay" simpEngineReplayArgs : tactic

end Lean.Parser.Tactic

namespace ExplicitLean.SimpEngine.Replay

private def checkPresence (expected : Simp.Engine.ProofPresence)
    (result : Simp.Result) : MetaM Unit := do
  unless ExplicitLean.SimpEngine.Recording.proofPresence result == expected do
    throwError "replay_proof_presence_mismatch"

private def replayExpression (expression : Expr) (ctx : Simp.Context)
    (certificate : Simp.Engine.Certificate) (subject : Simp.Engine.SubjectProgram)
    (stats : Simp.Stats) : MetaM (Simp.Result × Simp.Stats) := do
  if let some reason := subject.deferred then
    throwError "replay_deferred: {repr reason}"
  unless subject.simprocs.isEmpty do
    throwError "replay_deferred_simproc_observations"
  let (result, state) ← Simp.Engine.mainCoreReplay expression ctx
    certificate.config subject.program { stats with }
  return (result, { state with })

private structure ReplayedGoal where
  result? : Option (Array FVarId × MVarId)
  consumedSubjects : Nat
  deriving Inhabited

private def replayGoal (mvarId : MVarId) (ctx : Simp.Context)
    (certificate : Simp.Engine.Certificate) (fvarIdsToSimp : Array FVarId)
    (simplifyTarget : Bool) : MetaM ReplayedGoal := mvarId.withContext do
  mvarId.checkNotAssigned `simp_engine_replay
  let mut mvarIdNew := mvarId
  let mut toAssert := #[]
  let mut replaced := #[]
  let mut stats : Simp.Stats := {}
  let mut subjectIndex := 0
  for fvarId in fvarIdsToSimp do
    let some subject := certificate.subjects[subjectIndex]?
      | throwError "replay_missing_local_subject: {subjectIndex}"
    let .local expectedRef := subject.subject
      | throwError "replay_subject_order_mismatch: expected local"
    let localDecl ← fvarId.getDecl
    let actualRef ← ExplicitLean.SimpEngine.Recording.localRef localDecl
    unless actualRef == expectedRef do
      throwError "replay_local_subject_mismatch: expected {repr expectedRef}, got {repr actualRef}"
    let type ← instantiateMVars localDecl.type
    let subjectCtx := ctx.setSimpTheorems <|
      ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId)
    let (result, statsNew) ← replayExpression type subjectCtx certificate subject stats
    stats := statsNew
    match subject.terminal with
    | .localFalse presence =>
        checkPresence presence result
        unless result.expr.isFalse do throwError "replay_expected_local_false"
    | .localDefEqReplace =>
        unless result.proof?.isNone && !result.expr.isFalse do
          throwError "replay_expected_local_defeq_replace"
    | .localAssertClear presence =>
        checkPresence presence result
        unless result.proof?.isSome && !result.expr.isFalse do
          throwError "replay_expected_local_assert_clear"
    | _ => throwError "replay_local_terminal_mismatch"
    subjectIndex := subjectIndex + 1
    match result.proof? with
    | some _ =>
        match (← applySimpResult mvarIdNew (mkFVar fvarId) type result) with
        | none => return { result? := none, consumedSubjects := subjectIndex }
        | some (value, type) =>
            toAssert := toAssert.push {
              userName := localDecl.userName, type := type, value := value }
    | none =>
        if result.expr.isFalse then
          mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
          return { result? := none, consumedSubjects := subjectIndex }
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId result.expr
        replaced := replaced.push fvarId
  if simplifyTarget then
    let some subject := certificate.subjects[subjectIndex]?
      | throwError "replay_missing_target_subject"
    unless subject.subject == .target do
      throwError "replay_subject_order_mismatch: expected target"
    let (target, result, statsNew) ← mvarIdNew.withContext do
      let target ← instantiateMVars (← mvarIdNew.getType)
      let (result, statsNew) ← replayExpression target ctx certificate subject stats
      return (target, result, statsNew)
    stats := statsNew
    match subject.terminal with
    | .targetTrue presence =>
        checkPresence presence result
        unless result.expr.isTrue do throwError "replay_expected_target_true"
    | .targetTransport presence =>
        checkPresence presence result
        if result.expr.isTrue then throwError "replay_expected_target_transport"
    | _ => throwError "replay_target_terminal_mismatch"
    subjectIndex := subjectIndex + 1
    if result.expr.isTrue then
      mvarIdNew.withContext do
        match result.proof? with
        | some proof => mvarIdNew.assign (← mkOfEqTrue proof)
        | none => mvarIdNew.assign (mkConst ``True.intro)
      return { result? := none, consumedSubjects := subjectIndex }
    mvarIdNew ← mvarIdNew.withContext do
      applySimpResultToTarget mvarIdNew target result
  let (fvarIdsNew, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
  mvarIdNew := mvarIdNew'
  let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
  mvarIdNew ← mvarIdNew.tryClearMany toClear
  if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
    throwError "`simp` made no progress"
  return {
    result? := some (fvarIdsNew, mvarIdNew)
    consumedSubjects := subjectIndex
  }

def replayCertificate (recording : ExplicitLean.SimpEngine.Recording.TacticRecording) :
    TacticM Unit := do
  let initialGoals ← getGoals
  let initialState ← Simp.Engine.proofStateFingerprint initialGoals
  unless initialState == recording.certificate.initialState do
    throwError "replay_initial_state_mismatch"
  let mainGoal := initialGoals.head!
  let tail := initialGoals.tail
  let replayed ← replayGoal mainGoal recording.ctx recording.certificate
    recording.fvarIds recording.simplifyTarget
  unless replayed.consumedSubjects == recording.certificate.subjects.size do
    throwError "replay_unconsumed_subjects: {replayed.consumedSubjects}/{recording.certificate.subjects.size}"
  let finalGoals := ExplicitLean.SimpEngine.Recording.goalsAfter tail replayed.result?
  setGoals finalGoals
  let finalState ← Simp.Engine.proofStateFingerprint finalGoals
  unless finalState == recording.certificate.finalState do
    throwError "replay_final_state_mismatch"

private def recordAndReplay (simpStx : Syntax) (occurrenceId? : Option String := none) : TacticM Unit := do
  let recording ← ExplicitLean.SimpEngine.Recording.recordCertificate simpStx
    (commitReference := false)
  replayCertificate recording
  let occurrence := occurrenceId?.map (fun id => s!" occurrence={id}") |>.getD ""
  logInfo m!"SIMP_ENGINE_REPLAY{occurrence} branches={String.intercalate "," recording.branches.toList}"

elab_rules : tactic
  | `(tactic| simp_engine_replay $args:simpEngineReplayArgs) => withMainContext do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordAndReplay inner
end ExplicitLean.SimpEngine.Replay
