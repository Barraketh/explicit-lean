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

private def recordTarget (simpStx : Syntax) (target : Expr) : TacticM Unit := do
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  let initialMeta ← Meta.saveState
  let initialGoals ← getGoals
  let recording ← dischargeWrapper.with fun discharge? => do
    let methods := match discharge? with
      | none => Simp.Engine.mkDefaultMethodsCore simprocs
      | some discharge => Simp.Engine.mkMethods simprocs discharge
          (wellBehavedDischarge := false)
    let (reference, referenceState) ← Simp.Engine.mainCore target ctx (methods := methods)
    initialMeta.restore
    setGoals initialGoals
    let (recorded, recordedState, recording) ←
      Simp.Engine.mainCoreRecording target ctx (methods := methods)
    assertRecordedEquivalent reference recorded referenceState recordedState
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
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordTarget inner target
      evalTactic inner
  | `(tactic| simp_engine_observe $args:simpEngineRecordingArgs) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordTarget inner target
  | `(tactic| dsimp_engine_observe $args:dsimpEngineRecordingArgs) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let inner := mkNode ``Lean.Parser.Tactic.dsimp #[
        mkAtom "dsimp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordDSimpTarget inner target

end ExplicitLean.SimpEngine.Recording
