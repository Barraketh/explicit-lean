module

public meta import ExplicitLean.SimpEngine.Recording

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

/-- Observe the target with stock simp configuration and print the exact,
term-free operation stream without changing the proof state. -/
syntax (name := simpOperationsObserve)
  "simp_operations_observe" simpEngineRecordingArgs : tactic

/-- Internal retry-pipeline form carrying a source-site label outside the
operation JSON.  The label is correlation metadata only; the trace schema and
its term-free payload are unchanged. -/
syntax (name := simpOperationsObserveAt)
  "simp_operations_observe_at " num simpEngineRecordingArgs : tactic

end Lean.Parser.Tactic

namespace ExplicitLean.SimpOperations.Recording

private def observe (simpStx : Syntax) (target : Expr) :
    TacticM Lean.Meta.Simp.Operations.Trace := do
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  let initialMeta ← Simp.Engine.saveFullMetaState
  let initialGoals ← getGoals
  try
    dischargeWrapper.with fun discharge? => do
      let methods := match discharge? with
        | none => Simp.Engine.mkDefaultMethodsCore simprocs
        | some discharge => Simp.Engine.mkMethods simprocs discharge
            (wellBehavedDischarge := false)
      let (_, _, _, trace) ←
        Simp.Engine.mainCoreOperationalRecording target ctx (methods := methods)
      return trace
  finally
    initialMeta.restore
    setGoals initialGoals

elab_rules : tactic
  | `(tactic| simp_operations_observe $args:simpEngineRecordingArgs) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      let trace ← observe inner target
      logInfo m!"SIMP_OPERATIONS {Lean.toJson trace |>.compress}"
  | `(tactic| simp_operations_observe_at $site:num $args:simpEngineRecordingArgs) =>
      withMainContext do
        let target ← instantiateMVars (← (← getMainGoal).getType)
        let inner := mkNode ``Lean.Parser.Tactic.simp #[
          mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
        let trace ← observe inner target
        logInfo m!"SIMP_OPERATIONS_SITE {site.getNat} {Lean.toJson trace |>.compress}"

end ExplicitLean.SimpOperations.Recording
