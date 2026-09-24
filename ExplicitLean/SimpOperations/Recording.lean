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

private def nameLocationSubjects
    (operations : Array Lean.Meta.Simp.Operations.SubjectTrace)
    (names : Array (Option String)) :
    Array Lean.Meta.Simp.Operations.SubjectTrace :=
  let initial : Nat × Array Lean.Meta.Simp.Operations.SubjectTrace := (0, #[])
  (operations.foldl (init := initial) fun (localIndex, result) operation =>
    match operation.subject with
    | Lean.Meta.Simp.Operations.Subject.target =>
      (localIndex, result.push operation)
    | Lean.Meta.Simp.Operations.Subject.namedLocal _ =>
      (localIndex, result.push operation)
    | Lean.Meta.Simp.Operations.Subject.local _ =>
      let operation := match names[localIndex]?.join with
        | some source =>
          ⟨Lean.Meta.Simp.Operations.Subject.namedLocal source, operation.trace⟩
        | none => operation
      (localIndex + 1, result.push operation)).2

/-- Return the authored identifier for a wildcard location subject when that
identifier denotes exactly one declaration in the source context.  Raw
`LocalDecl.index` values are elaborator-state identities: observer
instrumentation may allocate locals before the replacement is elaborated, so
those numbers are not a stable source-level address across the two runs. -/
private def sourceLocationName? (lctx : LocalContext) (fvarId : FVarId) : Option String := do
  let decl ← lctx.find? fvarId
  let name := decl.userName
  if name.isAnonymous || name.isInaccessibleUserName || name.hasMacroScopes then
    none
  else
    let mut occurrences := 0
    for other in lctx do
      if other.userName == name then occurrences := occurrences + 1
    if occurrences == 1 then some name.toString else none

private def observeLocations (simpStx : Syntax) :
    TacticM Lean.Meta.Simp.Operations.TacticTrace := do
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  let location := expandOptLocation simpStx[5]
  let (fvarIds, simplifyTarget) ←
    SimpEngine.Recording.locationSubjects location
  let lctx ← getLCtx
  let namedLocals : Array (Option String) := match location with
    | .targets hyps _ => hyps.map fun hyp =>
        some <| match hyp with
          | Syntax.ident _ rawVal _ _ => rawVal.toString
          | stx => stx.reprint.getD hyp.getId.toString
    | .wildcard => fvarIds.map (sourceLocationName? lctx)
  let initialMeta ← Simp.Engine.saveFullMetaState
  let initialGoals ← getGoals
  let mainGoal := initialGoals.head!
  try
    dischargeWrapper.with fun discharge? => do
      let methods := match discharge? with
        | none => Simp.Engine.mkDefaultMethodsCore simprocs
        | some discharge => Simp.Engine.mkMethods simprocs discharge
            (wellBehavedDischarge := false)
      let recorded ← SimpEngine.Recording.recordGoal
        mainGoal ctx methods simplifyTarget fvarIds
      return { subjects := nameLocationSubjects recorded.operations namedLocals }
  finally
    initialMeta.restore
    setGoals initialGoals

private def observeAndLog (simpStx : Syntax) (site? : Option Nat := none) : TacticM Unit := do
  let payload ←
    if simpStx[5].isNone then
      let target ← instantiateMVars (← (← getMainGoal).getType)
      Lean.toJson <$> observe simpStx target
    else
      Lean.toJson <$> observeLocations simpStx
  match site? with
  | none => logInfo m!"SIMP_OPERATIONS {payload.compress}"
  | some site => logInfo m!"SIMP_OPERATIONS_SITE {site} {payload.compress}"

elab_rules : tactic
  | `(tactic| simp_operations_observe $args:simpEngineRecordingArgs) => withMainContext do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      observeAndLog inner
  | `(tactic| simp_operations_observe_at $site:num $args:simpEngineRecordingArgs) =>
      withMainContext do
        let inner := mkNode ``Lean.Parser.Tactic.simp #[
          mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
        observeAndLog inner (some site.getNat)

end ExplicitLean.SimpOperations.Recording
