import ExplicitLean.SimpTrace
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Real.Basic

open Lean Lean.Meta ExplicitLean.SimpTrace

/- Assigned metavariables owned by a temporary matching context must be
resolved before trace data leaves that context. Conversely, an unassigned
metavariable from the enclosing context remains live and is preserved. -/
run_cmd do
  let (snapshot, universeOnlySnapshot, outer, outerId, innerId, instanceId) ←
      Lean.Elab.Command.liftTermElabM do
    let outer ← mkFreshExprMVar (mkConst ``Nat)
    let outerId ← mkFreshFVarId
    let innerId ← mkFreshFVarId
    let instanceId ← mkFreshFVarId
    let (snapshot, universeOnlySnapshot) ← withNewMCtxDepth do
      let u ← mkFreshLevelMVar
      let α ← mkFreshExprMVar (mkSort (.succ u))
      let a ← mkFreshExprMVar α
      let b ← mkFreshExprMVar α
      assignLevelMVar u.mvarId! .zero
      α.mvarId!.assign (mkConst ``Nat)
      a.mvarId!.assign (mkNatLit 2)
      b.mvarId!.assign (mkNatLit 0)
      let before := mkAppN (mkConst ``Ne [.succ u]) #[α, a, b]
      let eq := mkAppN (mkConst ``Eq [.succ u]) #[α, a, b]
      let after := mkApp (mkConst ``Not) eq
      let instanceType := mkApp (mkConst ``Inhabited [u]) α
      let lctx := ({} : LocalContext)
        |>.mkLetDecl outerId `outer (mkConst ``Nat) outer
        |>.mkLetDecl innerId `inner α a
        |>.mkLocalDecl instanceId `inst instanceType .instImplicit
      let insts : LocalInstances := #[{
        className := ``Inhabited, fvar := mkFVar instanceId }]
      let ctx : EvCtx := { lctx := lctx, insts := insts }
      let ev := Event.rw #[] (.decl ``ne_eq true false) false none before after ctx
        #[] #[] none (.decl ``ne_eq true false) "" none none
      let snapshot ← Event.instantiateAssignments ev
      let universeOnlySnapshot ← instantiateEventAssignments (mkConst ``List [u])
      pure (snapshot, universeOnlySnapshot)
    pure (snapshot, universeOnlySnapshot, outer, outerId, innerId, instanceId)
  let (before, after, ctx) ← match snapshot with
    | .rw _ _ _ _ before after ctx _ _ _ _ _ _ _ => pure (before, after, ctx)
    | _ => throwError "expected a rewrite snapshot"
  if before.hasLevelMVar || after.hasLevelMVar then
    throwError "temporary universe metavariable escaped the event snapshot"
  if universeOnlySnapshot.hasLevelMVar then
    throwError "assigned universe-only expression escaped the event snapshot"
  let some (.ldecl _ _ _ innerType innerValue _ _) := ctx.lctx.find? innerId
    | throwError "missing snapshotted local declaration"
  unless innerType == mkConst ``Nat && innerValue == mkNatLit 2 do
    throwError "temporary term metavariable escaped the event context"
  let some (.ldecl _ _ _ _ outerValue _ _) := ctx.lctx.find? outerId
    | throwError "missing enclosing local declaration"
  unless outerValue == outer do
    throwError "an unassigned enclosing metavariable was not preserved"
  let some (.cdecl _ _ _ instanceType _ _) := ctx.lctx.find? instanceId
    | throwError "missing local instance declaration"
  let expectedInstanceType :=
    mkApp (mkConst ``Inhabited [.zero]) (mkConst ``Nat)
  unless instanceType == expectedInstanceType do
    throwError "temporary assignments in a local instance type were not snapshotted"
  unless ctx.insts.size == 1 && ctx.insts[0]!.fvar == mkFVar instanceId do
    throwError "the local instance reference was not preserved"
  let reason ← Lean.Elab.Command.liftTermElabM do
    checkRwStep (.decl ``ne_eq true false) #[] false none before after ctx
      #[] "" none
  if let some reason := reason then
    throwError "snapshotted ne_eq step did not validate: {reason}"

/- `recordEvent` checks liveness only when called at an identified temporary
depth boundary. The before/after expressions below are definitionally equal but
structurally distinct, so the test reaches the gate instead of no-op elision. It
rejects child-depth term and universe metavariables, but preserves valid
enclosing-depth metavariables and ordinary outer-depth events. -/
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    let ref : TraceRef ← ST.mkRef ({} : ExplicitLean.SimpTrace.TraceState)
    let termRef : TraceRef ← ST.mkRef ({} : ExplicitLean.SimpTrace.TraceState)
    let levelRef : TraceRef ← ST.mkRef ({} : ExplicitLean.SimpTrace.TraceState)
    let assignedLevelRef : TraceRef ← ST.mkRef ({} : ExplicitLean.SimpTrace.TraceState)
    let outerLevelRef : TraceRef ← ST.mkRef ({} : ExplicitLean.SimpTrace.TraceState)
    let outer ← mkFreshExprMVar (mkConst ``Nat)
    let .mvar outerTermId := outer | throwError "expected enclosing term metavariable"
    let outerLevel ← mkFreshLevelMVar
    let simpCtx ← Simp.Context.mkDefault
    let (_, _) ← Simp.SimpM.run simpCtx {} {} do
      withNewMCtxDepth do
        unless !(← outerTermId.isAssignable) do
          throwError "enclosing term metavariable became assignable at child depth"
        unless !(← isLevelMVarAssignable outerLevel.mvarId!) do
          throwError "enclosing universe metavariable became assignable at child depth"
        let outerApplied := mkApp (mkConst ``id [.succ .zero]) outer
        recordEvent ref (.defeq #[] .change none outerApplied outer {}) true
        let outerUniverseTerm := mkConst ``List [outerLevel]
        let outerUniverseApplied := mkApp
          (mkConst ``id [.succ outerLevel]) outerUniverseTerm
        recordEvent outerLevelRef
          (.defeq #[] .change none outerUniverseApplied outerUniverseTerm {}) true
        let innerTerm ← mkFreshExprMVar (mkConst ``Nat)
        unless (← innerTerm.mvarId!.isAssignable) do
          throwError "child term metavariable is not assignable at child depth"
        let innerApplied := mkApp (mkConst ``id [.succ .zero]) innerTerm
        recordEvent termRef (.defeq #[] .change none innerApplied innerTerm {}) true
        let innerLevel ← mkFreshLevelMVar
        unless (← isLevelMVarAssignable innerLevel.mvarId!) do
          throwError "child universe metavariable is not assignable at child depth"
        let innerUniverseTerm := mkConst ``List [innerLevel]
        let innerUniverseApplied := mkApp
          (mkConst ``id [.succ innerLevel]) innerUniverseTerm
        recordEvent levelRef
          (.defeq #[] .change none innerUniverseApplied innerUniverseTerm {}) true
        let assignedLevel ← mkFreshLevelMVar
        assignLevelMVar assignedLevel.mvarId! .zero
        let assignedUniverseTerm := mkConst ``List [assignedLevel]
        let assignedUniverseApplied := mkApp
          (mkConst ``id [.succ assignedLevel]) assignedUniverseTerm
        recordEvent assignedLevelRef
          (.defeq #[] .change none assignedUniverseApplied assignedUniverseTerm {}) true
      let outerTerm ← mkFreshExprMVar (mkConst ``Nat)
      let outerApplied := mkApp (mkConst ``id [.succ .zero]) outerTerm
      recordEvent ref (.defeq #[] .change none outerApplied outerTerm {})
    let state ← ref.get
    let termState ← termRef.get
    let levelState ← levelRef.get
    let assignedLevelState ← assignedLevelRef.get
    let outerLevelState ← outerLevelRef.get
    unless state.events.size == 2 do
      throwError "temporary-depth event gate rejected a valid outer metavariable"
    unless termState.events.isEmpty && termState.unresolved.contains
        "trace_event_has_unassigned_temporary_metavariable" do
      throwError "unassigned temporary term metavariable was not rejected"
    unless levelState.events.isEmpty && levelState.unresolved.contains
        "trace_event_has_unassigned_temporary_metavariable" do
      throwError "unassigned temporary universe metavariable was not rejected"
    unless assignedLevelState.events.size == 1 && assignedLevelState.unresolved.isEmpty do
      throwError "assigned temporary universe metavariable was rejected"
    let .defeq _ _ _ assignedUniverseSnapshot _ _ := assignedLevelState.events[0]!
      | throwError "expected the assigned universe-only event"
    unless assignedUniverseSnapshot ==
        mkApp (mkConst ``id [.succ .zero]) (mkConst ``List [.zero]) do
      throwError "assigned temporary universe level was not snapshotted"
    unless outerLevelState.events.size == 1 && outerLevelState.unresolved.isEmpty do
      throwError "valid enclosing universe metavariable was rejected"
    let .defeq _ _ _ retainedOuterLevel _ _ := outerLevelState.events[0]!
      | throwError "expected the enclosing universe event"
    unless retainedOuterLevel ==
        mkApp (mkConst ``id [.succ outerLevel]) (mkConst ``List [outerLevel]) do
      throwError "enclosing universe metavariable was not retained"
    let .defeq _ _ _ retainedOuter _ _ := state.events[0]!
      | throwError "expected the outer-depth event first"
    unless retainedOuter == mkApp (mkConst ``id [.succ .zero]) outer do
      throwError "temporary-depth check discarded a valid enclosing metavariable"
    let .defeq _ _ _ retainedCurrent _ _ := state.events[1]!
      | throwError "expected the ordinary outer-depth event second"
    unless retainedCurrent.hasMVar do
      throwError "ordinary outer-depth event did not retain its live metavariable"

/- A real `div_self` side trace exercises the same event boundary through the
recorder and its in-tactic validator. -/
example : (2 : ℝ) / 2 = 1 := by
  simp_trace =>trace "NESTED_NE_EQ_TRACE_PATH"
