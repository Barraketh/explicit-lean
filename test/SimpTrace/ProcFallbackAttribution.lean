import ExplicitLean.SimpTrace
import Mathlib.Order.Compare

open Lean Elab Tactic

/-- Reproduce the nested local rewrite inside `cmpLE_swap`: the rewrite by
`yx` changes the conditional test, while the opaque enclosing match changes to
`Ordering.eq`. They are separate pieces of evidence and must not be conflated. -/
example {α} [LE α] [@Std.Total α (· ≤ ·)] [DecidableLE α] (x y : α)
    (xy : x ≤ y) (yx : y ≤ x) :
    (cmpLE x y).swap = cmpLE y x := by
  simp_trace [cmpLE, *, Ordering.swap] =>trace "PROC_FALLBACK_TRACE_PATH"

/- A theorem-attribution probe may run an instrumented discharger. Its Simp
state and recorder mutations are diagnostic only and must not leak into the
following event. -/
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    let prefixSide : SideRec := .mk (mkConst ``True) #[] (some "true_intro")
      {} #[] (mkConst ``True) none
    let probeSide : SideRec := .mk (mkConst ``False) #[] none
      {} #[] (mkConst ``False) none
    let ref : TraceRef ← ST.mkRef
      ({ pendingSide := #[prefixSide] } : ExplicitLean.SimpTrace.TraceState)
    let addedOrigin : Origin := .decl ``Nat.add_zero true false
    let simpCtx ← Simp.Context.mkDefault
    let (_, _) ← Simp.SimpM.run simpCtx {} {} do
      let initial := (← get).usedTheorems.toArray
      let fresh ← mkFreshExprMVar (mkConst ``Nat)
      isolatedAttributionProbe ref do
        fresh.mvarId!.assign (mkNatLit 7)
        Simp.recordSimpTheorem addedOrigin
        ref.modify fun state =>
          { state with pendingSide := state.pendingSide.push probeSide }
      let after := (← get).usedTheorems.toArray
      unless after == initial do
        throwError "attribution probe changed simp usedTheorems"
      if ← fresh.mvarId!.isAssigned then
        throwError "attribution probe leaked a metavariable assignment"
      let state ← ref.get
      unless state.pendingSide.size == 1 do
        throwError "attribution probe leaked side evidence to the next event"
      let nextSides := state.pendingSide
      recordEvent ref (.eq #[] none (mkConst ``True) (mkConst ``True) {} nextSides)
      let state ← ref.get
      let .eq _ _ _ _ _ recordedSides := state.events[0]!
        | throwError "expected the event following the attribution probe"
      unless recordedSides.size == 1 do
        throwError "the next event received attribution-probe side evidence"
