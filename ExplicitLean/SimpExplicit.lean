module

public meta import Lean.Elab.Tactic.Simp
public import Lean.Elab.Tactic.Simp
public meta import Lean.Meta.Tactic.Refl

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

syntax simpExplicitPre := "↓"
syntax simpExplicitPost := "↑"
syntax simpExplicitRule := (simpExplicitPre <|> simpExplicitPost)? "← "? term
syntax simpExplicitEvent := (num " => ")? simpExplicitRule
syntax simpExplicitTraceArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?

/-- Replay an ordered simplifier certificate without consulting the simp set. -/
syntax (name := simpExplicit) "simp_explicit" " [" simpExplicitEvent,* "]" : tactic
/-- Run `simp` once and report an equivalent `simp_explicit` certificate. -/
syntax (name := simpExplicitTrace) "simp_explicit?" simpExplicitTraceArgs : tactic

end Lean.Parser.Tactic

namespace ExplicitLean

namespace SimpExplicit

inductive Phase where
  | pre
  | post
  deriving BEq, Repr

private structure RecordedEvent where
  tick : Nat
  phase : Phase
  origin : Origin

private structure RecorderState where
  tick : Nat := 0
  events : Array RecordedEvent := #[]

private def changedResult? (input : Expr) : Simp.Step → Option Simp.Result
  | .done result | .visit result =>
      if result.expr == input then none else some result
  | .continue result? => result?.bind fun result =>
      if result.expr == input then none else some result

private def changedOrigins (before after : Simp.Diagnostics) : Array Origin := Id.run do
  let mut result := #[]
  for (origin, count) in after.usedThmCounter.toArray do
    let previous := before.usedThmCounter.find? origin |>.getD 0
    for _ in *...(count - previous) do
      result := result.push origin
  return result

private def trackedMethod (ref : IO.Ref RecorderState) (phase : Phase)
    (method : Simp.Simproc) : Simp.Simproc := fun input => do
  let state ← ref.get
  let tick := state.tick + 1
  ref.set { state with tick }
  let before := (← get).diag
  let step ← method input
  let after := (← get).diag
  if (changedResult? input step).isSome then
    match changedOrigins before after with
    | #[origin] =>
        let state ← ref.get
        ref.set { state with events := state.events.push { tick, phase, origin } }
    | origins =>
        throwError "simp_explicit recorder cannot encode this simplifier step: expected one theorem rewrite, observed {origins.size} recorded rules"
  return step

private def recordingMethods (ref : IO.Ref RecorderState)
    (simprocs : Simp.SimprocsArray) (discharge? : Option Simp.Discharge) : Simp.Methods :=
  let methods := match discharge? with
    | none => Simp.mkDefaultMethodsCore simprocs
    | some discharge => Simp.mkMethods simprocs discharge (wellBehavedDischarge := false)
  { methods with
    pre := trackedMethod ref .pre methods.pre
    post := trackedMethod ref .post methods.post
    discharge? := fun proposition => do
      if (← methods.discharge? proposition).isSome then
        throwError "simp_explicit recorder cannot yet encode a discharged side condition"
      return none }

private def ruleText (origin : Origin) : MetaM String := do
  match origin with
  | .decl name _ inverse =>
      if (← Simp.isBuiltinSimproc name) || (← Simp.isSimproc name) then
        throwError "simp_explicit cannot yet encode simproc '{name}'"
      -- Keep declaration names fully qualified. Besides making certificates
      -- robust when pasted under a different namespace, this ensures that a
      -- printed positional certificate elaborates to the same simp theorem
      -- used while recording it.
      return (if inverse then "← " else "") ++ name.toString
  | .fvar fvarId =>
      let localDecl ← fvarId.getDecl
      if localDecl.userName.isInaccessibleUserName then
        throwError "simp_explicit cannot print inaccessible local simp lemma '{localDecl.userName}'"
      return localDecl.userName.toString
  | .stx _ ref =>
      let inverse := !ref[1].isNone
      let term := toString ref[2].prettyPrint
      return (if inverse then "← " else "") ++ term
  | .other name =>
      throwError "simp_explicit cannot yet encode special simp rule '{name}'"

private def isReflexiveClosure : Origin → Bool
  | .decl name _ _ => name == ``eq_self || name == ``iff_self
  | _ => false

private def certificateEventCount (events : Array RecordedEvent) : Nat := Id.run do
  let mut eventCount := events.size
  while true do
    if eventCount == 0 then
      break
    match events[eventCount - 1]? with
    | some event =>
        if isReflexiveClosure event.origin then
          eventCount := eventCount - 1
        else
          break
    | none => break
  return eventCount

private def certificateText (events : Array RecordedEvent) (withPositions := false) : MetaM String := do
  let eventCount := certificateEventCount events
  if eventCount == 0 then
    return "simp_explicit []"
  let mut lines := #["simp_explicit ["]
  for index in *...eventCount do
    let some event := events[index]?
      | throwError "simp_explicit recorder produced an inconsistent event count"
    let rule ← ruleText event.origin
    let comma := if index + 1 < eventCount then "," else ""
    let phase := if event.phase == .pre then "↓ " else ""
    let position := if withPositions then s!"{event.tick} => " else ""
    lines := lines.push s!"  {position}{phase}{rule}{comma}"
  lines := lines.push "]"
  return String.intercalate "\n" lines.toList

private def applyResultToTarget (mvarId : MVarId) (target : Expr)
    (result : Simp.Result) : TacticM Unit := do
  if result.expr.isTrue then
    let proof ← match result.proof? with
      | some equality => mkOfEqTrue equality
      | none => pure (mkConst ``True.intro)
    mvarId.assign proof
    replaceMainGoal []
  else
    let mvarId ← applySimpResultToTarget mvarId target result
    let simplifiedTarget ← instantiateMVars (← mvarId.getType)
    if simplifiedTarget.isAppOfArity ``Eq 3 then
      try
        mvarId.refl
        replaceMainGoal []
        return
      catch _ => pure ()
    else if simplifiedTarget.isAppOfArity ``Iff 2 then
      let lhs := simplifiedTarget.appFn!.appArg!
      let rhs := simplifiedTarget.appArg!
      if (← isDefEq lhs rhs) then
        mvarId.assign (mkApp (mkConst ``Iff.rfl) lhs)
        replaceMainGoal []
        return
    replaceMainGoal [mvarId]

private structure ReplayEvent where
  tick? : Option Nat
  phase : Phase
  rules : Array SimpTheorem
  source : Syntax

private structure ReplayState where
  tick : Nat := 0
  next : Nat := 0

private def parsePhase (stx : Syntax) : TacticM Phase :=
  if stx.isOfKind ``Lean.Parser.Tactic.simpExplicitPre then
    pure .pre
  else if stx.isOfKind ``Lean.Parser.Tactic.simpExplicitPost then
    pure .post
  else
    throwErrorAt stx "expected `↓` or `↑`"

private def elaborateRule (phase : Phase) (rule : Syntax) : TacticM (Array SimpTheorem) := do
  let inverse := !rule[1].isNone
  let term := rule[2]
  let proof? ← Term.withoutModifyingElabMetaStateWithInfo <| withRef term do
    let proof ← Term.elabTerm term .none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let proof ← instantiateMVars proof
    if proof.hasSyntheticSorry then
      return none
    let proof := proof.eta
    if proof.hasMVar then
      let abstracted ← abstractMVars proof
      return some (abstracted.paramNames, abstracted.expr)
    return some (#[], proof)
  let some (levelParams, proof) := proof?
    | throwErrorAt term "could not elaborate explicit simp rule"
  let origin := Origin.stx (← mkFreshId) rule
  mkSimpTheoremFromExpr origin levelParams proof
    (inv := inverse) (post := phase == .post)

private def elaborateEvent (stx : Syntax) : TacticM ReplayEvent := do
  let tick? := if stx[0].isNone then none else stx[0][0].isNatLit?
  if tick? == some 0 then
    throwErrorAt stx[0] "simp_explicit traversal positions start at 1"
  let rule := stx[1]
  let phase ← if rule[0].isNone then pure .post else parsePhase rule[0][0]
  let rules ← elaborateRule phase rule
  return { tick?, phase, rules, source := stx }

private def recordedReplayEvent (event : RecordedEvent) (withPosition : Bool) : TacticM ReplayEvent := do
  let post := event.phase == .post
  let (rules, source) ← match event.origin with
    | .decl name _ inverse =>
        if (← Simp.isBuiltinSimproc name) || (← Simp.isSimproc name) then
          throwError "simp_explicit cannot yet encode simproc '{name}'"
        pure (← mkSimpTheoremFromConst name (post := post) (inv := inverse), (mkIdent name).raw)
    | .fvar fvarId =>
        let localDecl ← fvarId.getDecl
        let rules ← mkSimpTheoremFromExpr event.origin #[] (mkFVar fvarId) (post := post)
        pure (rules, (mkIdent localDecl.userName).raw)
    | .stx _ ref =>
        pure (← elaborateRule event.phase ref, ref)
    | .other name =>
        throwError "simp_explicit cannot yet encode special simp rule '{name}'"
  return {
    tick? := if withPosition then some event.tick else none
    phase := event.phase
    rules
    source
  }

private def applyRecordedRules? (input : Expr) (event : ReplayEvent) : Simp.SimpM (Option Simp.Result) := do
  for rule in event.rules do
    if let some result ← Simp.tryTheorem? input rule then
      return some result
  return none

private def replayMethod (events : Array ReplayEvent) (ref : IO.Ref ReplayState)
    (phase : Phase) : Simp.Simproc := fun input => do
  let state ← ref.get
  let state := { state with tick := state.tick + 1 }
  ref.set state
  if h : state.next < events.size then
    let event := events[state.next]
    match event.tick? with
    | some tick =>
        if tick < state.tick then
          throwErrorAt event.source "simp_explicit passed recorded traversal position {tick} without applying its rule"
        else if tick == state.tick then
          unless event.phase == phase do
            throwErrorAt event.source "simp_explicit traversal phase changed at position {tick}"
          let some result ← applyRecordedRules? input event
            | throwErrorAt event.source "recorded simp rule no longer rewrites the expression at traversal position {tick}"
          ref.set { state with next := state.next + 1 }
          return .visit result
    | none =>
        if event.phase == phase then
          if let some result ← applyRecordedRules? input event then
            ref.set { state with next := state.next + 1 }
            return .visit result
  return .continue

private def runReplay (target : Expr) (events : Array ReplayEvent) : TacticM (Simp.Result × ReplayState) := do
  let congrTheorems ← getSimpCongrTheorems
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := congrTheorems)
  let ref ← IO.mkRef ({} : ReplayState)
  let methods : Simp.Methods := {
    pre := replayMethod events ref .pre
    post := replayMethod events ref .post
    discharge? := fun _ => return none
  }
  let (result, _) ← Simp.mainCore target ctx (methods := methods)
  return (result, ← ref.get)

private def replaySimp (eventSyntax : Array Syntax) : TacticM Unit := withMainContext do
  let events ← eventSyntax.mapM elaborateEvent
  let mut previousTick? : Option Nat := none
  for event in events do
    if let some tick := event.tick? then
      if let some previousTick := previousTick? then
        if previousTick >= tick then
          throwErrorAt event.source "explicit traversal positions must be strictly increasing"
      previousTick? := some tick
  let mvarId ← getMainGoal
  let target ← instantiateMVars (← mvarId.getType)
  let (result, state) ← runReplay target events
  unless state.next == events.size do
    match events[state.next]? with
    | some event =>
        match event.tick? with
        | some tick =>
            throwErrorAt event.source "simp_explicit ended before recorded traversal position {tick}"
        | none =>
            throwErrorAt event.source "ordered simp rule did not match anywhere in the remaining traversal"
    | none =>
        throwError "simp_explicit replay cursor is inconsistent"
  applyResultToTarget mvarId target result

private def isReflexiveResult (expr : Expr) : MetaM Bool := do
  if expr.isTrue then
    return true
  if expr.isAppOfArity ``Eq 3 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  if expr.isAppOfArity ``Iff 2 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  return false

private def canReplay (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) (withPositions : Bool) : TacticM Bool := do
  try
    withoutModifyingState do
      let count := certificateEventCount recorded
      let mut events := #[]
      for index in *...count do
        let some event := recorded[index]? | return false
        events := events.push (← recordedReplayEvent event (withPosition := withPositions))
      let (replayedResult, replayState) ← runReplay target events
      unless replayState.next == events.size do
        return false
      if searchedResult.expr.isTrue then
        isReflexiveResult replayedResult.expr
      else
        -- Subsequent syntax-sensitive tactics such as `rw` can distinguish
        -- definitionally equal goals. A certificate must reproduce the
        -- simplifier's actual output expression, not just its proposition.
        return searchedResult.expr == replayedResult.expr
  catch _ =>
    return false

private def recordSimp (simpStx reportStx : Syntax) : TacticM Unit := withMainContext do
  unless simpStx.getKind == ``Lean.Parser.Tactic.simp do
    throwErrorAt simpStx "simp_explicit? currently accepts one `simp` tactic"
  unless simpStx[5].isNone do
    throwErrorAt simpStx "simp_explicit? currently supports the target only"
  unless simpStx[1][0].isNone do
    throwErrorAt simpStx[1] "simp_explicit? does not yet encode nondefault simp configuration"
  unless simpStx[2].isNone do
    throwErrorAt simpStx[2] "simp_explicit? does not yet encode a custom discharger"
  let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext simpStx (eraseLocal := false)
  let mvarId ← getMainGoal
  let target ← instantiateMVars (← mvarId.getType)
  let ref ← IO.mkRef ({} : RecorderState)
  let result ← dischargeWrapper.with fun discharge? => do
    let methods := recordingMethods ref simprocs discharge?
    withOptions (·.setBool `diagnostics true) do
      return (← Simp.mainCore target ctx (methods := methods)).1
  let state ← ref.get
  let positionFree ← canReplay target state.events result (withPositions := false)
  unless positionFree || (← canReplay target state.events result (withPositions := true)) do
    throwErrorAt reportStx "simp_explicit recorder cannot encode this simplification as an exact deterministic replay"
  let suggestion ← certificateText state.events (withPositions := !positionFree)
  logInfoAt reportStx m!"Try this deterministic replay:\n{suggestion}"
  applyResultToTarget mvarId target result

end SimpExplicit

open SimpExplicit

elab_rules : tactic
  | `(tactic| simp_explicit? $args:simpExplicitTraceArgs) => do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], mkNullNode]
      recordSimp inner (← getRef)
  | `(tactic| simp_explicit [$events:simpExplicitEvent,*]) =>
      replaySimp (events.getElems.map (·.raw))

end ExplicitLean
