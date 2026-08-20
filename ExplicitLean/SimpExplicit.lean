module

public import ExplicitLean.Normalize
public meta import ExplicitLean.Normalize
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
/-- Run `simp` once and report an equivalent deterministic certificate. The
shortest validated suggestion may be a pipeline containing
`normalize_category` and `simp_explicit` phases. -/
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
        -- A certificate is a replacement proof program, not a promise to
        -- preserve the simplifier's internal expression representation.
        return ← isDefEq searchedResult.expr replayedResult.expr
  catch _ =>
    return false

private def replayEncoding? (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) : TacticM (Option Bool) := do
  if ← canReplay target recorded searchedResult (withPositions := false) then
    return some false
  if ← canReplay target recorded searchedResult (withPositions := true) then
    return some true
  return none

/-- Replay a recorded prefix, preferring a position-free encoding. The result
is the complete target after that prefix and whether absolute positions were
needed. -/
private def replayRecorded? (target : Expr)
    (recorded : Array RecordedEvent) : TacticM (Option (Simp.Result × Bool)) := do
  for withPositions in #[false, true] do
    try
      let count := certificateEventCount recorded
      let mut events := #[]
      for index in *...count do
        let some event := recorded[index]? | return none
        events := events.push (← recordedReplayEvent event withPositions)
      let (result, state) ← runReplay target events
      if state.next == events.size then
        return some (result, withPositions)
    catch _ =>
      pure ()
  return none

private def joinCertificatePhases (phases : Array String) : String :=
  String.intercalate "\n" phases.toList

/-- Keep automatic compression bounded on very large simplifier traces. -/
private def maxMixedPrefixEvents : Nat := 64

/-- Two phases discover `normalize; exact; normalize` programs while keeping
the certificate search small. -/
private def maxMixedNormalizerPhases : Nat := 2

private def maxMixedSearchStates : Nat := 256

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
  let runAndRecord := fun (input : Expr) => do
    let ref ← IO.mkRef ({} : RecorderState)
    let result ← dischargeWrapper.with fun discharge? => do
      let methods := recordingMethods ref simprocs discharge?
      withOptions (·.setBool `diagnostics true) do
        return (← Simp.mainCore input ctx (methods := methods)).1
    return (result, ← ref.get)
  let (result, state) ← runAndRecord target
  let some flatWithPositions ← replayEncoding? target state.events result
    | throwErrorAt reportStx "simp_explicit recorder cannot encode this simplification as a deterministic replay"
  let flatSuggestion ← certificateText state.events (withPositions := flatWithPositions)
  let mut suggestion := flatSuggestion

  -- Search a bounded certificate-program graph breadth first. A node is the
  -- current target plus the phases that produced it. Its outgoing edges replay
  -- an exact prefix and then normalize. Recording afresh at every node is
  -- essential: normalization can expose a different exact suffix.
  let mut frontier : Array (Expr × Array String) := #[(target, #[])]
  let mut stateCount := 1
  for depth in *...(maxMixedNormalizerPhases + 1) do
    let mut nextFrontier := #[]
    for (input, previousPhases) in frontier do
      let (nodeResult, nodeState) ← runAndRecord input
      let closes ← isReflexiveResult nodeResult.expr
      let reachesResult ← if closes then pure true else if result.expr.isTrue then
        pure false
      else
        isDefEq nodeResult.expr result.expr
      if reachesResult then
        if let some withPositions ← replayEncoding? input nodeState.events nodeResult then
          let mut phases := previousPhases
          if certificateEventCount nodeState.events > 0 then
            phases := phases.push
              (← certificateText nodeState.events (withPositions := withPositions))
          let candidate := joinCertificatePhases phases
          if !candidate.isEmpty && candidate.utf8ByteSize < suggestion.utf8ByteSize then
            suggestion := candidate

      if depth < maxMixedNormalizerPhases then
        let eventCount := certificateEventCount nodeState.events
        let prefixLimit := min eventCount maxMixedPrefixEvents
        for prefixCount in *...(prefixLimit + 1) do
          let transition? ← try
            withoutModifyingState do
              let prefixEvents := nodeState.events.extract 0 prefixCount
              let some (prefixResult, prefixWithPositions) ← replayRecorded? input prefixEvents
                | return none
              -- A replay phase would close the goal before the normalizer ran.
              if prefixCount > 0 && (← isReflexiveResult prefixResult.expr) then
                return none
              let normalized ← Normalize.categoryTarget mvarId prefixResult.expr
              if Expr.equal prefixResult.expr normalized.expr then
                return none
              let mut phases := previousPhases
              if prefixCount > 0 then
                phases := phases.push
                  (← certificateText prefixEvents (withPositions := prefixWithPositions))
              phases := phases.push "normalize_category"
              return some (normalized.expr, phases, ← isReflexiveResult normalized.expr)
          catch _ =>
            pure none
          if let some (normalized, phases, closes) := transition? then
            let phaseText := joinCertificatePhases phases
            if closes then
              if phaseText.utf8ByteSize < suggestion.utf8ByteSize then
                suggestion := phaseText
            else if stateCount < maxMixedSearchStates &&
                phaseText.utf8ByteSize < suggestion.utf8ByteSize then
              nextFrontier := nextFrontier.push (normalized, phases)
              stateCount := stateCount + 1
    frontier := nextFrontier
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
