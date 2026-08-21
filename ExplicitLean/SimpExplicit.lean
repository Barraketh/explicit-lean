module

public import ExplicitLean.Normalize
public meta import ExplicitLean.Normalize
public meta import ExplicitLean.ProofExport
public meta import Lean.Elab.Tactic.Simp
public import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Data.Json
public meta import Lean.Meta.Tactic.Refl

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

syntax simpExplicitPre := "↓"
syntax simpExplicitPost := "↑"
syntax simpExplicitRule := (simpExplicitPre <|> simpExplicitPost)? "← "? term
syntax simpExplicitEvent := (num " => ")? simpExplicitRule
syntax simpExplicitTraceArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?

/-- Replay an ordered simplifier certificate without consulting the simp set. -/
syntax (name := simpExplicit) "simp_explicit" " [" simpExplicitEvent,* "]" : tactic
/-- Run `simp` once and report an equivalent deterministic certificate. The
shortest validated suggestion may be a pipeline containing
`normalize_category` and `simp_explicit` phases. -/
syntax (name := simpExplicitTrace) "simp_explicit?" simpExplicitTraceArgs : tactic

end Lean.Parser.Tactic

namespace ExplicitLean

namespace SimpExplicit

register_option explicitLean.simpExplicit.report : Bool := {
  defValue := false
  descr := "emit one machine-readable report for each successful simp_explicit? recording"
}

/- The passive recorder is deliberately controlled by options rather than a
  second tactic.  This lets the coverage driver replace every source
  occurrence in one copied module while the wrapped tactic remains the
  original `simp` when recording is not possible. -/
register_option explicitLean.simpExplicit.passive : Bool := {
  defValue := false
  descr := "record simp traces without changing the wrapped tactic's behavior"
}

register_option explicitLean.simpExplicit.occurrenceId : String := {
  defValue := ""
  descr := "stable source identity supplied by the passive simp recorder"
}

def reportSchema : String := "explicitLean.simpRecording"
def reportSchemaVersion : Nat := 2

structure ExprFingerprint where
  /-- A bounded diagnostic rendering for humans.  This is never used for replay. -/
  printable : String
  /-- A canonical, alpha-stable expression fingerprint. -/
  fingerprint : String
  deriving ToJson

structure LocalFingerprint where
  index : Nat
  kind : String
  type : ExprFingerprint
  value : Option ExprFingerprint
  deriving ToJson

structure StateFingerprint where
  target : ExprFingerprint
  context : Array LocalFingerprint
  deriving ToJson

structure ValidationEnvelope where
  schemaVersion : Nat
  certificate : Option Nat
  initialState : StateFingerprint
  finalState : StateFingerprint
  deriving ToJson

structure OriginCandidate where
  kind : String
  name : String
  inverse : Bool
  source : Option String
  deriving ToJson

structure PremiseReport where
  proposition : ExprFingerprint
  proof : ExprFingerprint
  deriving ToJson

structure SemanticEventReport where
  tick : Nat
  phase : String
  input : ExprFingerprint
  step : String
  result : ExprFingerprint
  proof : Option ExprFingerprint
  origins : Array OriginCandidate
  premises : Array PremiseReport
  /-- `named_rule` for a compact origin replay, `generated_proof` for the
      authoritative result-proof fallback. -/
  encodingKind : Option String
  /-- Why a generated proof binding was needed, when applicable. -/
  encodingReason : Option String
  deriving ToJson

structure EncodingMetrics where
  mode : String := "event"
  namedRuleEvents : Nat := 0
  generatedProofEvents : Nat := 0
  generatedSimprocEvents : Nat := 0
  generatedSpecialEvents : Nat := 0
  wholeResultProofCount : Nat := 0
  generatedBindingCount : Nat := 0
  generatedBindingBytes : Nat := 0
  totalCertificateBytes : Nat := 0
  deriving ToJson

/- A proof-result encoder is intentionally the only public surface needed by
   other tactic producers.  The recorder's semantic event and replay state
   remain private; callers receive the validated source and its compact
   encoding diagnostics. -/
structure ProofResultEncoding where
  source : String
  metrics : EncodingMetrics
  encodingKind : String
  encodingReason : Option String

structure ExecutionReport where
  executionIndex : Nat
  result : String
  /-- `none` means that enclosing combinator instrumentation has not established
      commitment. Package F may replace this with `committed` or `backtracked`. -/
  disposition : Option String
  trace : Array SemanticEventReport
  initialState : StateFingerprint
  finalState : StateFingerprint
  failureCategory : Option String
  failureMessage : Option String
  deriving ToJson

structure RecordingReport where
  schema : String
  schemaVersion : Nat
  kind : String
  occurrenceId : String
  declaration : String
  originalSyntax : String
  closesGoal : Bool
  traceLength : Nat
  certificateEventCount : Nat
  positionsNeeded : Bool
  certificateBytes : Nat
  certificate : String
  executions : Array ExecutionReport
  terminalOutcome : Option String
  failureCategory : Option String
  failureMessage : Option String
  traceAvailable : Bool
  encodingStatus : String
  recordingReason : Option String
  encoding : EncodingMetrics
  encodingFallbackReason : Option String
  validation : Option ValidationEnvelope
  deriving ToJson

inductive Phase where
  | pre
  | post
  deriving BEq, Repr

private structure RecordedPremise where
  proposition : Expr
  proof : Expr

private structure RecordedEvent where
  tick : Nat
  phase : Phase
  input : Expr
  step : Simp.Step
  result : Simp.Result
  origins : Array Origin
  premises : Array RecordedPremise

private structure EventEncodingInfo where
  kind : String
  reason : Option String

private structure RecorderState where
  tick : Nat := 0
  /-- Number of reentrant simplifier methods currently executing. Nested
      calls contribute ticks and diagnostics to their enclosing method, but
      are not independent semantic replay events. -/
  activeDepth : Nat := 0
  events : Array RecordedEvent := #[]
  premises : Array RecordedPremise := #[]

private def stepResult? : Simp.Step → Option Simp.Result
  | .done result | .visit result => some result
  | .continue result? => result?

private def changedResult? (input : Expr) : Simp.Step → Option Simp.Result
  | step => stepResult? step |>.bind fun result =>
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
  let depth := state.activeDepth
  ref.set { state with tick, activeDepth := depth + 1 }
  let premiseStart := state.premises.size
  let before := (← get).diag
  let step ← try
    method input
  finally
    let state ← ref.get
    ref.set { state with activeDepth := state.activeDepth - 1 }
  let after := (← get).diag
  if depth == 0 then
    if let some result := changedResult? input step then
      let state ← ref.get
      let premises := state.premises.extract premiseStart state.premises.size
      ref.set {
        state with
          events := state.events.push {
            tick
            phase
            input
            step
            result
            origins := changedOrigins before after
            premises
          }
      }
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
      let result? ← methods.discharge? proposition
      if let some proof := result? then
        let state ← ref.get
        ref.set { state with premises := state.premises.push { proposition, proof } }
      return result? }

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
        if event.origins.size == 1 && isReflexiveClosure event.origins[0]! then
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
    let some origin := event.origins[0]?
      | throwError "simp_explicit cannot encode semantic event {index}: no diagnostic origin candidate"
    unless event.origins.size == 1 do
      throwError "simp_explicit cannot encode semantic event {index}: observed {event.origins.size} diagnostic origin candidates"
    let rule ← ruleText origin
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

private structure GeneratedBinding where
  name : Name
  type : Expr
  proof : Expr
  typeText : String
  proofText : String
  bytes : Nat

private structure EncodedEvent where
  event : RecordedEvent
  replay : ReplayEvent
  info : EventEncodingInfo
  ruleText : String
  binding? : Option GeneratedBinding

private structure CertificatePlan where
  events : Array EncodedEvent
  bindings : Array GeneratedBinding
  positions : Bool
  source : String
  metrics : EncodingMetrics

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
  let some origin := event.origins[0]?
    | throwError "simp_explicit cannot replay a semantic event without a named origin"
  unless event.origins.size == 1 do
    throwError "simp_explicit cannot replay a semantic event with {event.origins.size} origin candidates"
  let (rules, source) ← match origin with
    | .decl name _ inverse =>
        if (← Simp.isBuiltinSimproc name) || (← Simp.isSimproc name) then
          throwError "simp_explicit cannot yet encode simproc '{name}'"
        pure (← mkSimpTheoremFromConst name (post := post) (inv := inverse), (mkIdent name).raw)
    | .fvar fvarId =>
        let localDecl ← fvarId.getDecl
        let rules ← mkSimpTheoremFromExpr origin #[] (mkFVar fvarId) (post := post)
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

private def freshBindingName (eventIndex : Nat) (used : Array Name) : MetaM Name := do
  let lctx ← getLCtx
  let mut suffix := 0
  while true do
    let base := s!"h_explicit_{eventIndex + 1}"
    let candidate := Name.mkSimple (if suffix == 0 then base else s!"{base}_{suffix}")
    if (lctx.findFromUserName? candidate).isNone && !used.contains candidate then
      return candidate
    suffix := suffix + 1
  throwError "unreachable generated binding name search"

private def fallbackReason (event : RecordedEvent) : TacticM String := do
  if event.origins.isEmpty then
    return "no_origin"
  let mut hasSimproc := false
  let mut hasSpecial := false
  for origin in event.origins do
    match origin with
    | .decl name _ _ =>
        if (← Simp.isBuiltinSimproc name) || (← Simp.isSimproc name) then
          hasSimproc := true
    | .other _ => hasSpecial := true
    | _ => pure ()
  if hasSimproc then
    return "simproc"
  if hasSpecial then
    return "special_rule"
  if event.origins.size > 1 then
    return "multiple_origins"
  match event.origins[0]! with
  | .fvar fvarId =>
      if (← fvarId.getDecl).userName.isInaccessibleUserName then
        return "unprintable_local_fact"
  | _ => pure ()
  return "unvalidated_named_rule"

private def compactReplayEvent? (event : RecordedEvent) : TacticM (Option ReplayEvent) := do
  if event.origins.size != 1 then
    return none
  try
    let replay ← recordedReplayEvent event (withPosition := false)
    let (result, state) ← runReplay event.input #[replay]
    if state.next == 1 && (← isDefEq result.expr event.result.expr) then
      return some replay
  catch _ => pure ()
  return none

private def isReflexiveResultEarly (expr : Expr) : MetaM Bool := do
  if expr.isTrue then
    return true
  if expr.isAppOfArity ``Eq 3 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  if expr.isAppOfArity ``Iff 2 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  return false

private def generatedProofBinding (input : Expr) (result : Simp.Result)
    (eventIndex : Nat) (phase : Phase) (tick? : Option Nat)
    (usedNames : Array Name) : TacticM (GeneratedBinding × ReplayEvent) := do
  let relation ← mkEq input result.expr
  let proof ← Simp.Result.getProof' input result
  let proof ← mkExpectedTypeHint proof relation
  let proofType ← inferType proof
  unless ← isDefEq proofType relation do
    throwError "simp_explicit generated proof did not check against its recorded equality"
  let name ← freshBindingName eventIndex usedNames
  let sourceNamespace := ((← Term.getDeclName?).map (·.getPrefix)).getD Name.anonymous
  let rendered ← ProofExport.render proof (type? := some relation) (config := {
    sourceNamespace
  })
  let binding : GeneratedBinding := {
    name
    type := relation
    proof
    typeText := rendered.typeText
    proofText := rendered.valueText
    bytes := rendered.typeText.utf8ByteSize + rendered.valueText.utf8ByteSize
  }
  let rules ← mkSimpTheoremFromExpr (.other name) #[] proof
    (post := phase == .post)
  let replay : ReplayEvent := {
    tick?
    phase
    rules
    source := (mkIdent name).raw
  }
  return (binding, replay)

private def generatedBinding (event : RecordedEvent) (eventIndex : Nat)
    (usedNames : Array Name) (withPosition : Bool) : TacticM (GeneratedBinding × ReplayEvent) :=
  generatedProofBinding event.input event.result eventIndex event.phase
    (if withPosition then some event.tick else none) usedNames

private def indentSource (indent : String) (text : String) : String :=
  text.replace "\n" ("\n" ++ indent)

private def certificatePlanText (events : Array EncodedEvent)
    (bindings : Array GeneratedBinding) (withPositions : Bool) : String :=
  Id.run do
    let mut lines := #[]
    for binding in bindings do
      lines := lines.push s!"have {binding.name} : {indentSource "  " binding.typeText} :="
      lines := lines.push s!"  {indentSource "  " binding.proofText}"
    if events.isEmpty then
      if lines.isEmpty then
        return "simp_explicit []"
      lines := lines.push "simp_explicit []"
      return String.intercalate "\n" lines.toList
    lines := lines.push "simp_explicit ["
    for index in *...events.size do
      let some event := events[index]? | continue
      let comma := if index + 1 < events.size then "," else ""
      let phase := if event.event.phase == .pre then "↓ " else ""
      let position := if withPositions then s!"{event.event.tick} => " else ""
      lines := lines.push s!"  {position}{phase}{event.ruleText}{comma}"
    lines := lines.push "]"
    return String.intercalate "\n" lines.toList

private def wholeResultPlanText (binding : GeneratedBinding) : String :=
  let declaration :=
    s!"have {binding.name} : {indentSource "  " binding.typeText} :="
  let proof := s!"  {indentSource "  " binding.proofText}"
  let replay := s!"simp_explicit [↓ {binding.name}]"
  String.intercalate "\n" [declaration, proof, replay]

private def buildCertificatePlan? (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) (withPositions : Bool) : TacticM (Option CertificatePlan) := do
  try
    -- Keep the trailing reflexive closure in generated plans: unlike the
    -- compact certificate count, materialized proof bodies need the explicit
    -- closure to finish the rewritten target.
    let count := recorded.size
    let mut encoded := #[]
    let mut bindings := #[]
    let mut usedNames := #[]
    for index in *...count do
      let some event := recorded[index]? | return none
      if let some replay ← compactReplayEvent? event then
        let rule ← ruleText event.origins[0]!
        encoded := encoded.push {
          event
          replay := if withPositions then { replay with tick? := some event.tick } else replay
          info := { kind := "named_rule", reason := none }
          ruleText := rule
          binding? := none
        }
      else
        let reason ← fallbackReason event
        let (binding, replay) ← generatedBinding event index usedNames withPositions
        usedNames := usedNames.push binding.name
        bindings := bindings.push binding
        encoded := encoded.push {
          event
          replay
          info := { kind := "generated_proof", reason := some reason }
          ruleText := binding.name.toString
          binding? := some binding
        }
    let replayEvents := encoded.map (·.replay)
    let (replayedResult, replayState) ← runReplay target replayEvents
    unless replayState.next == replayEvents.size do
      return none
    let reachesResult ← if searchedResult.expr.isTrue then
      isReflexiveResultEarly replayedResult.expr
    else
      isDefEq searchedResult.expr replayedResult.expr
    unless reachesResult do
      return none
    let source := certificatePlanText encoded bindings withPositions
    let namedRuleEvents := encoded.foldl (fun n event =>
      if event.info.kind == "named_rule" then n + 1 else n) 0
    let generatedProofEvents := encoded.foldl (fun n event =>
      if event.info.kind == "generated_proof" then n + 1 else n) 0
    let generatedSimprocEvents := encoded.foldl (fun n event =>
      if event.info.reason == some "simproc" then n + 1 else n) 0
    let generatedSpecialEvents := encoded.foldl (fun n event =>
      if event.info.reason == some "special_rule" then n + 1 else n) 0
    let generatedBindingBytes := bindings.foldl (fun n binding => n + binding.bytes) 0
    return some {
      events := encoded
      bindings
      positions := withPositions
      source
      metrics := {
        namedRuleEvents
        generatedProofEvents
        generatedSimprocEvents
        generatedSpecialEvents
        generatedBindingCount := bindings.size
        generatedBindingBytes
        totalCertificateBytes := source.utf8ByteSize
      }
    }
  catch _ =>
    return none

/-- Encode one semantic simp result using the same event fallback and closed
    replay validation used by `simp_explicit?`.  `origins` is diagnostic input
    only; the resulting source never invokes ambient simp or simproc search. -/
def encodeProofResult (input : Expr) (result : Simp.Result)
    (origins : Array Origin) (phase : Phase) : TacticM ProofResultEncoding := do
  let event : RecordedEvent := {
    tick := 1
    phase
    input
    step := .done result
    result
    origins
    premises := #[]
  }
  let some plan ← buildCertificatePlan? input #[event] result (withPositions := false)
    | throwError "proof-result encoder could not validate an event replay"
  let some encoded := plan.events[0]?
    | throwError "proof-result encoder produced no event encoding"
  return {
    source := plan.source
    metrics := plan.metrics
    encodingKind := encoded.info.kind
    encodingReason := encoded.info.reason
  }

private def buildWholeResultPlan? (target : Expr) (searchedResult : Simp.Result) :
    TacticM (Option CertificatePlan) := do
  try
    let (binding, replay) ← generatedProofBinding target searchedResult 0 .pre none #[]
    let (replayedResult, replayState) ← runReplay target #[replay]
    unless replayState.next == 1 do
      return none
    let reachesResult ← if searchedResult.expr.isTrue then
      isReflexiveResultEarly replayedResult.expr
    else
      isDefEq searchedResult.expr replayedResult.expr
    unless reachesResult do
      return none
    let source := wholeResultPlanText binding
    return some {
      events := #[]
      bindings := #[binding]
      positions := false
      source
      metrics := {
        mode := "whole_result_proof"
        wholeResultProofCount := 1
        generatedBindingCount := 1
        generatedBindingBytes := binding.bytes
        totalCertificateBytes := source.utf8ByteSize
      }
    }
  catch _ =>
    return none

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

/- Persistent reports must not depend on pointer identities, `FVarId`s, raw
   `Expr`s, or position-bearing `Syntax`.  The canonical form below uses
   context-order indices for free variables and ignores binder names and
   annotation metadata, so alpha-renamed expressions receive the same
   fingerprint.  The pretty-printed field is intentionally kept separate as
   a diagnostic aid. -/
private structure CanonicalState where
  exprMVars : Std.HashMap MVarId Nat := {}
  levelMVars : Std.HashMap LMVarId Nat := {}
  nextExprMVar : Nat := 0
  nextLevelMVar : Nat := 0

private abbrev CanonicalM := StateM CanonicalState

private def canonicalLevel : Level → CanonicalM String
  | .zero => pure "0"
  | .succ level => return s!"(succ {← canonicalLevel level})"
  | .max lhs rhs => return s!"(max {← canonicalLevel lhs} {← canonicalLevel rhs})"
  | .imax lhs rhs => return s!"(imax {← canonicalLevel lhs} {← canonicalLevel rhs})"
  | .param name => pure s!"(param {name})"
  | .mvar mvarId => do
      let state ← get
      if let some ordinal := state.levelMVars.get? mvarId then
        return s!"(level-mvar {ordinal})"
      modify fun _ => { state with
        levelMVars := state.levelMVars.insert mvarId state.nextLevelMVar
        nextLevelMVar := state.nextLevelMVar + 1 }
      return s!"(level-mvar {state.nextLevelMVar})"

private def canonicalBinderInfo : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private partial def canonicalExpr (lctx : LocalContext) : Expr → CanonicalM String
  | .bvar index => pure s!"b{index}"
  | .fvar fvarId =>
      match lctx.find? fvarId with
      | some decl => pure s!"f{decl.index}"
      | none => pure "f?"
  | .mvar mvarId => do
      let state ← get
      if let some ordinal := state.exprMVars.get? mvarId then
        return s!"(mvar {ordinal})"
      modify fun _ => { state with
        exprMVars := state.exprMVars.insert mvarId state.nextExprMVar
        nextExprMVar := state.nextExprMVar + 1 }
      return s!"(mvar {state.nextExprMVar})"
  | .sort level => return s!"(sort {← canonicalLevel level})"
  | .const name levels =>
      return s!"(const {name} [{String.intercalate "," (← levels.mapM canonicalLevel)}])"
  | .app fn arg => return s!"(app {← canonicalExpr lctx fn} {← canonicalExpr lctx arg})"
  | .lam _ type body binderInfo =>
      return s!"(lam {← canonicalExpr lctx type} {← canonicalExpr lctx body} {canonicalBinderInfo binderInfo})"
  | .forallE _ type body binderInfo =>
      return s!"(forall {← canonicalExpr lctx type} {← canonicalExpr lctx body} {canonicalBinderInfo binderInfo})"
  | .letE _ type value body nondep =>
      return s!"(let {← canonicalExpr lctx type} {← canonicalExpr lctx value} {← canonicalExpr lctx body} {nondep})"
  | .lit literal => pure s!"(lit {repr literal})"
  | .mdata _ expression => canonicalExpr lctx expression
  | .proj name index expression =>
      return s!"(proj {name} {index} {← canonicalExpr lctx expression})"

private def exprFingerprint (expression : Expr) : MetaM ExprFingerprint := do
  let expression ← instantiateMVars expression
  let printable ← withOptions (pp.mvars.set · false |>.set pp.mvars.levels.name false) <| ppExpr expression
  let printable := toString printable
  let printable := if printable.length > 512 then (printable.take 512).toString ++ "…" else printable
  let (canonical, _) := (canonicalExpr (← getLCtx) expression).run {}
  return {
    printable
    fingerprint := s!"expr-v1:{hash canonical}"
  }

private def stateFingerprint (target : Expr) : MetaM StateFingerprint := do
  let mut context := #[]
  let lctx ← getLCtx
  for fvarId in lctx.getFVarIds do
    let decl ← fvarId.getDecl
    let (kind, value?) := match decl with
      | .cdecl .. => ("cdecl", none)
      | .ldecl _ _ _ _ value _ _ => ("ldecl", some value)
    context := context.push {
      index := decl.index
      kind
      type := ← exprFingerprint decl.type
      value := ← value?.mapM exprFingerprint
    }
  return { target := ← exprFingerprint target, context }

private def stepName : Simp.Step → String
  | .done _ => "done"
  | .visit _ => "visit"
  | .continue none => "continue"
  | .continue (some _) => "continue_with_result"

private def originCandidate (origin : Origin) : MetaM OriginCandidate := do
  match origin with
  | .decl name _ inverse =>
      return { kind := "decl", name := name.toString, inverse, source := none }
  | .fvar fvarId =>
      let decl ← fvarId.getDecl
      return {
        kind := "fvar"
        name := decl.userName.toString
        inverse := false
        source := none
      }
  | .stx _ ref =>
      let inverse := !ref[1].isNone
      return {
        kind := "syntax"
        name := "syntax"
        inverse
        source := some (toString ref.prettyPrint)
      }
  | .other name =>
      return { kind := "other", name := name.toString, inverse := false, source := none }

private def semanticEventReport (event : RecordedEvent)
    (encoding? : Option EventEncodingInfo := none) : MetaM SemanticEventReport := do
  let origins ← event.origins.mapM originCandidate
  let premises ← event.premises.mapM fun premise => do
    return {
      proposition := ← exprFingerprint premise.proposition
      proof := ← exprFingerprint premise.proof
    }
  return {
    tick := event.tick
    phase := if event.phase == .pre then "pre" else "post"
    input := ← exprFingerprint event.input
    step := stepName event.step
    result := ← exprFingerprint event.result.expr
    proof := ← event.result.proof?.mapM exprFingerprint
    origins
    premises
    encodingKind := encoding?.map (·.kind)
    encodingReason := encoding?.bind (·.reason)
  }

private def executionReport (target : Expr) (result : Simp.Result)
    (state : RecorderState) (executionIndex : Nat) (failureCategory? : Option String)
    (failureMessage? : Option String := none)
    (encodings : Array EventEncodingInfo := #[])
    : MetaM ExecutionReport := do
  return {
    executionIndex
    result := "succeeded"
    disposition := none
    trace := ← state.events.mapIdxM fun index event =>
      semanticEventReport event encodings[index]?
    initialState := ← stateFingerprint target
    finalState := ← stateFingerprint result.expr
    failureCategory := failureCategory?
    failureMessage := failureMessage?
  }

private def exceptionText (ex : Exception) : TacticM String := do
  liftM (m := BaseIO) ex.toMessageData.toString

private def emitRecordingReport (simpStx reportStx : Syntax) (target : Expr) (state : RecorderState)
    (result? : Option Simp.Result) (suggestion : String) (positionsNeeded : Bool)
    (failureCategory? : Option String) (failureMessage? : Option String)
    (terminalOutcome? : Option String) (traceAvailable := true)
    (encodingStatus := "validated") (recordingReason? : Option String := none)
    (encodings : Array EventEncodingInfo := #[])
    (encodingMetrics : EncodingMetrics := {})
    (encodingFallbackReason? : Option String := none) : TacticM Unit := do
  let declaration := (← Term.getDeclName?).map (·.toString) |>.getD "<unknown>"
  let originalSyntax := toString simpStx.prettyPrint
  let occurrenceId := explicitLean.simpExplicit.occurrenceId.get (← getOptions)
  let (closesGoal, finalTarget, executions) ← match result? with
    | some result =>
        let closesGoal ← isReflexiveResult result.expr
        let execution ← executionReport target result state 0 failureCategory? failureMessage? encodings
        pure (closesGoal, result.expr, #[execution])
    | none =>
        let finalTarget ← try
          instantiateMVars (← (← getMainGoal).getType)
        catch _ => pure target
        let execution : ExecutionReport := {
          executionIndex := 0
          result := "failed"
          disposition := none
          trace := #[]
          initialState := ← stateFingerprint target
          finalState := ← stateFingerprint finalTarget
          failureCategory := failureCategory?
          failureMessage := failureMessage?
        }
        pure (false, finalTarget, #[execution])
  let initialState ← stateFingerprint target
  let finalState ← stateFingerprint finalTarget
  let report : RecordingReport := {
    schema := reportSchema
    schemaVersion := reportSchemaVersion
    kind := "simp_explicit.recording"
    occurrenceId
    declaration
    originalSyntax
    closesGoal
    traceLength := state.events.size
    certificateEventCount := certificateEventCount state.events
    positionsNeeded
    certificateBytes := suggestion.utf8ByteSize
    certificate := suggestion
    executions
    terminalOutcome := terminalOutcome?
    failureCategory := failureCategory?
    failureMessage := failureMessage?
    traceAvailable
    encodingStatus
    recordingReason := recordingReason?
    encoding := { encodingMetrics with totalCertificateBytes := suggestion.utf8ByteSize }
    encodingFallbackReason := encodingFallbackReason?
    validation := some {
      schemaVersion := reportSchemaVersion
      certificate := if suggestion.isEmpty then none else some 0
      initialState
      finalState
    }
  }
  logInfoAt reportStx m!"EXPLICIT_LEAN_SIMP_REPORT {(toJson report).compress}"

private def passiveOriginalSimp (simpStx reportStx : Syntax) (target : Expr)
    (category : String) (detail : String) : TacticM Unit := do
  let state : RecorderState := {}
  try
    evalSimp simpStx
  catch ex =>
    let failureDetail ← exceptionText ex
    try
      emitRecordingReport simpStx reportStx target state none "" false
        (some "original_failure") (some failureDetail) none false "unavailable"
        (some failureDetail)
    catch _ => pure ()
    throw ex
  let finalTarget ← try
    instantiateMVars (← (← getMainGoal).getType)
  catch _ =>
    pure (mkConst ``True)
  let result : Simp.Result := { expr := finalTarget }
  try
    emitRecordingReport simpStx reportStx target state (some result) "" false
      (some category) (some detail) none false "unavailable" (some detail)
  catch ex =>
    logWarningAt reportStx m!"passive simp recording report failed: {← exceptionText ex}"

private def packageCPremiseEvent (event : RecordedEvent) : Bool :=
  if event.premises.isEmpty || event.origins.size != 1 then
    false
  else
    match event.origins[0]! with
    | .decl .. => true
    | _ => false

private def namedEncodingInfos (events : Array RecordedEvent) : Array EventEncodingInfo := Id.run do
  let count := certificateEventCount events
  let mut result := #[]
  for _ in *...count do
    result := result.push { kind := "named_rule", reason := none }
  return result

private def planEncodingInfos (plan : CertificatePlan) : Array EventEncodingInfo :=
  plan.events.map (·.info)

private def recordSimp (simpStx reportStx : Syntax) : TacticM Unit := withMainContext do
  unless simpStx.getKind == ``Lean.Parser.Tactic.simp do
    throwErrorAt simpStx "simp_explicit? currently accepts one `simp` tactic"
  let mvarId ← getMainGoal
  let target ← instantiateMVars (← mvarId.getType)
  let passive := explicitLean.simpExplicit.passive.get (← getOptions)
  if !simpStx[5].isNone then
    if passive then
      return ← passiveOriginalSimp simpStx reportStx target "context" "passive target recorder does not yet encode locations"
    else
      throwErrorAt simpStx "simp_explicit? currently supports the target only"
  if !simpStx[1][0].isNone then
    if passive then
      return ← passiveOriginalSimp simpStx reportStx target "recording" "passive recorder preserves nondefault simp configuration through the original tactic"
    else
      throwErrorAt simpStx[1] "simp_explicit? does not yet encode nondefault simp configuration"
  if !simpStx[2].isNone then
    if passive then
      return ← passiveOriginalSimp simpStx reportStx target "premise" "passive recorder preserves custom dischargers through the original tactic"
    else
      throwErrorAt simpStx[2] "simp_explicit? does not yet encode a custom discharger"
  let context? ← try
    some <$> mkSimpContext simpStx (eraseLocal := false)
  catch ex =>
    if passive then
      let detail ← exceptionText ex
      return ← passiveOriginalSimp simpStx reportStx target "recording" detail
    else
      throw ex
  let some { ctx, simprocs, dischargeWrapper, .. } := context?
    | throwError "simp_explicit recorder failed to construct a simp context"
  let runAndRecord := fun (input : Expr) => do
    let ref ← IO.mkRef ({} : RecorderState)
    let result ← dischargeWrapper.with fun discharge? => do
      let methods := recordingMethods ref simprocs discharge?
      withOptions (·.setBool `diagnostics true) do
        return (← Simp.mainCore input ctx (methods := methods)).1
    return (result, ← ref.get)
  let recording? ← try
    some <$> runAndRecord target
  catch ex =>
    if passive then
      let detail ← exceptionText ex
      return ← passiveOriginalSimp simpStx reportStx target "recording" detail
    else
      throw ex
  let some (result, state) := recording?
    | throwError "simp_explicit recorder did not return a simplifier result"
  let flatEncoding? ← replayEncoding? target state.events result
  let mut suggestion := ""
  let mut encodingInfos : Array EventEncodingInfo := #[]
  let mut encodingMetrics : EncodingMetrics := {}
  let mut encodingFallbackReason? : Option String := none
  let mut positionsNeeded := flatEncoding?.getD false
  if let some flatWithPositions := flatEncoding? then
    suggestion := ← certificateText state.events (withPositions := flatWithPositions)
    encodingInfos := namedEncodingInfos state.events
    encodingMetrics := {
      namedRuleEvents := encodingInfos.size
    }
  else
    if state.events.any packageCPremiseEvent then
      if passive then
        return ← passiveOriginalSimp simpStx reportStx target "premise"
          "cannot yet encode a discharged side condition"
      else
        throwErrorAt reportStx "simp_explicit cannot yet encode a discharged side condition"
    let plan? ← buildCertificatePlan? target state.events result (withPositions := false)
    let plan? ← if plan?.isSome then
      pure plan?
    else
      buildCertificatePlan? target state.events result (withPositions := true)
    let plan? ← match plan? with
      | some plan => pure (some plan)
      | none => buildWholeResultPlan? target result
    match plan? with
    | none =>
        if passive then
          return ← passiveOriginalSimp simpStx reportStx target "recording"
            "proof-result fallback could not be validated"
        else
          throwErrorAt reportStx "simp_explicit recorder cannot encode this simplification as a deterministic replay"
    | some plan =>
        suggestion := plan.source
        encodingInfos := planEncodingInfos plan
        encodingMetrics := plan.metrics
        encodingFallbackReason? :=
          if plan.metrics.mode == "whole_result_proof" then some "presentation_gap" else none
        positionsNeeded := plan.positions

  -- Search a bounded certificate-program graph breadth first. A node is the
  -- current target plus the phases that produced it. Its outgoing edges replay
  -- an exact prefix and then normalize. Recording afresh at every node is
  -- essential: normalization can expose a different exact suffix.
  if flatEncoding?.isSome then
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
            if !candidate.isEmpty &&
                (suggestion.isEmpty || candidate.utf8ByteSize < suggestion.utf8ByteSize) then
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
                if suggestion.isEmpty || phaseText.utf8ByteSize < suggestion.utf8ByteSize then
                  suggestion := phaseText
              else if stateCount < maxMixedSearchStates &&
                  (suggestion.isEmpty || phaseText.utf8ByteSize < suggestion.utf8ByteSize) then
                nextFrontier := nextFrontier.push (normalized, phases)
                stateCount := stateCount + 1
      frontier := nextFrontier
  let shouldReport := passive || explicitLean.simpExplicit.report.get (← getOptions)
  if shouldReport then
    -- Recording cannot assign a terminal outcome: `materialized` requires the
    -- coverage driver to compile the replacement in its complete body.
    let failureCategory? : Option String := none
    let terminalOutcome? : Option String := none
    let encodingStatus := if suggestion.isEmpty then "unavailable" else "validated"
    let recordingReason? := if suggestion.isEmpty then some "compact certificate encoding was not validated" else none
    if passive then
      try
        emitRecordingReport simpStx reportStx target state (some result) suggestion
          positionsNeeded failureCategory? none none
          (traceAvailable := true) (encodingStatus := encodingStatus)
          (recordingReason? := recordingReason?) (encodings := encodingInfos)
          (encodingMetrics := encodingMetrics)
          (encodingFallbackReason? := encodingFallbackReason?)
      catch ex =>
        logWarningAt reportStx m!"passive simp recording report failed: {← exceptionText ex}"
    else
      emitRecordingReport simpStx reportStx target state (some result) suggestion
        positionsNeeded failureCategory? none none
        (traceAvailable := true) (encodingStatus := encodingStatus)
        (recordingReason? := recordingReason?) (encodings := encodingInfos)
        (encodingMetrics := encodingMetrics)
        (encodingFallbackReason? := encodingFallbackReason?)
  unless passive do
    logInfoAt reportStx m!"Try this deterministic replay:\n{suggestion}"
  applyResultToTarget mvarId target result

end SimpExplicit

open SimpExplicit

elab_rules : tactic
  | `(tactic| simp_explicit? $args:simpExplicitTraceArgs) => do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordSimp inner (← getRef)
  | `(tactic| simp_explicit [$events:simpExplicitEvent,*]) =>
      replaySimp (events.getElems.map (·.raw))

end ExplicitLean
