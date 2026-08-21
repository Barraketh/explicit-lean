module

public import ExplicitLean.Normalize
public meta import ExplicitLean.Normalize
public meta import ExplicitLean.ProofExport
public meta import Lean.Elab.Tactic.Simp
public import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Data.Json
public meta import Lean.Meta.Tactic.Refl
public meta import Std.Sync.Mutex

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

syntax simpExplicitPre := "↓"
syntax simpExplicitPost := "↑"
syntax simpExplicitPremiseArgs := " using " "[" term,* "]"
syntax simpExplicitRule := (simpExplicitPre <|> simpExplicitPost)? "← "? term
  (simpExplicitPremiseArgs)?
declare_syntax_cat simpExplicitSelector
syntax "match " num : simpExplicitSelector
syntax atomic(ident num) : simpExplicitSelector
syntax num : simpExplicitSelector
declare_syntax_cat simpExplicitReduction
syntax (name := simpExplicitReduceUnary)
  (simpExplicitPre <|> simpExplicitPost)? "reduce" ident : simpExplicitReduction
syntax (name := simpExplicitReduceNamed)
  (simpExplicitPre <|> simpExplicitPost)? "reduce" ident ident : simpExplicitReduction
syntax (name := simpExplicitReduceProjection)
  (simpExplicitPre <|> simpExplicitPost)? "reduce" ident ident num : simpExplicitReduction
declare_syntax_cat simpExplicitEvent
syntax (name := simpExplicitRuleEvent)
  (simpExplicitSelector " => ")? simpExplicitRule : simpExplicitEvent
syntax (name := simpExplicitReductionEvent)
  (simpExplicitSelector " => ")? simpExplicitReduction : simpExplicitEvent
syntax simpExplicitTraceArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?
declare_syntax_cat simpExplicitContextGroup
syntax "at" ident " => " "[" simpExplicitEvent,* "]" : simpExplicitContextGroup

/-- Replay an ordered simplifier certificate without consulting the simp set. -/
syntax (name := simpExplicit) "simp_explicit" " [" simpExplicitEvent,* "]" : tactic
/-- Replay an ordered certificate while preserving a reflexive final goal for
the following tactic, matching an ordinary `simp` call that did not close. -/
syntax (name := simpExplicitLeaveOpen) "simp_explicit" " leave_open" " ["
  simpExplicitEvent,* "]" : tactic
/-- Replay independent closed certificates against selected local declarations and
the target, using the same batch staging semantics as `simp at ...`. -/
syntax (name := simpExplicitContext) "simp_explicit_context" " [" simpExplicitContextGroup,* "]" : tactic
declare_syntax_cat simpExplicitLocalRename
syntax num " => " ident : simpExplicitLocalRename
/-- Give recorded local-context entries stable printable names. Unlike
`rename_i`, this operation addresses exact context indices and is idempotent,
so independently generated certificates can be composed in one declaration. -/
syntax (name := simpExplicitRename) "simp_explicit_rename" " ["
  simpExplicitLocalRename,* "]" : tactic
syntax (name := simpExplicitBodyScope) "simp_explicit_body_scope" str " in " tacticSeq : tactic
/-- On-demand variant of the body recorder that also exports a proof when the
complete inventoried body closes its input goal. Coverage uses this only after
an occurrence-level certificate fails source materialization. -/
syntax (name := simpExplicitBodyScopeProof) "simp_explicit_body_scope_proof" str
  " in " tacticSeq : tactic
/-- Instrument one closed `first` owner while materializing a body.  This is
    an internal source-rewriter primitive: it records a printable proof only
    when the wrapped owner closes its input goal. -/
syntax (name := simpExplicitFirstScope) "simp_explicit_first_scope" str " in " tacticSeq : tactic
/-- Internal passive-recorder entry point used by source rewriting. The source
identity is an argument rather than nested `set_option ... in` syntax so the
surrounding tactic context keeps its original macro scopes. -/
syntax (name := simpExplicitRecord) "simp_explicit_record" str simpExplicitTraceArgs : tactic
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

register_option explicitLean.simpExplicit.bodyScopeFrame : Nat := {
  defValue := 0
  descr := "internal body-scope registry frame (not a source/report identity)"
}

def reportSchema : String := "explicitLean.simpRecording"
def reportSchemaVersion : Nat := 11

structure ExprFingerprint where
  /-- A bounded diagnostic rendering for humans.  This is never used for replay. -/
  printable : String
  /-- A canonical, alpha-stable expression fingerprint. -/
  fingerprint : String
  deriving ToJson

/- The recorder compiles the source simp configuration into the generated
   event program.  Keep its provenance separately from the certificate: the
   replay tactic deliberately has no configuration mode and never consults
   ambient simp state.  Every built-in `Simp.Config` field is represented with
   JSON primitives; plugin-specific options remain available through `optConfig`.
-/
structure SimpConfigSummary where
  maxSteps : Nat
  maxDischargeDepth : Nat
  contextual : Bool
  memoize : Bool
  singlePass : Bool
  zeta : Bool
  beta : Bool
  eta : Bool
  etaStruct : String
  iota : Bool
  proj : Bool
  decide : Bool
  arith : Bool
  autoUnfold : Bool
  dsimp : Bool
  failIfUnchanged : Bool
  ground : Bool
  unfoldPartialApp : Bool
  zetaDelta : Bool
  index : Bool
  implicitDefEqProofs : Bool
  zetaUnused : Bool
  catchRuntime : Bool
  zetaHave : Bool
  letToHave : Bool
  congrConsts : Bool
  bitVecOfNat : Bool
  warnExponents : Bool
  suggestions : Bool
  maxSuggestions : Option Nat
  locals : Bool
  instances : Bool
  deriving ToJson

structure SimpConfigurationReport where
  /-- Pretty-printed `optConfig` syntax, retained even if elaboration failed. -/
  optConfig : String
  /-- The elaborated built-in configuration, when context construction succeeded. -/
  normalized : Option SimpConfigSummary
  deriving ToJson

private def etaStructModeText : EtaStructMode → String
  | .all => "all"
  | .notClasses => "notClasses"
  | .none => "none"

private def simpConfigSummary (config : Simp.Config) : SimpConfigSummary := {
  maxSteps := config.maxSteps
  maxDischargeDepth := config.maxDischargeDepth
  contextual := config.contextual
  memoize := config.memoize
  singlePass := config.singlePass
  zeta := config.zeta
  beta := config.beta
  eta := config.eta
  etaStruct := etaStructModeText config.etaStruct
  iota := config.iota
  proj := config.proj
  decide := config.decide
  arith := config.arith
  autoUnfold := config.autoUnfold
  dsimp := config.dsimp
  failIfUnchanged := config.failIfUnchanged
  ground := config.ground
  unfoldPartialApp := config.unfoldPartialApp
  zetaDelta := config.zetaDelta
  index := config.index
  implicitDefEqProofs := config.implicitDefEqProofs
  zetaUnused := config.zetaUnused
  catchRuntime := config.catchRuntime
  zetaHave := config.zetaHave
  letToHave := config.letToHave
  congrConsts := config.congrConsts
  bitVecOfNat := config.bitVecOfNat
  warnExponents := config.warnExponents
  suggestions := config.suggestions
  maxSuggestions := config.maxSuggestions
  locals := config.locals
  instances := config.instances
}

private def simpConfigurationReport (simpStx : Syntax)
    (config? : Option Simp.Config := none) : SimpConfigurationReport := {
  optConfig := toString simpStx[1].prettyPrint
  normalized := config?.map simpConfigSummary
}

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

/-! A reduction is a first-class replay operation.  In particular, it is not
    represented as `Origin.other`: the latter is reserved for opaque simp
    provenance and cannot express an ambient-free operation. -/
inductive ReductionKind where
  | delta (name : Name)
  | beta
  | zeta
  | iota
  | projection (structureName : Name) (field : Nat)
  | eta
  deriving BEq, Repr

structure ReductionIdentity where
  kind : ReductionKind

structure ReductionReport where
  kind : String
  name : Option String
  field : Option Nat
  deriving ToJson

/-! The recorder keeps transition diagnostics separate from certificate source.
    The fingerprints are intentionally bounded, alpha-stable recording data;
    none of these fields is copied into a replacement theorem. -/
structure TransitionContinuityReport where
  firstUnconsumedEventIndex : Option Nat
  /-- `before_event`, `between_events`, or `after_events`.  The index is
      `recorded.size` for a trailing transition. -/
  gapLocation : String
  noNamedSelectorCandidate : Bool
  nextConsumedCount : Nat
  matchConsumedCount : Nat
  tickConsumedCount : Nat
  initialSubjectFingerprint : Option ExprFingerprint
  replayedPrefixFingerprint : Option ExprFingerprint
  expectedEventInputFingerprint : Option ExprFingerprint
  expectedEventResultFingerprint : Option ExprFingerprint
  matchedSubexpressionFingerprint : Option ExprFingerprint
  /-- Stable, diagnostic-only path from the replayed prefix subject to the
      matched subexpression.  Labels identify expression-child positions;
      this is never used as certificate source. -/
  matchedSubexpressionPath : Array String
  recordedFinalStateFingerprint : Option ExprFingerprint
  replayedFinalStateFingerprint : Option ExprFingerprint
  expectedEventOrigins : Array String
  reasonCode : String
  operationHint : Option String
  operationKind : Option String
  hintClassification : Option String
  deriving ToJson

structure OperationalAdmissibility where
  accepted : Bool
  code : String
  reason : Option String
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
  origins : Array OriginCandidate
  encodingKind : Option String
  encodingReason : Option String
  bindingName : Option String
  deriving ToJson

structure SubjectReport where
  kind : String
  name : Option String
  contextIndex : Option Nat
  deriving ToJson

structure SubjectTransportReport where
  originalContextIndex : Nat
  originalName : Option String
  resultingContextIndex : Option Nat
  resultingName : Option String
  originalCleared : Bool
  deriving ToJson

structure SubjectSummary where
  subject : SubjectReport
  initial : ExprFingerprint
  result : ExprFingerprint
  closesGoal : Bool
  eventCount : Nat
  transport : Option SubjectTransportReport
  transitionContinuity : Option TransitionContinuityReport
  operationalAdmissibility : OperationalAdmissibility
  deriving ToJson

structure SemanticEventReport where
  subject : SubjectReport
  tick : Nat
  phase : String
  input : ExprFingerprint
  step : String
  result : ExprFingerprint
  proof : Option ExprFingerprint
  reduction : Option ReductionReport
  origins : Array OriginCandidate
  premises : Array PremiseReport
  /-- `named_rule` for a compact origin replay, `generated_proof` for the
      authoritative result-proof fallback. -/
  encodingKind : Option String
  /-- Why a generated proof binding was needed, when applicable. -/
  encodingReason : Option String
  /-- Selector emitted for this event, when the certificate has been encoded. -/
  selectorKind : Option String
  /-- Ordinal for `match`, or absolute traversal position for `tick`. -/
  selectorValue : Option Nat
  deriving ToJson

structure EncodingMetrics where
  mode : String := "event"
  /-- Number of emitted presentation-only `change` prepasses. -/
  presentationChangeCount : Nat := 0
  namedRuleEvents : Nat := 0
  reductionEvents : Nat := 0
  deltaReductionEvents : Nat := 0
  generatedProofEvents : Nat := 0
  generatedSimprocEvents : Nat := 0
  generatedSpecialEvents : Nat := 0
  wholeResultProofCount : Nat := 0
  generatedBindingCount : Nat := 0
  generatedBindingBytes : Nat := 0
  premiseBindingCount : Nat := 0
  premiseBindingBytes : Nat := 0
  nestedPremiseBindings : Nat := 0
  termPremiseBindings : Nat := 0
  nextSelectorCount : Nat := 0
  matchSelectorCount : Nat := 0
  tickSelectorCount : Nat := 0
  totalCertificateBytes : Nat := 0
  deriving ToJson

private def computeOperationalAdmissibility
    (metrics : EncodingMetrics)
    (suggestion : String)
    (overrideCode? : Option String := none)
    (transitionContinuity? : Option TransitionContinuityReport := none) : OperationalAdmissibility :=
  let inferredCode? :=
    if metrics.generatedSimprocEvents > 0 then
      some "deferred_simproc"
    else if let some continuity := transitionContinuity? then
      some continuity.reasonCode
    else if let some overrideCode := overrideCode? then
      some overrideCode
    else if metrics.termPremiseBindings > 0 then
      some "inadmissible_direct_term_premise"
    else if metrics.wholeResultProofCount > 0 || metrics.mode == "whole_result_proof" then
      some "inadmissible_whole_result_proof"
    else if metrics.presentationChangeCount > 0 || metrics.mode == "presentation_change" then
      some "inadmissible_presentation_change"
    else if metrics.generatedSpecialEvents > 0 then
      some "inadmissible_generated_special_rule"
    else if metrics.generatedProofEvents > 0 then
      some "inadmissible_generated_proof"
    else if suggestion.isEmpty then
      some "unavailable"
    else
      some "accepted"
  match inferredCode? with
  | some "accepted" => { accepted := true, code := "accepted", reason := none }
  | some code => {
      accepted := false
      code
      reason := some code
    }
  | none => { accepted := false, code := "unavailable", reason := some "unavailable" }

/- A proof-result encoder is intentionally the only public surface needed by
   other tactic producers.  The recorder's semantic event and replay state
   remain private; callers receive the validated source and its compact
   encoding diagnostics. -/
structure ProofResultEncoding where
  source : String
  metrics : EncodingMetrics
  encodingKind : String
  encodingReason : Option String

structure LocalRenameInfo where
  /-- Stable local-context index renamed by `simp_explicit_rename`. -/
  contextIndex : Nat
  generatedName : String
  deriving ToJson

structure ExecutionReport where
  /-- Deterministic source-scope token; empty for unscoped compatibility reports. -/
  attemptToken : String
  executionIndex : Nat
  result : String
  /-- `none` means that enclosing combinator instrumentation has not established
      commitment. Package F may replace this with `committed` or `backtracked`. -/
  disposition : Option String
  /-- The certificate owned by this dynamic execution, when one was encoded. -/
  certificate : Option String
  /-- Certificate source accepted by the operational materializer.  Legacy
      fallback source, when present, is retained separately for migration
      diagnostics and must never be selected as a replacement. -/
  acceptedCertificate : Option String
  legacyCertificate : Option String
  legacyCertificateBytes : Nat
  certificateBytes : Nat
  certificateEventCount : Nat
  positionsNeeded : Bool
  encodingStatus : String
  recordingReason : Option String
  encoding : EncodingMetrics
  encodingFallbackReason : Option String
  operationallyAdmissible : Bool
  operationalAdmissibility : OperationalAdmissibility
  transitionContinuity : Option TransitionContinuityReport
  localRenames : Array LocalRenameInfo
  closesGoal : Bool
  trace : Array SemanticEventReport
  subjects : Array SubjectSummary
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
  bodyScopeId : Option String
  declaration : String
  originalSyntax : String
  configuration : SimpConfigurationReport
  closesGoal : Bool
  traceLength : Nat
  certificateEventCount : Nat
  positionsNeeded : Bool
  certificateBytes : Nat
  certificate : String
  acceptedCertificate : Option String
  legacyCertificate : Option String
  legacyCertificateBytes : Nat
  executions : Array ExecutionReport
  terminalOutcome : Option String
  failureCategory : Option String
  failureMessage : Option String
  traceAvailable : Bool
  encodingStatus : String
  recordingReason : Option String
  encoding : EncodingMetrics
  encodingFallbackReason : Option String
  operationallyAdmissible : Bool
  operationalAdmissibility : OperationalAdmissibility
  transitionContinuity : Option TransitionContinuityReport
  localRenames : Array LocalRenameInfo
  validation : Option ValidationEnvelope
  deriving ToJson

/-! Dynamic body-scope state is deliberately kept outside Meta state.  The
    sentinel itself is a Meta mvar, while the report payload and its source
    token live in this IO registry so a tactic combinator can roll Meta state
    back without erasing the diagnostic record.  The registry is process
    local and frames are stacked, so nested elaboration cannot overwrite a
    sibling scope's records.  MVarIds and frame ids never cross the JSON
    boundary. -/
structure ScopedAttempt where
  frameId : Nat
  occurrenceId : String
  attemptToken : String
  sentinel : MVarId
  reportRef : IO.Ref (Option RecordingReport)

structure ScopedFrame where
  frameId : Nat
  scopeId : String
  attempts : Array ScopedAttempt

structure ScopedRegistry where
  nextFrameId : Nat
  frames : Array ScopedFrame
  deriving Nonempty

initialize scopedRegistry : Std.Mutex ScopedRegistry ←
  Std.Mutex.new { nextFrameId := 1, frames := #[] }

inductive Phase where
  | pre
  | post
  deriving BEq, Repr

private structure RecordedPremise where
  proposition : Expr
  proof : Expr
  origins : Array Origin

private structure PremiseEncodingInfo where
  kind : String
  reason : Option String
  bindingName : Option Name
  bytes : Nat

private structure RecordedEvent where
  tick : Nat
  phase : Phase
  input : Expr
  step : Simp.Step
  result : Simp.Result
  origins : Array Origin
  premises : Array RecordedPremise
  reduction : Option ReductionIdentity := none

private structure EventEncodingInfo where
  kind : String
  reason : Option String
  selectorKind : Option String := none
  selectorValue : Option Nat := none

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

private def subtractOrigins (origins removed : Array Origin) : Array Origin := Id.run do
  let mut remaining := removed
  let mut result := #[]
  for origin in origins do
    let mut found := false
    let mut next := #[]
    for candidate in remaining do
      if !found && candidate == origin then
        found := true
      else
        next := next.push candidate
    if !found then
      result := result.push origin
    remaining := next
  return result

/-! This is the deliberately narrow recorder seam for named delta.  The
    private simplifier `reduceStep` is not mirrored: we only inspect a public
    pre-method boundary after it has declined to rewrite the expression. -/
private def selectedDeltaReduction? (input : Expr) : Simp.SimpM (Option (Name × Expr)) := do
  let .const head _ := input.getAppFn | return none
  let cfg ← Simp.getConfig
  let ctx ← Simp.getContext
  if cfg.beta && input.getAppFn.isHeadBetaTargetFn false then
    return none
  if input.isProj then
    return none
  if ← isProjectionFn head then
    return none
  if cfg.autoUnfold then
    return none
  if cfg.iota then
    let metaSnapshot ← liftM Meta.saveState
    let simpSnapshot ← get
    try
      let iota? ← Simp.withSimpMetaConfig <| reduceRecMatcher? input
      liftM metaSnapshot.restore
      set simpSnapshot
      if iota?.isSome then
        return none
    catch _ =>
      liftM metaSnapshot.restore
      set simpSnapshot
      return none
  unless ctx.isDeclToUnfold head do
    return none
  if ← isIrreducible head then
    return none
  let options ← getOptions
  let smart := smartUnfolding.get options && (← getEnv).contains (mkSmartUnfoldingNameFor head)
  unless cfg.unfoldPartialApp || smart do
    let some cinfo := (← getEnv).find? head | return none
    let some value := cinfo.value? | return none
    if value.getNumHeadLambdas > input.getAppNumArgs then
      return none
  let some output ← Simp.withSimpMetaConfig <| unfoldDefinition? input (ignoreTransparency := true)
    | return none
  if Expr.equal input output then
    return none
  return some (head, output)

private def trackedMethod (ref : IO.Ref RecorderState) (phase : Phase)
    (method : Simp.Simproc) : Simp.Simproc := fun input => do
  let state ← ref.get
  let position := state.tick + 1
  let depth := state.activeDepth
  ref.set { state with tick := position, activeDepth := depth + 1 }
  let premiseStart := state.premises.size
  let before := (← get).diag
  let originalStep ← try
    method input
  finally
    let state ← ref.get
    ref.set { state with activeDepth := state.activeDepth - 1 }
  let mut step := originalStep
  let mut reduction? : Option ReductionIdentity := none
  if depth == 0 && phase == .pre then
    match originalStep with
    | .continue none =>
        if let some (head, output) ← selectedDeltaReduction? input then
          let result : Simp.Result := { expr := output }
          step := .visit result
          reduction? := some { kind := .delta head }
    | _ => pure ()
  let after := (← get).diag
  if depth == 0 then
    if let some result := changedResult? input step then
      let state ← ref.get
      let premises := state.premises.extract premiseStart state.premises.size
      let premiseOrigins := premises.foldl (fun result premise => result ++ premise.origins) #[]
      ref.set {
        state with
          events := state.events.push {
            tick := position
            phase
            input
            step
            result
            origins := if reduction?.isSome then #[] else
              subtractOrigins (changedOrigins before after) premiseOrigins
            premises
            reduction := reduction?
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
      let before := (← get).diag
      let result? ← methods.discharge? proposition
      let after := (← get).diag
      if let some proof := result? then
        let state ← ref.get
        ref.set {
          state with
            premises := state.premises.push {
              proposition
              proof
              origins := changedOrigins before after
            }
        }
      return result? }

/-- State for the one bounded presentation probe used by the F3 encoder.  The
    probe deliberately suppresses proof-producing/default rewrites while one
    deterministic `Simp.mainCore` pass commits every proofless,
    expression-changing method result. -/
private structure PresentationProbeState where
  candidates : Array (Expr × Expr) := #[]

private def presentationMethod (ref : IO.Ref PresentationProbeState)
    (method : Simp.Simproc) : Simp.Simproc := fun input => do
  let metaSnapshot ← liftM Meta.saveState
  let simpSnapshot ← get
  try
    let step ← method input
    match stepResult? step with
    | some result =>
        let state ← ref.get
        if result.proof?.isNone && !Expr.equal result.expr input then
          ref.set {
            candidates := state.candidates.push (input, result.expr)
          }
          return step
        else
          -- A rejected method is observational only. Restore both Meta and
          -- Simp state: default dischargers and caches may have assigned
          -- metavariables or consumed diagnostics before returning a result.
          liftM metaSnapshot.restore
          set simpSnapshot
          return .continue
    | none =>
        liftM metaSnapshot.restore
        set simpSnapshot
        return .continue
  catch _ =>
    liftM metaSnapshot.restore
    set simpSnapshot
    return .continue

private def presentationCandidate? (target : Expr) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) (recorded : Array RecordedEvent) :
    TacticM (Option (Expr × Array (Expr × Expr))) := do
  try
    -- The theorem engine is independent of `Simp.Methods`; method wrappers
    -- alone cannot suppress recorded proof-bearing rewrites.  Remove exactly
    -- the origins of those events from this speculative context, preserving
    -- all original definition/unfolding entries and proofless rules.
    let presentationTheorems := recorded.foldl (fun theorems event =>
      if event.result.proof?.isSome then
        event.origins.foldl (fun theorems origin => theorems.eraseTheorem origin) theorems
      else
        theorems) ctx.simpTheorems
    let presentationCtx := ctx.setSimpTheorems presentationTheorems
    withoutModifyingState do
      let ref ← IO.mkRef ({} : PresentationProbeState)
      let methods := Simp.mkDefaultMethodsCore simprocs
      let methods : Simp.Methods := {
        methods with
          pre := presentationMethod ref methods.pre
          post := presentationMethod ref methods.post
      }
      let (result, _) ← withOptions (·.setBool `diagnostics true) do
        Simp.mainCore target presentationCtx (methods := methods)
      let probe ← ref.get
      -- Return the complete target produced by the probe. The accepted local
      -- pairs are only boundary evidence for removing presentation events
      -- already realized by this pass.
      -- The candidate must be a genuine presentation change, but remain
      -- definitionally equal to the original target so `change` is checked by
      -- the kernel at the replacement site.
      unless !Expr.equal result.expr target do
        return none
      unless ← isDefEq result.expr target do
        return none
      return some (result.expr, probe.candidates)
  catch _ =>
    return none

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

private inductive ReplaySelector where
  | next
  | matchSite (ordinal : Nat)
  | tickPos (position : Nat)
  /-- Internal-only selector used while discovering a stable match ordinal. -/
  | discover (input : Expr) (result : Expr)

private def selectorKind? : ReplaySelector → Option String
  | .next => some "next"
  | .matchSite _ => some "match"
  | .tickPos _ => some "tick"
  | .discover .. => none

private def selectorValue? : ReplaySelector → Option Nat
  | .next => none
  | .matchSite ordinal => some ordinal
  | .tickPos position => some position
  | .discover .. => none

private def isTickSelector : ReplaySelector → Bool
  | .tickPos _ => true
  | _ => false

private def selectorSource : ReplaySelector → String
  | .next => ""
  | .matchSite ordinal => s!"match {ordinal} => "
  | .tickPos position => s!"tick {position} => "
  | .discover .. => ""

private def reductionReport (reduction : ReductionIdentity) : ReductionReport :=
  match reduction.kind with
  | .delta name => {
      kind := "delta"
      name := some name.toString
      field := none
    }
  | .beta => { kind := "beta", name := none, field := none }
  | .zeta => { kind := "zeta", name := none, field := none }
  | .iota => { kind := "iota", name := none, field := none }
  | .projection structureName field => {
      kind := "projection"
      name := some structureName.toString
      field := some field
    }
  | .eta => { kind := "eta", name := none, field := none }

private def reductionText (reduction : ReductionIdentity) : String :=
  match reduction.kind with
  | .delta name => s!"reduce delta {name}"
  | .beta => "reduce beta"
  | .zeta => "reduce zeta"
  | .iota => "reduce iota"
  | .projection structureName field => s!"reduce projection {structureName} {field}"
  | .eta => "reduce eta"

private def reductionSource (reduction : ReductionIdentity) (phase : Phase) : String := by
  let phasePrefix := if phase == .pre then "" else "↑ "
  exact phasePrefix ++ reductionText reduction

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

private def certificateEventListText (events : Array RecordedEvent)
    (selectors : Array ReplaySelector := #[])
    (includeTrailingReflexive : Bool := false) : MetaM String := do
  let eventCount := if includeTrailingReflexive then events.size else certificateEventCount events
  if eventCount == 0 then
    return "[]"
  let mut lines := #["["]
  for index in *...eventCount do
    let some event := events[index]?
      | throwError "simp_explicit recorder produced an inconsistent event count"
    let comma := if index + 1 < eventCount then "," else ""
    let selector := selectors[index]?.getD .next
    let command ← match event.reduction with
      | some reduction => pure (reductionSource reduction event.phase)
      | none => do
          let some origin := event.origins[0]?
            | throwError "simp_explicit cannot encode semantic event {index}: no diagnostic origin candidate"
          unless event.origins.size == 1 do
            throwError "simp_explicit cannot encode semantic event {index}: observed {event.origins.size} diagnostic origin candidates"
          let rule ← ruleText origin
          let phase := if event.phase == .pre then "↓ " else ""
          pure (phase ++ rule)
    lines := lines.push s!"  {selectorSource selector}{command}{comma}"
  lines := lines.push "]"
  return String.intercalate "\n" lines.toList

private def certificateText (events : Array RecordedEvent)
    (selectors : Array ReplaySelector := #[]) (leaveOpen := false) : MetaM String := do
  let command := if leaveOpen then "simp_explicit leave_open " else "simp_explicit "
  return command ++ (← certificateEventListText events selectors)

private def applyResultToTarget (mvarId : MVarId) (target : Expr)
    (result : Simp.Result) (closeReflexive := true) : TacticM Unit := do
  if result.expr.isTrue then
    let proof ← match result.proof? with
      | some equality => mkOfEqTrue equality
      | none => pure (mkConst ``True.intro)
    mvarId.assign proof
    replaceMainGoal []
  else
    let mvarId ← applySimpResultToTarget mvarId target result
    let simplifiedTarget ← instantiateMVars (← mvarId.getType)
    if closeReflexive && simplifiedTarget.isAppOfArity ``Eq 3 then
      try
        mvarId.refl
        replaceMainGoal []
        return
      catch _ => pure ()
    else if closeReflexive && simplifiedTarget.isAppOfArity ``Iff 2 then
      let lhs := simplifiedTarget.appFn!.appArg!
      let rhs := simplifiedTarget.appArg!
      if (← isDefEq lhs rhs) then
        mvarId.assign (mkApp (mkConst ``Iff.rfl) lhs)
        replaceMainGoal []
        return
    replaceMainGoal [mvarId]

private structure ReplayEvent where
  selector : ReplaySelector
  phase : Phase
  rules : Array SimpTheorem
  premises : Array Expr := #[]
  reduction : Option ReductionIdentity := none
  source : Syntax

private structure GeneratedBinding where
  name : Name
  kind : String
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
  premiseNames : Array Name := #[]
  premiseEncodings : Array PremiseEncodingInfo := #[]
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
  siteCount : Nat := 0
  premiseNext : Nat := 0
  premiseFailure? : Option String := none
  /-- Ordinals discovered for committed internal discovery events, in cursor order. -/
  discoveredOrdinals : Array Nat := #[]

private structure LocalRenamePlan where
  contextIndex : Nat
  fvarId : FVarId
  generatedName : Name

private structure EncodingAttempt where
  suggestion : String
  encodingInfos : Array EventEncodingInfo
  premiseEncodingInfos : Array (Array PremiseEncodingInfo)
  encodingMetrics : EncodingMetrics
  encodingFallbackReason? : Option String
  positionsNeeded : Bool
  transitionContinuity? : Option TransitionContinuityReport

private def premiseDefEqHeartbeatBudget : Nat := 20000

private def premiseDefEq? (actual expected : Expr) : MetaM (Except String Bool) := do
  let actual ← instantiateMVars actual
  let expected ← instantiateMVars expected
  if Expr.equal actual expected then
    return .ok true
  try
    -- This is a raw Core heartbeat budget, deliberately independent of the
    -- user's `maxHeartbeats` option.  `isDefEq` consults the Core reader.
    let equal ← withTheReader Core.Context
        (fun context => { context with maxHeartbeats := premiseDefEqHeartbeatBudget }) do
      withCurrHeartbeats do
        withReducible <| isDefEq actual expected
    return .ok equal
  catch ex =>
    if ex.isMaxHeartbeat then
      return .error "premise_defeq_timeout"
    throw ex

private def premiseProvider (premises : Array Expr) (ref : IO.Ref ReplayState)
    (proposition : Expr) : Simp.SimpM (Option Expr) := do
  let state ← ref.get
  match premises[state.premiseNext]? with
  | none =>
      ref.set { state with premiseFailure? := some "premise_missing" }
      return none
  | some proof =>
      let proof ← instantiateMVars proof
      let proposition ← instantiateMVars proposition
      let proofType ← try
        instantiateMVars (← inferType proof)
      catch _ =>
        ref.set { state with premiseFailure? := some "premise_type_mismatch" }
        return none
      let valid? ← premiseDefEq? proofType proposition
      match valid? with
      | .error reason =>
          ref.set { state with premiseFailure? := some reason }
          return none
      | .ok false =>
          ref.set { state with premiseFailure? := some "premise_type_mismatch" }
          return none
      | .ok true =>
          let proof ← try
            mkExpectedTypeHint proof proposition
          catch _ =>
            ref.set { state with premiseFailure? := some "premise_type_mismatch" }
            return none
          ref.set { state with premiseNext := state.premiseNext + 1 }
          return some proof

private def parsePhase (stx : Syntax) : TacticM Phase :=
  if stx.isOfKind ``Lean.Parser.Tactic.simpExplicitPre then
    pure .pre
  else if stx.isOfKind ``Lean.Parser.Tactic.simpExplicitPost then
    pure .post
  else
    throwErrorAt stx "expected `↓` or `↑`"

private def elaborateReduction (stx : Syntax) : TacticM (Phase × ReductionIdentity) := do
  let phase ← if stx[0].isNone then pure .pre else parsePhase stx[0][0]
  let operation := stx[2].getId
  if stx.getNumArgs == 5 then
    unless operation == `projection do
      throwErrorAt stx[2] "expected `projection` for a four-argument reduction command"
    let some field := stx[4].isNatLit?
      | throwErrorAt stx[4] "expected a numeric projection field index"
    return (phase, { kind := .projection stx[3].getId field })
  if stx.getNumArgs == 4 then
    unless operation == `delta do
      throwErrorAt stx[2] "expected `delta` for a named reduction command"
    return (phase, { kind := .delta stx[3].getId })
  unless stx.getNumArgs == 3 do
    throwErrorAt stx "invalid simp_explicit reduction command"
  match operation with
  | `beta => return (phase, { kind := .beta })
  | `zeta => return (phase, { kind := .zeta })
  | `iota => return (phase, { kind := .iota })
  | `eta => return (phase, { kind := .eta })
  | _ => throwErrorAt stx[2] "unknown simp_explicit reduction operation"

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

private def premiseSyntaxes (rule : Syntax) : Array Syntax :=
  if rule[3].isNone || rule[3].getNumArgs == 0 then
    #[]
  else
    match rule[3][0] with
    | `(Lean.Parser.Tactic.simpExplicitPremiseArgs| using [$terms:term,*]) => terms.getElems
    | _ => #[]

private def elaboratePremise (term : Syntax) : TacticM Expr := do
  Term.withoutModifyingElabMetaStateWithInfo <| withRef term do
    let proof ← Term.elabTerm term .none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let proof ← instantiateMVars proof
    if proof.hasSyntheticSorry || proof.hasMVar then
      throwErrorAt term "could not elaborate explicit simp premise"
    return proof

private def elaborateSelector (stx : Syntax) : TacticM ReplaySelector := do
  match stx with
  | `(simpExplicitSelector| match $n:num) =>
      let some ordinal := n.raw.isNatLit?
        | throwErrorAt n "expected a numeric match ordinal"
      if ordinal == 0 then
        throwErrorAt stx "simp_explicit match ordinals start at 1"
      return .matchSite ordinal
  | `(simpExplicitSelector| $kind:ident $n:num) =>
      unless kind.getId == `tick do
        throwErrorAt kind "expected `tick n` as the explicit traversal selector"
      let some position := n.raw.isNatLit?
        | throwErrorAt n "expected a numeric traversal position"
      if position == 0 then
        throwErrorAt stx "simp_explicit traversal positions start at 1"
      return .tickPos position
  | `(simpExplicitSelector| $n:num) =>
      let some position := n.raw.isNatLit?
        | throwErrorAt n "expected a numeric traversal position"
      if position == 0 then
        throwErrorAt stx "simp_explicit traversal positions start at 1"
      return .tickPos position
  | _ =>
      throwErrorAt stx "expected `match n`, `tick n`, or a numeric traversal position"

private def elaborateEvent (stx : Syntax) : TacticM ReplayEvent := do
  let selector ← if stx[0].isNone then pure .next else elaborateSelector stx[0][0]
  let rule := stx[1]
  if rule.getKind == ``Lean.Parser.Tactic.simpExplicitReduceUnary ||
      rule.getKind == ``Lean.Parser.Tactic.simpExplicitReduceNamed ||
      rule.getKind == ``Lean.Parser.Tactic.simpExplicitReduceProjection then
    let (phase, reduction) ← elaborateReduction rule
    return { selector, phase, rules := #[], premises := #[], reduction := some reduction, source := stx }
  else
    let phase ← if rule[0].isNone then pure .post else parsePhase rule[0][0]
    let rules ← elaborateRule phase rule
    let premises ← premiseSyntaxes rule |>.mapM elaboratePremise
    return { selector, phase, rules, premises, source := stx }

private def recordedReplayEvent (event : RecordedEvent)
    (selector : ReplaySelector := .next) : TacticM ReplayEvent := do
  if let some reduction := event.reduction then
    return {
      selector
      phase := event.phase
      rules := #[]
      premises := #[]
      reduction := some reduction
      source := (mkIdent `reduce).raw
    }
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
    selector
    phase := event.phase
    rules
    premises := event.premises.map (·.proof)
    reduction := none
    source
  }

private def applyRecordedRules? (input : Expr) (event : ReplayEvent)
    (ref : IO.Ref ReplayState) : Simp.SimpM (Option Simp.Result) := do
  let initial ← ref.get
  let mut lastFailure? : Option String := initial.premiseFailure?
  for rule in event.rules do
    let snapshot ← ref.get
    ref.set { snapshot with premiseNext := 0, premiseFailure? := none }
    let metaSnapshot ← liftM Meta.saveState
    let result? ← try
      Simp.withDischarger (premiseProvider event.premises ref) false <|
        Simp.tryTheorem? input rule
    catch ex =>
      liftM metaSnapshot.restore
      ref.set snapshot
      throw ex
    let after ← ref.get
    let reason? := after.premiseFailure?
    let restoreMeta := do
      liftM metaSnapshot.restore
      ref.set { snapshot with premiseFailure? := reason? }
    match result? with
    | some result =>
        if after.premiseNext == event.premises.size then
          ref.set { after with premiseFailure? := none }
          return some result
        lastFailure? := some "premise_unconsumed"
        liftM metaSnapshot.restore
        ref.set { snapshot with premiseFailure? := lastFailure? }
    | none =>
        -- A failed theorem candidate must not leave metavariable assignments
        -- behind.  Keep only the structured provider reason for diagnostics.
        if let some reason := reason? then
          lastFailure? := some reason
        restoreMeta
  let state ← ref.get
  ref.set { state with premiseFailure? := lastFailure? }
  return none

/- A continuity comparison is diagnostic-only and may unfold ordinary
   definitions such as `Finsupp.sum`.  Keep it separately bounded from the
   stricter premise/certificate validation relation above. -/
private def diagnosticDefEq? (actual expected : Expr) : MetaM Bool := do
  if actual.hasLooseBVars || expected.hasLooseBVars then
    return false
  let lctx ← getLCtx
  let actualWellFormed ← MetavarContext.isWellFormed lctx actual
  let expectedWellFormed ← MetavarContext.isWellFormed lctx expected
  if !actualWellFormed || !expectedWellFormed then
    return false
  let metaSnapshot ← Meta.saveState
  try
    let equal ← withTheReader Core.Context
        (fun context => { context with maxHeartbeats := premiseDefEqHeartbeatBudget }) do
      withCurrHeartbeats do
        withTransparency .default <| isDefEq actual expected
    metaSnapshot.restore
    return equal
  catch _ =>
    metaSnapshot.restore
    return false

private def replayExprMatches? (actual expected : Expr) : Simp.SimpM Bool := do
  if Expr.equal actual expected then
    return true
  -- Discovery is allowed a bounded reducible-definitional fallback, but the
  -- comparison itself must not leak assignments into either a skipped probe
  -- or the selected theorem application.
  let metaSnapshot ← liftM Meta.saveState
  try
    let result ← liftM (premiseDefEq? actual expected)
    liftM metaSnapshot.restore
    match result with
    | .ok equal => return equal
    | .error _ => return false
  catch _ =>
    liftM metaSnapshot.restore
    return false

private def prooflessReductionResult? (input output : Expr) : Option Simp.Result :=
  if Expr.equal input output then none else some { expr := output }

/-! Reduction replay deliberately uses only the operation named in the
    certificate.  It never invokes `Simp.reduceStep`, `Simp.mainCore`, or an
    ambient simp configuration. -/
private def replayDelta? (input : Expr) (name : Name) : Simp.SimpM (Option Expr) := do
  let .const head _ := input.getAppFn | return none
  unless head == name do
    return none
  if ← isIrreducible name then
    return none
  let snapshot ← liftM Meta.saveState
  try
    let output? ← Simp.withSimpMetaConfig <|
      unfoldDefinition? input (ignoreTransparency := true)
    match output? with
    | some output => return some output
    | none =>
        liftM snapshot.restore
        return none
  catch _ =>
    liftM snapshot.restore
    return none

private def replayBeta? (input : Expr) : MetaM (Option Expr) := do
  let f := input.getAppFn
  if f.isHeadBetaTargetFn false then
    return some (f.betaRev input.getAppRevArgs)
  return none

private def replayZeta? (input : Expr) : MetaM (Option Expr) := do
  match input with
  | .letE _ _ value body _ =>
      return some (expandLet body #[value] (zetaHave := true))
  | _ => return none

private def replayIota? (input : Expr) : Simp.SimpM (Option Expr) := do
  let snapshot ← Meta.saveState
  try
    let output? ← Simp.withSimpMetaConfig <|
      withConfig (fun config => { config with iota := true }) <|
        reduceRecMatcher? input
    match output? with
    | some output => return some output
    | none =>
        snapshot.restore
        return none
  catch _ =>
    snapshot.restore
    return none

private def replayProjection? (input : Expr) (structureName : Name) (field : Nat) : Simp.SimpM (Option Expr) := do
  match input with
  | .proj inputStructure inputField _ =>
      unless inputStructure == structureName && inputField == field do
        return none
      let snapshot ← Meta.saveState
      try
        let output? ← Simp.withSimpMetaConfig <|
          withConfig (fun config => { config with proj := .yesWithDelta }) <|
            reduceProj? input
        match output? with
        | some output => return some output
        | none =>
            snapshot.restore
            return none
      catch _ =>
        snapshot.restore
        return none
  | _ => return none

private def replayEta? (input : Expr) : MetaM (Option Expr) := do
  let output := input.eta
  return if Expr.equal input output then none else some output

private def applyRecordedReduction? (input : Expr) (reduction : ReductionIdentity) :
    Simp.SimpM (Option Simp.Result) := do
  let output? ← match reduction.kind with
    | .delta name => replayDelta? input name
    | .beta => liftM <| replayBeta? input
    | .zeta => liftM <| replayZeta? input
    | .iota => replayIota? input
    | .projection structureName field => replayProjection? input structureName field
    | .eta => liftM <| replayEta? input
  return output?.bind (prooflessReductionResult? input)

private def hasUncommandedReduction (input : Expr) : Simp.SimpM Bool := do
  let iotaSnapshot ← liftM Meta.saveState
  let iota? ← replayIota? input
  liftM iotaSnapshot.restore
  if iota?.isSome then
    return true
  let .proj structureName field _ := input | return false
  let snapshot ← liftM Meta.saveState
  let output? ← replayProjection? input structureName field
  liftM snapshot.restore
  return output?.isSome

private def applyReplayEvent? (input : Expr) (event : ReplayEvent)
    (ref : IO.Ref ReplayState) : Simp.SimpM (Option Simp.Result) := do
  match event.reduction with
  | some reduction => applyRecordedReduction? input reduction
  | none => applyRecordedRules? input event ref

private def replayMethod (events : Array ReplayEvent) (ref : IO.Ref ReplayState)
    (phase : Phase) : Simp.Simproc := fun input => do
  let state ← ref.get
  let state := { state with tick := state.tick + 1 }
  ref.set state
  if h : state.next < events.size then
    let event := events[state.next]
    match event.selector with
    | .tickPos position =>
        if position < state.tick then
          throwErrorAt event.source "simp_explicit passed recorded traversal position {position} without applying its rule"
        else if position == state.tick then
          unless event.phase == phase do
            throwErrorAt event.source "simp_explicit traversal phase changed at position {position}"
          let some result ← applyReplayEvent? input event ref
            | match (← ref.get).premiseFailure? with
              | some reason =>
                  throwErrorAt event.source
                    "simp_explicit {reason} at traversal position {position}"
              | none =>
                  throwErrorAt event.source
                    "recorded simp rule no longer rewrites the expression at traversal position {position}"
          ref.set { state with next := state.next + 1, siteCount := 0, premiseNext := 0, premiseFailure? := none }
          return .visit result
    | .next =>
        if event.phase == phase then
          if let some result ← applyReplayEvent? input event ref then
            ref.set { state with next := state.next + 1, siteCount := 0, premiseNext := 0, premiseFailure? := none }
            return .visit result
          else
            -- Position-free events are tried at every traversal callback. A
            -- failed premise at one callback is not terminal: a later
            -- callback may be the exact recorded site. Keep the latest
            -- structured reason for the final cursor diagnostic instead.
            pure ()
    | .matchSite ordinal =>
        if event.phase == phase then
          let probeState ← ref.get
          let metaSnapshot ← liftM Meta.saveState
          try
            let result? ← applyReplayEvent? input event ref
            match result? with
            | none =>
                -- A failed match probe is observational only. In particular,
                -- premise cursors and diagnostics must not leak to a later
                -- callback site.
                liftM metaSnapshot.restore
                ref.set probeState
            | some result =>
                if Expr.equal result.expr input then
                  -- A proof-carrying result which leaves the callback input
                  -- unchanged is not a match site. Restore both snapshots so
                  -- it cannot consume a premise or assign a theorem mvar.
                  liftM metaSnapshot.restore
                  ref.set probeState
                else
                  let observed := probeState.siteCount + 1
                  if observed < ordinal then
                    -- The successful site is deliberately skipped. Restore
                    -- theorem metavariables and event-local state, retaining
                    -- only ordinal progress for the next probe.
                    liftM metaSnapshot.restore
                    ref.set { probeState with siteCount := observed, premiseNext := 0, premiseFailure? := none }
                  else if observed == ordinal then
                    let after ← ref.get
                    ref.set { after with next := state.next + 1, siteCount := 0, premiseNext := 0, premiseFailure? := none }
                    return .visit result
                  else
                    liftM metaSnapshot.restore
                    ref.set probeState
                    throwErrorAt event.source
                      "simp_explicit match ordinal {ordinal} was passed unexpectedly"
          catch ex =>
            liftM metaSnapshot.restore
            ref.set probeState
            throw ex
    | .discover expectedInput expectedResult =>
        if event.phase == phase then
          let probeState ← ref.get
          let metaSnapshot ← liftM Meta.saveState
          try
            let result? ← applyReplayEvent? input event ref
            match result? with
            | none =>
                -- Discovery probes are observational until the historical
                -- input/result pair agrees.  Preserve no premise cursor,
                -- failure, or metavariable effects from a failed site.
                liftM metaSnapshot.restore
                ref.set probeState
            | some result =>
                if Expr.equal result.expr input then
                  -- A structurally unchanged result is not a successful
                  -- application site and must not advance the ordinal.
                  liftM metaSnapshot.restore
                  ref.set probeState
                else
                  let observed := probeState.siteCount + 1
                  let inputMatches ← replayExprMatches? input expectedInput
                  let resultMatches ← replayExprMatches? result.expr expectedResult
                  if inputMatches && resultMatches then
                    let after ← ref.get
                    ref.set {
                      after with
                        next := state.next + 1
                        siteCount := 0
                        premiseNext := 0
                        premiseFailure? := none
                        discoveredOrdinals := after.discoveredOrdinals.push observed
                    }
                    return .visit result
                  else
                    -- This was a changing, exact-premise site, but not the
                    -- historical event.  Commit only its ordinal progress.
                    liftM metaSnapshot.restore
                    ref.set {
                      probeState with
                        siteCount := observed
                        premiseNext := 0
                        premiseFailure? := none
                    }
          catch ex =>
            liftM metaSnapshot.restore
            ref.set probeState
            throw ex
  if phase == .pre && (← hasUncommandedReduction input) then
    throwError "simp_explicit encountered a reducible iota or native projection without an explicit reduction command"
  return .continue

private def runReplay (target : Expr) (events : Array ReplayEvent) : TacticM (Simp.Result × ReplayState) := do
  let congrTheorems ← getSimpCongrTheorems
  -- Traversal must be operationally inert.  In particular, the underlying
  -- simplifier may not beta/zeta/iota/project on the certificate's behalf;
  -- those state changes are available only through explicit replay events.
  -- The pinned traversal needs iota enabled to expose matcher applications to
  -- the pre hook.  `replayMethod` rejects any such reduction that is not
  -- consumed by an explicit command before `reduceStep` can perform it.
  let replayConfig := { Simp.neutralConfig with iota := true }
  let ctx ← Simp.mkContext (config := replayConfig)
    (simpTheorems := {}) (congrTheorems := congrTheorems)
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

private def freshPremiseBindingName (premiseIndex : Nat) (used : Array Name) : MetaM Name := do
  let lctx ← getLCtx
  let mut suffix := 0
  while true do
    let base := s!"h_premise_{premiseIndex + 1}"
    let candidate := Name.mkSimple (if suffix == 0 then base else s!"{base}_{suffix}")
    if (lctx.findFromUserName? candidate).isNone && !used.contains candidate then
      return candidate
    suffix := suffix + 1
  throwError "unreachable generated premise binding name search"

private def localRenamePlan (lctx : LocalContext) : MetaM (Array LocalRenamePlan) := do
  let mut found : NameSet := {}
  let mut reverseCandidates : Array LocalDecl := #[]
  let n := lctx.numIndices
  -- This is the same reverse scan used by `rename_i`: shadowed names are
  -- selected from newest to oldest, then restored to local-context order for
  -- the generated source argument list.
  for i in *...n do
    let j := n - i - 1
    match lctx.getAt? j with
    | none => pure ()
    | some localDecl =>
        if localDecl.isImplementationDetail then
          continue
        let inaccessible := localDecl.userName.isInaccessibleUserName ||
          localDecl.userName.hasMacroScopes
        let shadowed := found.contains localDecl.userName
        if inaccessible || shadowed then
          reverseCandidates := reverseCandidates.push localDecl
        found := found.insert localDecl.userName
  let candidates := reverseCandidates.reverse
  let mut usedNames : NameSet := {}
  for i in *...n do
    match lctx.getAt? i with
    | some localDecl =>
        -- Compare generated source names with both hygienic and printable
        -- forms so a macro-scoped declaration cannot collide after source
        -- rendering erases its scopes.
        usedNames := usedNames.insert localDecl.userName
        usedNames := usedNames.insert localDecl.userName.eraseMacroScopes
    | none => pure ()
  let mut result := #[]
  for localDecl in candidates do
    let base := s!"h_explicit_{localDecl.index + 1}"
    let mut suffix := 0
    let mut generatedName := Name.mkSimple base
    while usedNames.contains generatedName do
      suffix := suffix + 1
      generatedName := Name.mkSimple s!"{base}_{suffix}"
    result := result.push {
      contextIndex := localDecl.index
      fvarId := localDecl.fvarId
      generatedName
    }
    usedNames := usedNames.insert generatedName
    usedNames := usedNames.insert generatedName.eraseMacroScopes
  return result

private def renamedLocalContext (lctx : LocalContext)
    (plan : Array LocalRenamePlan) : LocalContext :=
  plan.foldl (fun current rename => current.setUserName rename.fvarId rename.generatedName) lctx

private def localRenameInfos (plan : Array LocalRenamePlan) : Array LocalRenameInfo :=
  plan.map fun rename => {
    contextIndex := rename.contextIndex
    generatedName := rename.generatedName.toString
  }

private def localRenamePrefix (plan : Array LocalRenamePlan) : String :=
  if plan.isEmpty then
    ""
  else
    let entries := plan.map fun rename =>
      s!"{rename.contextIndex} => {rename.generatedName}"
    s!"simp_explicit_rename [{String.intercalate ", " entries.toList}]\n"

private def exactLocalRenames (renames : Array (Nat × Name)) : TacticM Unit :=
  withMainContext do
    let mvarId ← getMainGoal
    let mvarDecl ← mvarId.getDecl
    let mut lctx := mvarDecl.lctx
    for (contextIndex, requestedName) in renames do
      let generatedName := requestedName.eraseMacroScopes
      let some localDecl := lctx.getAt? contextIndex
        | throwError "simp_explicit_rename: local-context index {contextIndex} is absent"
      if localDecl.isImplementationDetail then
        throwError "simp_explicit_rename: local-context index {contextIndex} is an implementation detail"
      if localDecl.userName.eraseMacroScopes == generatedName then
        continue
      for other in lctx do
        if other.fvarId != localDecl.fvarId &&
            other.userName.eraseMacroScopes == generatedName then
          throwError "simp_explicit_rename: name '{generatedName}' is already used by local-context index {other.index}"
      lctx := lctx.setUserName localDecl.fvarId generatedName
    let mvarNew ← Meta.mkFreshExprMVarAt lctx mvarDecl.localInstances mvarDecl.type
      mvarDecl.kind mvarDecl.userName mvarDecl.numScopeArgs
    mvarId.assign mvarNew
    replaceMainGoal [mvarNew.mvarId!]

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
    let replay ← recordedReplayEvent event .next
    let (result, state) ← runReplay event.input #[replay]
    if state.next == 1 && (← isDefEq result.expr event.result.expr) then
      return some replay
  catch _ =>
    return none
  return none

private def nestedPremiseProof? (premise : RecordedPremise) :
    TacticM (Option (Expr × String)) := do
  if premise.origins.size != 1 then
    return none
  try
    withoutModifyingState do
      let proposition0 ← instantiateMVars premise.proposition
      let authoritativeProof ← instantiateMVars premise.proof
      let proofType ← instantiateMVars (← inferType authoritativeProof)
      let proposition := if proposition0.hasMVar then proofType else proposition0
      let result : Simp.Result := { expr := mkConst ``True }
      let event : RecordedEvent := {
        tick := 1
        phase := .post
        input := proposition
        step := .done result
        result
        origins := premise.origins
        premises := #[]
      }
      let some replay ← compactReplayEvent? event
        | return none
      let (replayed, state) ← runReplay proposition #[replay]
      unless state.next == 1 && replayed.expr.isTrue do
        return none
      let equality ← Simp.Result.getProof' proposition replayed
      let proof ← mkOfEqTrue equality
      let proof ← mkExpectedTypeHint proof proposition
      unless ← isDefEq (← inferType proof) proposition do
        return none
      let rule ← ruleText premise.origins[0]!
      return some (proof, s!"by\n  simp_explicit [{rule}]")
  catch _ =>
    return none

private def generatedPremiseBinding (premise : RecordedPremise)
    (premiseIndex : Nat) (usedNames : Array Name) :
    TacticM (GeneratedBinding × PremiseEncodingInfo) := do
  let authoritativeProof ← instantiateMVars premise.proof
  let proposition0 ← instantiateMVars premise.proposition
  let proofType ← instantiateMVars (← inferType authoritativeProof)
  let proposition := if proposition0.hasMVar then proofType else proposition0
  let authoritativeProof ← mkExpectedTypeHint authoritativeProof proposition
  unless ← isDefEq (← inferType authoritativeProof) proposition do
    throwError "recorded premise proof did not check against its proposition"
  let sourceNamespace := ((← Term.getDeclName?).map (·.getPrefix)).getD Name.anonymous
  let name ← freshPremiseBindingName premiseIndex usedNames
  let nested? ← nestedPremiseProof? premise
  let (bindingProof, typeText, proofText, kind, reason) ← match nested? with
    | some (nestedProof, proofText) =>
        -- Nested certificates are the primary representation. The checked
        -- proof remains in memory for replay, while source prints only the
        -- proposition type and the closed nested certificate. The proof may
        -- contain a copied-module private auxiliary that has no source form.
        let rendered ← ProofExport.renderType proposition (config := {
          sourceNamespace
        })
        pure (nestedProof, rendered.valueText, proofText, "premise_nested", none)
    | none =>
        let rendered ← ProofExport.render authoritativeProof (type? := some proposition) (config := {
          sourceNamespace
        })
        pure (authoritativeProof, rendered.typeText, rendered.valueText, "premise_term",
          some "nested_certificate_unavailable")
  let bytes := typeText.utf8ByteSize + proofText.utf8ByteSize
  let binding : GeneratedBinding := {
    name
    kind
    type := proposition
    proof := bindingProof
    typeText
    proofText
    bytes
  }
  return (binding, {
    kind
    reason
    bindingName := some name
    bytes
  })

private def isReflexiveResultEarly (expr : Expr) : MetaM Bool := do
  if expr.isTrue then
    return true
  if expr.isAppOfArity ``Eq 3 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  if expr.isAppOfArity ``Iff 2 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  return false

private def generatedProofBinding (input : Expr) (result : Simp.Result)
    (eventIndex : Nat) (phase : Phase) (usedNames : Array Name) :
    TacticM (GeneratedBinding × ReplayEvent) := do
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
    kind := "rewrite"
    type := relation
    proof
    typeText := rendered.typeText
    proofText := rendered.valueText
    bytes := rendered.typeText.utf8ByteSize + rendered.valueText.utf8ByteSize
  }
  let rules ← mkSimpTheoremFromExpr (.other name) #[] proof
    (post := phase == .post)
  let replay : ReplayEvent := {
    selector := .next
    phase
    rules
    source := (mkIdent name).raw
  }
  return (binding, replay)

private def generatedBinding (event : RecordedEvent) (eventIndex : Nat)
    (usedNames : Array Name) : TacticM (GeneratedBinding × ReplayEvent) :=
  generatedProofBinding event.input event.result eventIndex event.phase usedNames

private def indentSource (indent : String) (text : String) : String :=
  text.replace "\n" ("\n" ++ indent)

private def certificatePlanEventListText (events : Array EncodedEvent) : String :=
  Id.run do
    if events.isEmpty then
      return "[]"
    let mut lines := #["["]
    for index in *...events.size do
      let some event := events[index]? | continue
      let comma := if index + 1 < events.size then "," else ""
      let phase := if event.event.phase == .pre then "↓ " else ""
      let premises :=
        if event.premiseNames.isEmpty then
          ""
        else
          let names := event.premiseNames.map Name.toString
          s!" using [{String.intercalate ", " names.toList}]"
      lines := lines.push s!"  {selectorSource event.replay.selector}{phase}{event.ruleText}{premises}{comma}"
    lines := lines.push "]"
    return String.intercalate "\n" lines.toList

private def certificatePlanText (events : Array EncodedEvent)
    (bindings : Array GeneratedBinding) (leaveOpen := false) : String :=
  Id.run do
    let mut lines := #[]
    for binding in bindings do
      lines := lines.push s!"have {binding.name} : {indentSource "  " binding.typeText} :="
      lines := lines.push s!"  {indentSource "  " binding.proofText}"
    let eventList := certificatePlanEventListText events
    let command := if leaveOpen then "simp_explicit leave_open " else "simp_explicit "
    if bindings.isEmpty then
      return command ++ eventList
    lines := lines.push (command ++ eventList)
    return String.intercalate "\n" lines.toList

private def wholeResultPlanText (binding : GeneratedBinding) (leaveOpen := false) : String :=
  let declaration :=
    s!"have {binding.name} : {indentSource "  " binding.typeText} :="
  let proof := s!"  {indentSource "  " binding.proofText}"
  let command := if leaveOpen then "simp_explicit leave_open" else "simp_explicit"
  let replay := s!"{command} [↓ {binding.name}]"
  String.intercalate "\n" [declaration, proof, replay]

private inductive CertificateSelectorMode where
  | next
  | discover
  | ticks

private def reachesSearchedResult? (searchedResult replayedResult : Simp.Result) : TacticM Bool := do
  if searchedResult.expr.isTrue then
    isReflexiveResultEarly replayedResult.expr
  else
    isDefEq searchedResult.expr replayedResult.expr

private def buildEncodedEvents? (recorded : Array RecordedEvent)
    (initialUsedNames : Array Name := #[]) :
    TacticM (Option (Array EncodedEvent × Array GeneratedBinding × Array Name)) := do
  try
    -- Keep the trailing reflexive closure in generated plans: unlike the
    -- compact certificate count, materialized proof bodies need the explicit
    -- closure to finish the rewritten target.
    let count := recorded.size
    let mut encoded := #[]
    let mut bindings := #[]
    let mut usedNames := initialUsedNames
    for index in *...count do
      let some event := recorded[index]? | return none
      -- A named event may be under a traversal binder, so its isolated
      -- callback input is not necessarily replayable in the current local
      -- context.  Construct the named rule without claiming that this local
      -- probe validates it; the complete ordered program below remains the
      -- acceptance check.
      let replay? ← try
        some <$> recordedReplayEvent event .next
      catch _ =>
        pure none
      if let some replay := replay? then
        let rule ← match event.reduction with
          | some reduction => pure (reductionSource reduction event.phase)
          | none => do
              unless event.origins.size == 1 do
                throwError "simp_explicit cannot encode semantic event {index}: observed {event.origins.size} diagnostic origin candidates"
              ruleText event.origins[0]!
        let mut premiseNames := #[]
        let mut premiseEncodings := #[]
        for premiseIndex in *...event.premises.size do
          let some premise := event.premises[premiseIndex]? | return none
          let (binding, premiseEncoding) ← generatedPremiseBinding premise premiseIndex usedNames
          usedNames := usedNames.push binding.name
          bindings := bindings.push binding
          premiseNames := premiseNames.push binding.name
          premiseEncodings := premiseEncodings.push premiseEncoding
        encoded := encoded.push {
          event
          replay
          info := {
            kind := if event.reduction.isSome then "reduction" else "named_rule"
            reason := none
          }
          ruleText := rule
          premiseNames
          premiseEncodings
          binding? := none
        }
      else
        let reason ← fallbackReason event
        let (binding, replay) ← generatedBinding event index usedNames
        usedNames := usedNames.push binding.name
        bindings := bindings.push binding
        let premiseEncodings := event.premises.map fun _ => {
          kind := "embedded_proof"
          reason := some reason
          bindingName := none
          bytes := 0
        }
        encoded := encoded.push {
          event
          replay
          info := { kind := "generated_proof", reason := some reason }
          ruleText := binding.name.toString
          premiseEncodings
          binding? := some binding
        }
    return some (encoded, bindings, usedNames)
  catch _ =>
    return none

private def selectCertificateEvents? (target : Expr) (searchedResult : Simp.Result)
    (encoded : Array EncodedEvent) (mode : CertificateSelectorMode) :
    TacticM (Option (Array EncodedEvent)) := do
  try
    let selected ← match mode with
      | .next => pure encoded
      | .ticks =>
          pure <| encoded.map fun item =>
            { item with replay := { item.replay with selector := .tickPos item.event.tick } }
      | .discover =>
          let mut discoveryEvents := #[]
          for item in encoded do
            discoveryEvents := discoveryEvents.push {
              item.replay with
                selector := .discover item.event.input item.event.result.expr
            }
          let (_, discoveryState) ← runReplay target (discoveryEvents.map id)
          unless discoveryState.next == encoded.size do
            return none
          unless discoveryState.discoveredOrdinals.size == encoded.size do
            return none
          let mut selectors := #[]
          for ordinal in discoveryState.discoveredOrdinals do
            selectors := selectors.push (if ordinal == 1 then .next else .matchSite ordinal)
          let mut result := #[]
          for index in *...encoded.size do
            let some item := encoded[index]? | return none
            let some selector := selectors[index]? | return none
            result := result.push { item with replay := { item.replay with selector } }
          pure result
    let replayEvents := selected.map (·.replay)
    let (replayedResult, replayState) ← runReplay target replayEvents
    unless replayState.next == replayEvents.size do
      return none
    unless ← reachesSearchedResult? searchedResult replayedResult do
      return none
    return some selected
  catch _ =>
    return none

private def annotateSelectorInfo (events : Array EncodedEvent) : Array EncodedEvent :=
  events.map fun event => {
    event with
      info := {
        event.info with
          selectorKind := selectorKind? event.replay.selector
          selectorValue := selectorValue? event.replay.selector
      }
  }

private def buildCertificatePlan? (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) (initialUsedNames : Array Name := #[]) :
    TacticM (Option CertificatePlan) := do
  let some (baseEncoded, bindings, _) ← buildEncodedEvents? recorded initialUsedNames
    | return none
  for mode in #[CertificateSelectorMode.next, CertificateSelectorMode.discover,
      CertificateSelectorMode.ticks] do
    let some selected ← selectCertificateEvents? target searchedResult baseEncoded mode
      | continue
    let encoded := annotateSelectorInfo selected
    let leaveOpen ← if searchedResult.expr.isTrue then pure false else
      isReflexiveResultEarly searchedResult.expr
    let source := certificatePlanText encoded bindings leaveOpen
    let namedRuleEvents := encoded.foldl (fun n event =>
      if event.info.kind == "named_rule" then n + 1 else n) 0
    let generatedProofEvents := encoded.foldl (fun n event =>
      if event.info.kind == "generated_proof" then n + 1 else n) 0
    let generatedSimprocEvents := encoded.foldl (fun n event =>
      if event.info.reason == some "simproc" then n + 1 else n) 0
    let generatedSpecialEvents := encoded.foldl (fun n event =>
      if event.info.reason == some "special_rule" then n + 1 else n) 0
    let reductionEvents := encoded.foldl (fun n event =>
      if event.info.kind == "reduction" then n + 1 else n) 0
    let deltaReductionEvents := encoded.foldl (fun n event =>
      match event.event.reduction with
      | some { kind := .delta .. } => n + 1
      | _ => n) 0
    let generatedBindingBytes := bindings.foldl (fun n binding => n + binding.bytes) 0
    let premiseEncodings := encoded.foldl (fun result event => result ++ event.premiseEncodings) #[]
    let premiseBindingCount := premiseEncodings.foldl (fun n encoding =>
      if encoding.bindingName.isSome then n + 1 else n) 0
    let premiseBindingBytes := premiseEncodings.foldl (fun n encoding => n + encoding.bytes) 0
    let nestedPremiseBindings := premiseEncodings.foldl (fun n encoding =>
      if encoding.kind == "premise_nested" then n + 1 else n) 0
    let termPremiseBindings := premiseEncodings.foldl (fun n encoding =>
      if encoding.kind == "premise_term" then n + 1 else n) 0
    let mut nextSelectorCount := 0
    let mut matchSelectorCount := 0
    let mut tickSelectorCount := 0
    for event in encoded do
      match event.replay.selector with
      | .next => nextSelectorCount := nextSelectorCount + 1
      | .matchSite _ => matchSelectorCount := matchSelectorCount + 1
      | .tickPos _ => tickSelectorCount := tickSelectorCount + 1
      | .discover .. => pure ()
    return some {
      events := encoded
      bindings
      positions := tickSelectorCount > 0
      source
      metrics := {
        namedRuleEvents
        reductionEvents
        deltaReductionEvents
        generatedProofEvents
        generatedSimprocEvents
        generatedSpecialEvents
        generatedBindingCount := bindings.size
        generatedBindingBytes
        premiseBindingCount
        premiseBindingBytes
        nestedPremiseBindings
        termPremiseBindings
        nextSelectorCount
        matchSelectorCount
        tickSelectorCount
        totalCertificateBytes := source.utf8ByteSize
      }
    }
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
  let some plan ← buildCertificatePlan? input #[event] result
    | throwError "proof-result encoder could not validate an event replay"
  let some encoded := plan.events[0]?
    | throwError "proof-result encoder produced no event encoding"
  return {
    source := plan.source
    metrics := plan.metrics
    encodingKind := encoded.info.kind
    encodingReason := encoded.info.reason
  }

private def buildWholeResultPlan? (target : Expr) (searchedResult : Simp.Result)
    (initialUsedNames : Array Name := #[]) : TacticM (Option CertificatePlan) := do
  try
    let (binding, replay) ← generatedProofBinding target searchedResult 0 .pre initialUsedNames
    let (replayedResult, replayState) ← runReplay target #[replay]
    unless replayState.next == 1 do
      return none
    let reachesResult ← if searchedResult.expr.isTrue then
      isReflexiveResultEarly replayedResult.expr
    else
      isDefEq searchedResult.expr replayedResult.expr
    unless reachesResult do
      return none
    let leaveOpen ← if searchedResult.expr.isTrue then pure false else
      isReflexiveResultEarly searchedResult.expr
    let source := wholeResultPlanText binding leaveOpen
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

private def replaySimp (eventSyntax : Array Syntax) (closeReflexive := true) : TacticM Unit := withMainContext do
  let events ← eventSyntax.mapM elaborateEvent
  let mut previousTick? : Option Nat := none
  for event in events do
    match event.selector with
    | .tickPos position =>
        if let some previousTick := previousTick? then
          if previousTick >= position then
            throwErrorAt event.source "explicit traversal positions must be strictly increasing"
        previousTick? := some position
    | .next | .matchSite _ | .discover .. => pure ()
  let mvarId ← getMainGoal
  let target ← instantiateMVars (← mvarId.getType)
  let (result, state) ← runReplay target events
  unless state.next == events.size do
    match events[state.next]? with
    | some event =>
        match event.selector with
        | .tickPos position =>
            throwErrorAt event.source "simp_explicit ended before recorded traversal position {position}"
        | .matchSite ordinal =>
            throwErrorAt event.source
              "simp_explicit match ordinal {ordinal} not reached; observed {state.siteCount} successful sites"
        | .next =>
            match state.premiseFailure? with
            | some reason =>
                throwErrorAt event.source "simp_explicit {reason}; ordered simp rule did not match anywhere in the remaining traversal"
            | none =>
                throwErrorAt event.source "ordered simp rule did not match anywhere in the remaining traversal"
        | .discover .. =>
            throwErrorAt event.source "internal simp_explicit selector discovery leaked into source replay"
    | none =>
        throwError "simp_explicit replay cursor is inconsistent"
  applyResultToTarget mvarId target result closeReflexive

private def isReflexiveResult (expr : Expr) : MetaM Bool := do
  if expr.isTrue then
    return true
  if expr.isAppOfArity ``Eq 3 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  if expr.isAppOfArity ``Iff 2 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  return false

private def recordedReplayEvents (recorded : Array RecordedEvent)
    (selectors : Array ReplaySelector) : TacticM (Option (Array ReplayEvent)) := do
  let count := certificateEventCount recorded
  if selectors.size != count then
    return none
  let mut events := #[]
  for index in *...count do
    let some event := recorded[index]? | return none
    let some selector := selectors[index]? | return none
    events := events.push (← recordedReplayEvent event selector)
  return some events

private inductive ContextReplaySubject where
  | local (decl : LocalDecl)
  | target

private structure ContextReplayGroup where
  subject : ContextReplaySubject
  events : Array ReplayEvent
  source : Syntax

private structure PendingContextHypothesis where
  subjectIndex : Nat
  contextIndex : Nat
  fvarId : FVarId
  hypothesis : Hypothesis

private structure ContextRecordSubject where
  subject : ContextReplaySubject
  report : SubjectReport

private structure ContextSubjectTrace where
  subject : SubjectReport
  fvarId? : Option FVarId
  lctx : LocalContext
  initial : Expr
  result : Simp.Result
  state : RecorderState
  encodingInfos : Array EventEncodingInfo
  premiseEncodingInfos : Array (Array PremiseEncodingInfo)
  metrics : EncodingMetrics
  eventText : String
  bindings : Array GeneratedBinding
  transport : Option SubjectTransportReport
  transitionContinuity : Option TransitionContinuityReport

private def contextRecordSubject (fvarId : FVarId) : TacticM ContextRecordSubject := do
  let decl ← fvarId.getDecl
  return {
    subject := .local decl
    report := {
      kind := "local"
      name := some decl.userName.toString
      contextIndex := some decl.index
    }
  }

private def contextLocationSubjects (mvarId : MVarId) (location : Location) :
    TacticM (Array ContextRecordSubject) := do
  match location with
  | .targets hypotheses includeTarget =>
      let fvarIds ← getFVarIds hypotheses
      let mut result := #[]
      for fvarId in fvarIds do
        result := result.push (← contextRecordSubject fvarId)
      if includeTarget then
        result := result.push {
          subject := .target
          report := {
            kind := "target"
            name := some "target"
            contextIndex := none
          }
        }
      return result
  | .wildcard =>
      let fvarIds ← mvarId.getNondepPropHyps
      let mut result := #[]
      for fvarId in fvarIds do
        result := result.push (← contextRecordSubject fvarId)
      result := result.push {
        subject := .target
        report := {
          kind := "target"
          name := some "target"
          contextIndex := none
        }
      }
      return result

private def contextSubjectLabel : ContextReplaySubject → String
  | .local decl => decl.userName.toString
  | .target => "target"

private def elaborateContextGroups (groupSyntax : Array Syntax) : TacticM (Array ContextReplayGroup) := do
  let lctx ← getLCtx
  let mut groups := #[]
  let mut seenLocals : Array FVarId := #[]
  let mut targetSeen := false
  for h : index in *...groupSyntax.size do
    let groupStx := groupSyntax[index]
    match groupStx with
    | `(simpExplicitContextGroup| at $name:ident => [$events:simpExplicitEvent,*]) =>
        let events ← events.getElems.mapM elaborateEvent
        if name.getId == `target then
          if targetSeen then
            throwErrorAt groupStx "simp_explicit_context may contain `target` at most once"
          if index + 1 != groupSyntax.size then
            throwErrorAt groupStx "simp_explicit_context requires `target` to be the last group"
          groups := groups.push {
            subject := .target
            events
            source := groupStx
          }
          targetSeen := true
        else
          let some localDecl := lctx.findFromUserName? name.getId
            | throwErrorAt name "unknown local subject `{name.getId}`"
          if seenLocals.any (· == localDecl.fvarId) then
            throwErrorAt name "duplicate local subject `{name.getId}`"
          groups := groups.push {
            subject := .local localDecl
            events
            source := groupStx
          }
          seenLocals := seenLocals.push localDecl.fvarId
    | _ =>
        throwErrorAt groupStx "invalid simp_explicit_context group"
  return groups

private def runContextGroup (mvarId : MVarId) (group : ContextReplayGroup) :
    TacticM (Simp.Result × ReplayState) := do
  let subject := contextSubjectLabel group.subject
  try
    mvarId.withContext do
      let target ← match group.subject with
        | .local decl => instantiateMVars (← decl.fvarId.getType)
        | .target => instantiateMVars (← mvarId.getType)
      runReplay target group.events
  catch ex =>
    let detail ← liftM (m := BaseIO) ex.toMessageData.toString
    throwErrorAt group.source
      m!"simp_explicit_context at {subject} failed: {detail}"

private def applyContextTargetResult (mvarId : MVarId) (target : Expr)
    (result : Simp.Result) : MetaM (Option MVarId) := do
  if result.expr.isTrue then
    let proof ← match result.proof? with
      | some equality => mkOfEqTrue equality
      | none => pure (mkConst ``True.intro)
    mvarId.assign proof
    return none
  return some (← applySimpResultToTarget mvarId target result)

private def replayContext (groupSyntax : Array Syntax) : TacticM Unit := withMainContext do
  let groups ← elaborateContextGroups groupSyntax
  let mut mvarId ← getMainGoal
  let mut pending : Array PendingContextHypothesis := #[]
  let mut closed := false
  for h : index in *...groups.size do
    let group := groups[index]
    if closed then
      throwErrorAt group.source
        "simp_explicit_context group at {contextSubjectLabel group.subject} is unreachable after the goal closed"
    let (result, replayState) ← runContextGroup mvarId group
    unless replayState.next == group.events.size do
      let subject := contextSubjectLabel group.subject
      throwErrorAt group.source
        m!"simp_explicit_context at {subject} did not consume its complete event group " ++
          m!"(consumed {replayState.next}, expected {group.events.size})"
    match group.subject with
    | .local decl =>
        let localDecl ← mvarId.withContext do decl.fvarId.getDecl
        let type ← mvarId.withContext do instantiateMVars localDecl.type
        if result.proof?.isSome then
          if result.expr.isFalse && index + 1 < groups.size then
            throwErrorAt group.source
              "simp_explicit_context local result closed the goal before all groups were consumed"
          let applied? ← mvarId.withContext do
            applySimpResult mvarId (mkFVar decl.fvarId) type result
          match applied? with
          | none =>
              closed := true
          | some (value, type') =>
              pending := pending.push {
                subjectIndex := index
                contextIndex := localDecl.index
                fvarId := decl.fvarId
                hypothesis := {
                  userName := localDecl.userName
                  type := type'
                  value
                  binderInfo := localDecl.binderInfo
                  kind := localDecl.kind
                }
              }
        else if result.expr.isFalse then
          if index + 1 < groups.size then
            throwErrorAt group.source
              "simp_explicit_context local result closed the goal before all groups were consumed"
          mvarId.withContext do
            mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar decl.fvarId))
          closed := true
        else
          mvarId ← mvarId.withContext do
            mvarId.replaceLocalDeclDefEq decl.fvarId result.expr
          pure ()
    | .target =>
        let target ← mvarId.withContext do instantiateMVars (← mvarId.getType)
        let mvarId? ← mvarId.withContext do
          applyContextTargetResult mvarId target result
        match mvarId? with
        | none => closed := true
        | some mvarId' => mvarId := mvarId'
  if !closed then
    -- Keep the authored location order.  This mirrors the fvar order supplied
    -- to Lean's batch simp path; dependent staged hypotheses must not be
    -- silently reordered by their context indices.
    let (_, mvarId') ← mvarId.withContext do
      mvarId.assertHypotheses (pending.map (·.hypothesis))
    mvarId ← mvarId'.withContext do mvarId'.tryClearMany (pending.map (·.fvarId))
    replaceMainGoal [mvarId]
  else
    replaceMainGoal []

private def tickSelectors (recorded : Array RecordedEvent) : Array ReplaySelector := Id.run do
  let count := certificateEventCount recorded
  let mut selectors := #[]
  for index in *...count do
    if let some event := recorded[index]? then
      selectors := selectors.push (.tickPos event.tick)
  return selectors

private def nextSelectors (recorded : Array RecordedEvent) : Array ReplaySelector :=
  Array.replicate (certificateEventCount recorded) (.next : ReplaySelector)

private def discoverSelectors? (target : Expr) (recorded : Array RecordedEvent) :
    TacticM (Option (Array ReplaySelector)) := do
  try
    let count := certificateEventCount recorded
    let mut events := #[]
    for index in *...count do
      let some event := recorded[index]? | return none
      let replay ← recordedReplayEvent event (.discover event.input event.result.expr)
      events := events.push replay
    let (_, state) ← runReplay target events
    unless state.next == events.size && state.discoveredOrdinals.size == events.size do
      return none
    let mut selectors := #[]
    for ordinal in state.discoveredOrdinals do
      selectors := selectors.push (if ordinal == 1 then .next else .matchSite ordinal)
    return some selectors
  catch _ =>
    return none

private def canReplayWithSelectors (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) (selectors : Array ReplaySelector) : TacticM Bool := do
  try
    withoutModifyingState do
      let some events ← recordedReplayEvents recorded selectors | return false
      let (replayedResult, replayState) ← runReplay target events
      unless replayState.next == events.size do
        return false
      return ← reachesSearchedResult? searchedResult replayedResult
  catch _ =>
    return false

private def replayEncoding? (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) : TacticM (Option (Array ReplaySelector)) := do
  let next := nextSelectors recorded
  if ← canReplayWithSelectors target recorded searchedResult next then
    return some next
  if let some mixed ← discoverSelectors? target recorded then
    if ← canReplayWithSelectors target recorded searchedResult mixed then
      return some mixed
  let ticks := tickSelectors recorded
  if ← canReplayWithSelectors target recorded searchedResult ticks then
    return some ticks
  return none

/- Context subjects must retain a trailing reflexive-closure event.  Target
   certificates may omit it because their close-versus-leave-open behavior is
   explicit in the replay command. -/
private def contextRecordedReplayEvents (recorded : Array RecordedEvent)
    (selectors : Array ReplaySelector) : TacticM (Option (Array ReplayEvent)) := do
  if selectors.size != recorded.size then
    return none
  let mut events := #[]
  for index in *...recorded.size do
    let some event := recorded[index]? | return none
    let some selector := selectors[index]? | return none
    events := events.push (← recordedReplayEvent event selector)
  return some events

private def contextCanReplayWithSelectors (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) (selectors : Array ReplaySelector) : TacticM Bool := do
  try
    withoutModifyingState do
      let some events ← contextRecordedReplayEvents recorded selectors | return false
      let (replayedResult, replayState) ← runReplay target events
      unless replayState.next == events.size do
        return false
      return ← reachesSearchedResult? searchedResult replayedResult
  catch _ =>
    return false

private def contextReplayEncoding? (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) : TacticM (Option (Array ReplaySelector)) := do
  let next := Array.replicate recorded.size (.next : ReplaySelector)
  if ← contextCanReplayWithSelectors target recorded searchedResult next then
    return some next
  let ticks := recorded.map (fun event => .tickPos event.tick)
  if ← contextCanReplayWithSelectors target recorded searchedResult ticks then
    return some ticks
  return none

private def continuityReplayCount? (target : Expr) (recorded : Array RecordedEvent)
    (selectors : Array ReplaySelector) : TacticM (Option Nat) := do
  try
    withoutModifyingState do
      let some events ← contextRecordedReplayEvents recorded selectors | return none
      let (_, state) ← runReplay target events
      return some state.next
  catch _ =>
    return none

private def continuityPrefixReplay? (target : Expr) (recorded : Array RecordedEvent)
    (selectors : Array ReplaySelector) (prefixCount : Nat) : TacticM (Option Expr) := do
  if prefixCount == 0 then
    return some target
  if prefixCount > recorded.size || prefixCount > selectors.size then
    return none
  try
    let prefixRecorded := recorded.take prefixCount
    let prefixSelectors := selectors.take prefixCount
    let some events ← contextRecordedReplayEvents prefixRecorded prefixSelectors | return none
    let (result, state) ← runReplay target events
    unless state.next == prefixCount do
      return none
    return some result.expr
  catch _ =>
    return none

private def namedRuleReplayable? (event : RecordedEvent) : TacticM Bool := do
  try
    let some replay ← contextRecordedReplayEvents #[event] #[.next] | return false
    let (result, state) ← runReplay event.input replay
    unless state.next == 1 do
      return false
    match ← premiseDefEq? result.expr event.result.expr with
    | .ok equal => return equal
    | .error _ => return false
  catch _ =>
    return false

private structure DefEqSubexpression where
  expression : Expr
  path : Array String

private def expressionChildren (expression : Expr) : Array (String × Expr) :=
  match expression with
  | .app fn arg => #[ ("app.fn", fn), ("app.arg", arg) ]
  | .lam _ type body _ => #[ ("lam.type", type), ("lam.body", body) ]
  | .forallE _ type body _ => #[ ("forall.type", type), ("forall.body", body) ]
  | .letE _ type value body _ =>
      #[ ("let.type", type), ("let.value", value), ("let.body", body) ]
  | .mdata _ expression => #[ ("mdata.value", expression) ]
  | .proj _ _ expression => #[ ("proj.value", expression) ]
  | _ => #[]

/- Search outermost-first so a large closed subject is preferred to a binder
   body.  Binder bodies can contain loose bvars when visited as standalone
   expressions; such candidates are skipped, while their closed children may
   still be inspected.  In particular, neither `isDefEq` nor fingerprints are
   attempted on a loose-bvar expression. -/
private partial def firstDefEqSubexpression? (subject expected : Expr)
    (path : Array String := #[]) (fuel : Nat := 256) : MetaM (Option DefEqSubexpression) := do
  if fuel == 0 || expected.hasLooseBVars then
    return none
  if !subject.hasLooseBVars && !Expr.equal subject expected then
    if ← diagnosticDefEq? subject expected then
      return some { expression := subject, path }
  for (label, child) in expressionChildren subject do
    if let some found ← firstDefEqSubexpression? child expected (path.push label) (fuel - 1) then
      return some found
  return none

private def originName? : Origin → Option Name
  | .decl name _ _ => some name
  | _ => none

private partial def containsConstant (expression : Expr) (name : String) : Bool :=
  match expression with
  | .const candidate _ => candidate.toString == name
  | .app fn arg => containsConstant fn name || containsConstant arg name
  | .lam _ type body _ => containsConstant type name || containsConstant body name
  | .forallE _ type body _ => containsConstant type name || containsConstant body name
  | .letE _ type value body _ =>
      containsConstant type name || containsConstant value name || containsConstant body name
  | .mdata _ expression => containsConstant expression name
  | .proj _ _ expression => containsConstant expression name
  | _ => false

private def transitionOperationHint (initial expected : Expr)
    (event : RecordedEvent) : (Option String × Option String × Option String) :=
  let initialHasFinsupp := containsConstant initial "Finsupp.sum"
  let expectedHasFinsupp := containsConstant expected "Finsupp.sum"
  let firstOriginIsMulSum := event.origins.any fun origin =>
    (originName? origin |>.map Name.toString).getD "" == "Finset.mul_sum"
  if initialHasFinsupp && !expectedHasFinsupp && firstOriginIsMulSum then
    (some "delta Finsupp.sum", some "delta", some "diagnostic_candidate")
  else if !Expr.equal initial expected then
    (some "definitional reduction", some "reduction", some "diagnostic_candidate")
  else
    (none, none, none)

/-- Replay a recorded prefix using the same selector order as a complete
certificate. The result is the complete target after that prefix and the
selectors that validated it. -/
private def replayRecorded? (target : Expr)
    (recorded : Array RecordedEvent) : TacticM (Option (Simp.Result × Array ReplaySelector)) := do
  let mut candidates := #[nextSelectors recorded]
  if let some mixed ← discoverSelectors? target recorded then
    candidates := candidates.push mixed
  candidates := candidates.push (tickSelectors recorded)
  for selectors in candidates do
    try
      let some events ← recordedReplayEvents recorded selectors | continue
      let (result, state) ← runReplay target events
      if state.next == events.size then
        return some (result, selectors)
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
  let printable ← withOptions
      (pp.mvars.set · false |>.set pp.mvars.levels.name false
        |>.set pp.fvars.anonymous.name false) <| ppExpr expression
  -- A free variable that is not present in the diagnostic reader can otherwise
  -- be rendered as Lean's internal `_fvar._` placeholder.  Keep that
  -- diagnostic stable and explicitly non-identity-bearing in persistent JSON;
  -- source rendering uses the original expression and is unaffected.
  let printable := (toString printable).replace "_fvar._" "<free-variable>"
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

/- Report the first event that no known selector can consume.  This is a
   bounded comparison aid for migration diagnostics; it does not infer or
   serialize a replay command. -/
private def buildTransitionContinuityCore? (target : Expr) (recorded : Array RecordedEvent)
    (recordedFinal : Expr) : TacticM (Option TransitionContinuityReport) := do
  let initialFingerprint ← exprFingerprint target
  if recorded.isEmpty then
    if Expr.equal target recordedFinal then
      return none
    let recordedFinalFingerprint ← exprFingerprint recordedFinal
    let replayedFinalFingerprint ← exprFingerprint target
    return some {
      firstUnconsumedEventIndex := some 0
      gapLocation := "after_events"
      noNamedSelectorCandidate := true
      nextConsumedCount := 0
      matchConsumedCount := 0
      tickConsumedCount := 0
      initialSubjectFingerprint := some initialFingerprint
      replayedPrefixFingerprint := some replayedFinalFingerprint
      expectedEventInputFingerprint := none
      expectedEventResultFingerprint := some recordedFinalFingerprint
      matchedSubexpressionFingerprint := none
      matchedSubexpressionPath := #[]
      recordedFinalStateFingerprint := some recordedFinalFingerprint
      replayedFinalStateFingerprint := some replayedFinalFingerprint
      expectedEventOrigins := #[]
      reasonCode := "missing_transition"
      operationHint := some "whole-subject transition"
      operationKind := some "transition"
      hintClassification := some "diagnostic_candidate"
    }
  let nextSelectors : Array ReplaySelector := Array.replicate recorded.size (.next : ReplaySelector)
  let matchSelectors : Array ReplaySelector := recorded.map
    (fun event => .discover event.input event.result.expr)
  let tickSelectors : Array ReplaySelector := recorded.map
    (fun event => .tickPos event.tick)
  let nextConsumedCount := (← continuityReplayCount? target recorded nextSelectors).getD 0
  let matchConsumedCount := (← continuityReplayCount? target recorded matchSelectors).getD 0
  let tickConsumedCount := (← continuityReplayCount? target recorded tickSelectors).getD 0
  let bestCount := max nextConsumedCount (max matchConsumedCount tickConsumedCount)
  let bestSelectors :=
    if nextConsumedCount >= matchConsumedCount && nextConsumedCount >= tickConsumedCount then
      nextSelectors
    else if matchConsumedCount >= tickConsumedCount then
      matchSelectors
    else
      tickSelectors
  if bestCount >= recorded.size then
    let some events ← contextRecordedReplayEvents recorded bestSelectors | return none
    let (replayedResult, replayState) ← runReplay target events
    unless replayState.next == recorded.size do
      return none
    if Expr.equal replayedResult.expr recordedFinal then
      return none
    let recordedFinalFingerprint ← exprFingerprint recordedFinal
    let replayedFinalFingerprint ← exprFingerprint replayedResult.expr
    return some {
      firstUnconsumedEventIndex := some recorded.size
      gapLocation := "after_events"
      noNamedSelectorCandidate := true
      nextConsumedCount
      matchConsumedCount
      tickConsumedCount
      initialSubjectFingerprint := some initialFingerprint
      replayedPrefixFingerprint := some replayedFinalFingerprint
      expectedEventInputFingerprint := none
      expectedEventResultFingerprint := some recordedFinalFingerprint
      matchedSubexpressionFingerprint := none
      matchedSubexpressionPath := #[]
      recordedFinalStateFingerprint := some recordedFinalFingerprint
      replayedFinalStateFingerprint := some replayedFinalFingerprint
      expectedEventOrigins := #[]
      reasonCode := "missing_transition"
      operationHint := some "trailing transition"
      operationKind := some "transition"
      hintClassification := some "diagnostic_candidate"
    }
  let firstUnconsumed := bestCount
  let some event := recorded[firstUnconsumed]? | return none
  let prefixExpr := (← continuityPrefixReplay? target recorded bestSelectors firstUnconsumed).getD target
  let matched? ← firstDefEqSubexpression? prefixExpr event.input
  let replayable ← namedRuleReplayable? event
  let hasDefinitionalEvidence := matched?.isSome
  let reasonCode := if replayable && hasDefinitionalEvidence then
      "missing_transition"
    else
      "unidentified_theorem_application"
  let (operationHint, operationKind, hintClassification) := if hasDefinitionalEvidence then
      let matchedExpression := match matched? with
        | some found => found.expression
        | none => prefixExpr
      transitionOperationHint matchedExpression event.input event
    else
      (none, none, none)
  let expectedFingerprint? ← if event.input.hasLooseBVars then
      pure none
    else
      some <$> exprFingerprint event.input
  let expectedResultFingerprint? ← if event.result.expr.hasLooseBVars then
      pure none
    else
      some <$> exprFingerprint event.result.expr
  let prefixFingerprint? ← if prefixExpr.hasLooseBVars then
      pure none
    else
      some <$> exprFingerprint prefixExpr
  let expectedOrigins ← event.origins.mapM fun origin => do
    return (← originCandidate origin).name
  return some {
    firstUnconsumedEventIndex := some firstUnconsumed
    gapLocation := if firstUnconsumed == 0 then "before_event" else "between_events"
    noNamedSelectorCandidate :=
      nextConsumedCount <= firstUnconsumed &&
      matchConsumedCount <= firstUnconsumed &&
      tickConsumedCount <= firstUnconsumed
    nextConsumedCount
    matchConsumedCount
    tickConsumedCount
    initialSubjectFingerprint := some initialFingerprint
    replayedPrefixFingerprint := prefixFingerprint?
    expectedEventInputFingerprint := expectedFingerprint?
    expectedEventResultFingerprint := expectedResultFingerprint?
    matchedSubexpressionFingerprint := ← matched?.mapM (fun found =>
      liftM (exprFingerprint found.expression))
    matchedSubexpressionPath := matched?.map (·.path) |>.getD #[]
    recordedFinalStateFingerprint := none
    replayedFinalStateFingerprint := none
    expectedEventOrigins := expectedOrigins
    reasonCode
    operationHint
    operationKind
    hintClassification
  }

private def diagnosticFallbackContinuity (target : Expr) (recorded : Array RecordedEvent)
    (recordedFinal : Expr) : TacticM (Option TransitionContinuityReport) := do
  let initialFingerprint? ← try
    some <$> exprFingerprint target
  catch _ =>
    pure none
  let finalFingerprint? ← try
    some <$> exprFingerprint recordedFinal
  catch _ =>
    pure none
  return some {
    firstUnconsumedEventIndex := some 0
    gapLocation := if recorded.isEmpty then "after_events" else "before_event"
    noNamedSelectorCandidate := true
    nextConsumedCount := 0
    matchConsumedCount := 0
    tickConsumedCount := 0
    initialSubjectFingerprint := initialFingerprint?
    replayedPrefixFingerprint := initialFingerprint?
    expectedEventInputFingerprint := none
    expectedEventResultFingerprint := none
    matchedSubexpressionFingerprint := none
    matchedSubexpressionPath := #[]
    recordedFinalStateFingerprint := finalFingerprint?
    replayedFinalStateFingerprint := initialFingerprint?
    expectedEventOrigins := #[]
    reasonCode := "unidentified_theorem_application"
    operationHint := none
    operationKind := none
    hintClassification := some "diagnostic_failure"
  }

/- Continuity is migration diagnostics only.  A failure in bounded replay or
   metadata inspection must never discard the recorder trace or fall through
   to passive execution; preserve a structured, conservative diagnosis. -/
private def buildTransitionContinuity? (target : Expr) (recorded : Array RecordedEvent)
    (recordedFinal : Expr) : TacticM (Option TransitionContinuityReport) := do
  try
    withoutModifyingState do
      buildTransitionContinuityCore? target recorded recordedFinal
  catch _ =>
    diagnosticFallbackContinuity target recorded recordedFinal

private def semanticEventReport (event : RecordedEvent)
    (encoding? : Option EventEncodingInfo := none)
    (premiseEncodings : Array PremiseEncodingInfo := #[])
    (subject : SubjectReport := {
      kind := "target"
      name := some "target"
      contextIndex := none
    }) : MetaM SemanticEventReport := do
  let origins ← event.origins.mapM originCandidate
  let premises ← event.premises.mapIdxM fun index premise => do
    let premiseOrigins ← premise.origins.mapM originCandidate
    let encoding? := premiseEncodings[index]?
    return {
      proposition := ← exprFingerprint premise.proposition
      proof := ← exprFingerprint premise.proof
      origins := premiseOrigins
      encodingKind := encoding?.map (·.kind)
      encodingReason := encoding?.bind (·.reason)
      bindingName := encoding?.bind (·.bindingName.map (·.toString))
    }
  return {
    subject
    tick := event.tick
    phase := if event.phase == .pre then "pre" else "post"
    input := ← exprFingerprint event.input
    step := stepName event.step
    result := ← exprFingerprint event.result.expr
    proof := ← event.result.proof?.mapM exprFingerprint
    reduction := event.reduction.map reductionReport
    origins
    premises
    encodingKind := encoding?.map (·.kind)
    encodingReason := encoding?.bind (·.reason)
    selectorKind := encoding?.bind (·.selectorKind)
    selectorValue := encoding?.bind (·.selectorValue)
  }

private def executionReport (target : Expr) (result : Simp.Result)
    (state : RecorderState) (executionIndex : Nat) (failureCategory? : Option String)
    (failureMessage? : Option String := none)
    (encodings : Array EventEncodingInfo := #[])
    (premiseEncodings : Array (Array PremiseEncodingInfo) := #[])
    (subjects : Array SubjectSummary := #[])
    (suggestion : String := "") (positionsNeeded : Bool := false)
    (encodingStatus : String := "validated")
    (recordingReason? : Option String := none)
    (encodingMetrics : EncodingMetrics := {})
    (encodingFallbackReason? : Option String := none)
    (localRenames : Array LocalRenameInfo := #[])
    (transitionContinuity? : Option TransitionContinuityReport := none)
    (admissibilityCode? : Option String := none)
    : MetaM ExecutionReport := do
  let targetSubject : SubjectReport := {
    kind := "target"
    name := some "target"
    contextIndex := none
  }
  let admissibility := computeOperationalAdmissibility encodingMetrics suggestion
    admissibilityCode? transitionContinuity?
  let targetSummary : SubjectSummary := {
    subject := targetSubject
    initial := ← exprFingerprint target
    result := ← exprFingerprint result.expr
    closesGoal := result.expr.isTrue
    eventCount := state.events.size
    transport := none
    transitionContinuity := transitionContinuity?
    operationalAdmissibility := admissibility
  }
  let subjects := if subjects.isEmpty then #[targetSummary] else subjects
  let acceptedCertificate := if admissibility.accepted then
      if suggestion.isEmpty then none else some suggestion
    else
      none
  let effectiveStatus := if admissibility.accepted then encodingStatus
    else if admissibility.code.startsWith "deferred_" then "deferred"
    else if admissibility.code == "unavailable" then "unavailable"
    else "inadmissible"
  return {
    attemptToken := ""
    executionIndex
    result := "succeeded"
    disposition := none
    certificate := acceptedCertificate
    acceptedCertificate
    legacyCertificate := if admissibility.accepted || suggestion.isEmpty then
        none else some suggestion
    legacyCertificateBytes := if admissibility.accepted then 0 else suggestion.utf8ByteSize
    certificateBytes := acceptedCertificate.map String.utf8ByteSize |>.getD 0
    certificateEventCount := certificateEventCount state.events
    positionsNeeded
    encodingStatus := effectiveStatus
    recordingReason := recordingReason?
    encoding := { encodingMetrics with totalCertificateBytes := suggestion.utf8ByteSize }
    encodingFallbackReason := encodingFallbackReason?
    operationallyAdmissible := admissibility.accepted
    operationalAdmissibility := admissibility
    transitionContinuity := transitionContinuity?
    localRenames
    closesGoal := result.expr.isTrue
    trace := ← state.events.mapIdxM fun index event =>
      semanticEventReport event encodings[index]? (premiseEncodings[index]?.getD #[])
        targetSubject
    subjects
    initialState := ← stateFingerprint target
    finalState := ← stateFingerprint result.expr
    failureCategory := failureCategory?
    failureMessage := failureMessage?
  }

private def exceptionText (ex : Exception) : TacticM String := do
  liftM (m := BaseIO) ex.toMessageData.toString

private def currentScopedFrame? : TacticM (Option ScopedFrame) := do
  let frameId := explicitLean.simpExplicit.bodyScopeFrame.get (← getOptions)
  if frameId == 0 then
    return none
  scopedRegistry.atomically do
    let registry ← get
    pure (registry.frames.find? (·.frameId == frameId))

private def replaceScopedFrame (frame : ScopedFrame) : TacticM Unit := do
  scopedRegistry.atomically do
    let registry ← get
    let some index := registry.frames.findIdx? (·.frameId == frame.frameId) | return
    set { registry with frames := registry.frames.set! index frame }

private def enterScopedFrame (scopeId : String) : TacticM Nat := do
  scopedRegistry.atomically do
    let registry ← get
    let frameId := registry.nextFrameId
    set ({
      nextFrameId := frameId + 1
      frames := registry.frames.push { frameId, scopeId, attempts := #[] }
    } : ScopedRegistry)
    pure frameId

private def leaveScopedFrame (frameId : Nat) : TacticM Unit := do
  scopedRegistry.atomically do
    let registry ← get
    set { registry with frames := registry.frames.filter (·.frameId != frameId) }

private def beginScopedAttempt? : TacticM (Option ScopedAttempt) := withMainContext do
  let some frame ← currentScopedFrame? | return none
  let occurrenceId := explicitLean.simpExplicit.occurrenceId.get (← getOptions)
  if occurrenceId.isEmpty then
    return none
  let main ← getMainGoal
  let decl ← main.getDecl
  let sentinelExpr ← mkFreshExprMVarAt decl.lctx decl.localInstances
    (mkConst ``True) MetavarKind.syntheticOpaque
  let reportRef ← IO.mkRef (none : Option RecordingReport)
  let attemptIndex := frame.attempts.size
  let attempt : ScopedAttempt := {
    frameId := frame.frameId
    occurrenceId
    attemptToken := s!"{frame.scopeId}:{occurrenceId}:{attemptIndex}"
    sentinel := sentinelExpr.mvarId!
    reportRef
  }
  replaceScopedFrame { frame with attempts := frame.attempts.push attempt }
  pure (some attempt)

private def commitScopedAttempt (attempt : ScopedAttempt) : TacticM Unit := do
  attempt.sentinel.assign (mkConst ``True.intro)

private def emitRecordingReport (simpStx reportStx : Syntax) (target : Expr) (state : RecorderState)
    (result? : Option Simp.Result) (suggestion : String) (positionsNeeded : Bool)
    (failureCategory? : Option String) (failureMessage? : Option String)
    (terminalOutcome? : Option String) (traceAvailable := true)
    (encodingStatus := "validated") (recordingReason? : Option String := none)
    (encodings : Array EventEncodingInfo := #[])
    (premiseEncodings : Array (Array PremiseEncodingInfo) := #[])
    (encodingMetrics : EncodingMetrics := {})
    (encodingFallbackReason? : Option String := none)
    (localRenames : Array LocalRenameInfo := #[])
    (transitionContinuity? : Option TransitionContinuityReport := none)
    (admissibilityCode? : Option String := none)
    (capture? : Option (IO.Ref (Option RecordingReport)) := none)
    (config? : Option Simp.Config := none) : TacticM Unit := do
  let declaration := (← Term.getDeclName?).map (·.toString) |>.getD "<unknown>"
  let originalSyntax := toString simpStx.prettyPrint
  let occurrenceId := explicitLean.simpExplicit.occurrenceId.get (← getOptions)
  let (closesGoal, finalTarget, executions) ← match result? with
    | some result =>
        let closesGoal := result.expr.isTrue
        let execution ← executionReport target result state 0 failureCategory? failureMessage?
          encodings premiseEncodings (suggestion := suggestion)
            (positionsNeeded := positionsNeeded) (encodingStatus := encodingStatus)
            (recordingReason? := recordingReason?) (encodingMetrics := encodingMetrics)
            (encodingFallbackReason? := encodingFallbackReason?) (localRenames := localRenames)
            (transitionContinuity? := transitionContinuity?)
            (admissibilityCode? := admissibilityCode?)
        pure (closesGoal, result.expr, #[execution])
    | none =>
        let finalTarget ← try
          instantiateMVars (← (← getMainGoal).getType)
        catch _ => pure target
        let execution : ExecutionReport := {
          attemptToken := ""
          executionIndex := 0
          result := "failed"
          disposition := none
          certificate := none
          acceptedCertificate := none
          legacyCertificate := none
          legacyCertificateBytes := 0
          certificateBytes := 0
          certificateEventCount := 0
          positionsNeeded := false
          encodingStatus := "unavailable"
          recordingReason := recordingReason?
          encoding := {}
          encodingFallbackReason := none
          operationallyAdmissible := false
          operationalAdmissibility := {
            accepted := false
            code := "unavailable"
            reason := some "unavailable"
          }
          transitionContinuity := none
          localRenames := #[]
          closesGoal := false
          trace := #[]
          subjects := #[{
            subject := {
              kind := "target"
              name := some "target"
              contextIndex := none
            }
            initial := ← exprFingerprint target
            result := ← exprFingerprint finalTarget
            closesGoal := false
            eventCount := 0
            transport := none
            transitionContinuity := none
            operationalAdmissibility := {
              accepted := false
              code := "unavailable"
              reason := some "unavailable"
            }
          }]
          initialState := ← stateFingerprint target
          finalState := ← stateFingerprint finalTarget
          failureCategory := failureCategory?
          failureMessage := failureMessage?
        }
        pure (false, finalTarget, #[execution])
  let initialState ← stateFingerprint target
  let finalState ← stateFingerprint finalTarget
  let acceptedCertificate := executions[0]?.bind (·.acceptedCertificate)
  let report : RecordingReport := {
    schema := reportSchema
    schemaVersion := reportSchemaVersion
    kind := "simp_explicit.recording"
    occurrenceId
    bodyScopeId := none
    declaration
    originalSyntax
    configuration := simpConfigurationReport simpStx config?
    closesGoal
    traceLength := state.events.size
    certificateEventCount := certificateEventCount state.events
    positionsNeeded
    certificateBytes := executions[0]?.map (·.certificateBytes) |>.getD 0
    certificate := executions[0]?.bind (·.certificate) |>.getD ""
    acceptedCertificate
    legacyCertificate := executions[0]?.bind (·.legacyCertificate)
    legacyCertificateBytes := executions[0]?.map (·.legacyCertificateBytes) |>.getD 0
    executions
    terminalOutcome := terminalOutcome?
    failureCategory := failureCategory?
    failureMessage := failureMessage?
    traceAvailable
    encodingStatus := executions[0]?.map (·.encodingStatus) |>.getD encodingStatus
    recordingReason := recordingReason?
    encoding := { encodingMetrics with totalCertificateBytes := suggestion.utf8ByteSize }
    encodingFallbackReason := encodingFallbackReason?
    operationallyAdmissible := executions[0]?.map (·.operationallyAdmissible) |>.getD false
    operationalAdmissibility := executions[0]?.map (·.operationalAdmissibility) |>.getD {
      accepted := false
      code := "unavailable"
      reason := some "unavailable"
    }
    transitionContinuity := executions[0]?.bind (·.transitionContinuity)
    localRenames
    validation := some {
      schemaVersion := reportSchemaVersion
      certificate := if acceptedCertificate.isSome then some 0 else none
      initialState
      finalState
    }
  }
  match capture? with
  | some capture => capture.set (some report)
  | none => logInfoAt reportStx m!"EXPLICIT_LEAN_SIMP_REPORT {(toJson report).compress}"

private def passiveOriginalSimp (simpStx reportStx : Syntax) (target : Expr)
    (category : String) (detail : String)
    (capture? : Option (IO.Ref (Option RecordingReport)) := none)
    (config? : Option Simp.Config := none) : TacticM Unit := do
  let state : RecorderState := {}
  try
    evalSimp simpStx
  catch ex =>
    let failureDetail ← exceptionText ex
    try
      emitRecordingReport simpStx reportStx target state none "" false
        (some "original_failure") (some failureDetail) none false "unavailable"
        (some failureDetail) (capture? := capture?) (config? := config?)
    catch _ => pure ()
    throw ex
  let finalTarget ← try
    instantiateMVars (← (← getMainGoal).getType)
  catch _ =>
    pure (mkConst ``True)
  let result : Simp.Result := { expr := finalTarget }
  try
    let admissibilityCode? := if category == "deferred_simproc" then
        some "deferred_simproc"
      else if category == "deferred_custom_discharger" then
        some "deferred_custom_discharger"
      else
        none
    emitRecordingReport simpStx reportStx target state (some result) "" false
      (some category) (some detail) none false "unavailable" (some detail)
      (admissibilityCode? := admissibilityCode?)
      (capture? := capture?) (config? := config?)
    catch ex =>
      logWarningAt reportStx m!"passive simp recording report failed: {← exceptionText ex}"

private def namedEncodingInfos (events : Array RecordedEvent)
    (selectors : Array ReplaySelector)
    (includeTrailingReflexive : Bool := false) : Array EventEncodingInfo := Id.run do
  let count := if includeTrailingReflexive then events.size else certificateEventCount events
  let mut result := #[]
  for index in *...count do
    let selector := selectors[index]?.getD .next
    let kind := match events[index]? with
      | some event => if event.reduction.isSome then "reduction" else "named_rule"
      | none => "named_rule"
    result := result.push {
      kind
      reason := none
      selectorKind := selectorKind? selector
      selectorValue := selectorValue? selector
    }
  return result

private def planEncodingInfos (plan : CertificatePlan) : Array EventEncodingInfo :=
  plan.events.map (·.info)

private def planPremiseEncodingInfos (plan : CertificatePlan) :
    Array (Array PremiseEncodingInfo) :=
  plan.events.map (·.premiseEncodings)

private structure ContextSubjectEncoding where
  eventText : String
  bindings : Array GeneratedBinding
  encodingInfos : Array EventEncodingInfo
  premiseEncodingInfos : Array (Array PremiseEncodingInfo)
  metrics : EncodingMetrics
  fallbackReason? : Option String
  positionsNeeded : Bool
  transitionContinuity? : Option TransitionContinuityReport

private structure ContextEncodingBundle where
  traces : Array ContextSubjectTrace
  bindings : Array GeneratedBinding
  metrics : EncodingMetrics
  fallbackReason? : Option String
  positionsNeeded : Bool

private structure ContextReportBundle where
  initialLctx : LocalContext
  finalLctx : LocalContext
  traces : Array ContextSubjectTrace
  bindings : Array GeneratedBinding
  metrics : EncodingMetrics
  fallbackReason? : Option String
  positionsNeeded : Bool
  suggestion : String
  localRenames : Array LocalRenameInfo

private def contextRenameName? (subject : SubjectReport)
    (plan : Array LocalRenamePlan) : Option Name :=
  subject.contextIndex.bind fun contextIndex =>
    plan.find? (fun rename => rename.contextIndex == contextIndex) |>.map (·.generatedName)

private def renamedLocalContextByFVars (lctx : LocalContext)
    (renames : Array (FVarId × Name)) : LocalContext :=
  renames.foldl (fun current (fvarId, name) => current.setUserName fvarId name) lctx

private def contextReportRenamePairs (traces : Array ContextSubjectTrace)
    (resultingFVars : Array (Option FVarId)) (plan : Array LocalRenamePlan) :
    Array (FVarId × Name) := Id.run do
  let mut pairs : Array (FVarId × Name) := #[]
  for h : index in *...traces.size do
    let trace := traces[index]
    let some generatedName := contextRenameName? trace.subject plan | continue
    if let some fvarId := trace.fvarId? then
      pairs := pairs.push (fvarId, generatedName)
    if let some (some resultingFVar) := resultingFVars[index]? then
      pairs := pairs.push (resultingFVar, generatedName)
  return pairs

private def contextTransportTraces (traces : Array ContextSubjectTrace)
    (resultingFVars : Array (Option FVarId)) (finalLctx : LocalContext) :
    Array ContextSubjectTrace :=
  traces.mapIdx fun index trace =>
    match trace.fvarId?, trace.subject.contextIndex, trace.subject.name with
    | some fvarId, some contextIndex, some originalName =>
        let resultingId? := match resultingFVars[index]? with
          | some id? => id?
          | none => none
        let resulting? := resultingId?.bind (fun id => finalLctx.find? id)
        { trace with
          transport := some {
            originalContextIndex := contextIndex
            originalName := some originalName
            resultingContextIndex := resulting?.map (·.index)
            resultingName := resulting?.map (·.userName.toString)
            originalCleared := finalLctx.find? fvarId |>.isNone
          } }
    | _, _, _ => trace

private def addEncodingMetrics (lhs rhs : EncodingMetrics) : EncodingMetrics := {
  mode := if lhs.mode == "event" && rhs.mode == "event" then "event" else "context"
  presentationChangeCount := lhs.presentationChangeCount + rhs.presentationChangeCount
  namedRuleEvents := lhs.namedRuleEvents + rhs.namedRuleEvents
  reductionEvents := lhs.reductionEvents + rhs.reductionEvents
  deltaReductionEvents := lhs.deltaReductionEvents + rhs.deltaReductionEvents
  generatedProofEvents := lhs.generatedProofEvents + rhs.generatedProofEvents
  generatedSimprocEvents := lhs.generatedSimprocEvents + rhs.generatedSimprocEvents
  generatedSpecialEvents := lhs.generatedSpecialEvents + rhs.generatedSpecialEvents
  wholeResultProofCount := lhs.wholeResultProofCount + rhs.wholeResultProofCount
  generatedBindingCount := lhs.generatedBindingCount + rhs.generatedBindingCount
  generatedBindingBytes := lhs.generatedBindingBytes + rhs.generatedBindingBytes
  premiseBindingCount := lhs.premiseBindingCount + rhs.premiseBindingCount
  premiseBindingBytes := lhs.premiseBindingBytes + rhs.premiseBindingBytes
  nestedPremiseBindings := lhs.nestedPremiseBindings + rhs.nestedPremiseBindings
  termPremiseBindings := lhs.termPremiseBindings + rhs.termPremiseBindings
  nextSelectorCount := lhs.nextSelectorCount + rhs.nextSelectorCount
  matchSelectorCount := lhs.matchSelectorCount + rhs.matchSelectorCount
  tickSelectorCount := lhs.tickSelectorCount + rhs.tickSelectorCount
  totalCertificateBytes := lhs.totalCertificateBytes + rhs.totalCertificateBytes
}

private def scopedDisposition (attempt : ScopedAttempt) : TacticM String := do
  try
    if ← attempt.sentinel.isAssigned then
      pure "committed"
    else
      pure "backtracked"
  catch _ =>
    pure "backtracked"

private def scopedOccurrenceGroups (attempts : Array ScopedAttempt) :
    Array (String × Array ScopedAttempt) := Id.run do
  let mut groups : Array (String × Array ScopedAttempt) := #[]
  for attempt in attempts do
    match groups.findIdx? (fun group => group.1 == attempt.occurrenceId) with
    | some index =>
        let group := groups[index]!
        groups := groups.set! index (group.1, group.2.push attempt)
    | none =>
        groups := groups.push (attempt.occurrenceId, #[attempt])
  return groups

private def scopedAggregateReport (scopeId occurrenceId : String)
    (attempts : Array ScopedAttempt) : TacticM (Option RecordingReport) := do
  let mut reports : Array RecordingReport := #[]
  let mut executions : Array ExecutionReport := #[]
  for attempt in attempts do
    let disposition ← scopedDisposition attempt
    let report? ← attempt.reportRef.get
    match report? with
    | none => pure ()
    | some report =>
        reports := reports.push report
        for execution in report.executions do
          executions := executions.push {
            execution with
              attemptToken := attempt.attemptToken
              executionIndex := executions.size
              disposition := some disposition
          }
  let some firstReport := reports[0]? | return none
  if executions.isEmpty then
    return none
  let successful := executions.filter (·.result == "succeeded")
  let mut aggregateEncoding : EncodingMetrics := {}
  let mut traceLength := 0
  let mut certificateEventCount := 0
  let mut positionsNeeded := false
  let mut traceAvailable := false
  for execution in executions do
    aggregateEncoding := addEncodingMetrics aggregateEncoding execution.encoding
    traceLength := traceLength + execution.trace.size
    certificateEventCount := certificateEventCount + execution.certificateEventCount
    positionsNeeded := positionsNeeded || execution.positionsNeeded
    traceAvailable := traceAvailable || !execution.trace.isEmpty
  let committedSuccessful := successful.filter (·.disposition == some "committed")
  let closesGoal := !committedSuccessful.isEmpty && committedSuccessful.all (·.closesGoal)
  let singleSuccessful? := if successful.size == 1 then successful[0]? else none
  let certificate := singleSuccessful?.bind (·.certificate) |>.getD ""
  let certificateBytes := singleSuccessful?.map (·.certificateBytes) |>.getD 0
  let legacyCertificate := singleSuccessful?.bind (·.legacyCertificate)
  let legacyCertificateBytes := singleSuccessful?.map (·.legacyCertificateBytes) |>.getD 0
  let encodingStatus := singleSuccessful?.map (·.encodingStatus) |>.getD
    (if successful.size > 1 then "body_rewrite_required" else "unavailable")
  let recordingReason := match singleSuccessful? with
    | some execution => execution.recordingReason
    | none => if successful.size > 1 then some "multiple_dynamic_executions" else none
  let encodingFallbackReason := singleSuccessful?.bind (·.encodingFallbackReason)
  let localRenames := singleSuccessful?.map (·.localRenames) |>.getD #[]
  let validation := if successful.size == 1 then firstReport.validation else none
  let aggregateAdmissibility := if successful.size > 1 then {
      accepted := false
      code := "source_rewrite_required"
      reason := some "multiple_dynamic_executions"
    } else
    singleSuccessful?.map (·.operationalAdmissibility) |>.getD {
      accepted := false
      code := "unavailable"
      reason := some "unavailable"
    }
  let report : RecordingReport := {
    firstReport with
      schemaVersion := reportSchemaVersion
      occurrenceId
      bodyScopeId := some scopeId
      closesGoal
      traceLength
      certificateEventCount
      positionsNeeded
      certificateBytes
      certificate
      acceptedCertificate := if aggregateAdmissibility.accepted then
        singleSuccessful?.bind (·.acceptedCertificate) else none
      legacyCertificate
      legacyCertificateBytes
      executions
      traceAvailable
      encodingStatus
      operationallyAdmissible := aggregateAdmissibility.accepted
      operationalAdmissibility := aggregateAdmissibility
      transitionContinuity := singleSuccessful?.bind (·.transitionContinuity)
      recordingReason
      /- Metrics belong to the dynamic executions.  In particular, a
         multi-execution occurrence has no single top-level certificate, but
         its aggregate byte/count metrics remain auditable. -/
      encoding := aggregateEncoding
      encodingFallbackReason
      localRenames
      validation
  }
  pure (some report)

private def publishScopedFrame (scopeId : String) (frameId : Nat)
    (reportStx : Syntax) : TacticM Unit := do
  let some frame ← scopedRegistry.atomically do
    let registry ← get
    pure (registry.frames.find? (·.frameId == frameId))
    | return
  for group in scopedOccurrenceGroups frame.attempts do
    let some report ← scopedAggregateReport scopeId group.1 group.2 | continue
    logInfoAt reportStx m!"EXPLICIT_LEAN_SIMP_REPORT {(toJson report).compress}"
  leaveScopedFrame frameId

private structure FirstOwnerReport where
  ownerId : String
  proof : String
  proofBytes : Nat
  closesGoal : Bool
  deriving ToJson

private structure BodyScopeProofReport where
  scopeId : String
  proof : Option String
  proofBytes : Nat
  closesGoal : Bool
  failureReason : Option String
  localRenames : Array LocalRenameInfo := #[]
  deriving ToJson

private def runFirstOwnerScope (ownerId : String) (body : Syntax) (reportStx : Syntax) :
    TacticM Unit := withMainContext do
  let main ← getMainGoal
  let initialTarget ← instantiateMVars (← main.getType)
  let sourceNamespace := ((← Term.getDeclName?).map (·.getPrefix)).getD Name.anonymous
  evalTactic body
  let goals ← getGoals
  unless goals.isEmpty do
    return
  unless ← main.isAssigned do
    return
  let some proof ← getExprMVarAssignment? main | return
  let proof ← instantiateMVars proof
  let proofType ← inferType proof
  unless ← isDefEq proofType initialTarget do
    return
  let some rendered ← try
      main.withContext do
        some <$> ProofExport.render proof (type? := some initialTarget) {
          sourceNamespace
        }
    catch _ =>
      pure none
    | return
  let report : FirstOwnerReport := {
    ownerId
    proof := rendered.valueText
    proofBytes := rendered.valueText.utf8ByteSize
    closesGoal := true
  }
  logInfoAt reportStx m!"EXPLICIT_LEAN_FIRST_OWNER_REPORT {(toJson report).compress}"

private def selectorMetrics (events : Array RecordedEvent)
    (selectors : Array ReplaySelector) : EncodingMetrics := Id.run do
  let mut nextSelectorCount := 0
  let mut matchSelectorCount := 0
  let mut tickSelectorCount := 0
  let mut namedRuleEvents := 0
  let mut reductionEvents := 0
  let mut deltaReductionEvents := 0
  for index in *...selectors.size do
    let some selector := selectors[index]? | continue
    match selector with
    | .next => nextSelectorCount := nextSelectorCount + 1
    | .matchSite _ => matchSelectorCount := matchSelectorCount + 1
    | .tickPos _ => tickSelectorCount := tickSelectorCount + 1
    | .discover .. => pure ()
    match events[index]? with
    | some event =>
        match event.reduction with
        | some reduction =>
            reductionEvents := reductionEvents + 1
            match reduction.kind with
            | .delta _ => deltaReductionEvents := deltaReductionEvents + 1
            | _ => pure ()
        | none => namedRuleEvents := namedRuleEvents + 1
    | none => namedRuleEvents := namedRuleEvents + 1
  return {
    namedRuleEvents
    reductionEvents
    deltaReductionEvents
    nextSelectorCount
    matchSelectorCount
    tickSelectorCount
  }

private def contextSubjectEncoding? (target : Expr)
    (state : RecorderState) (result : Simp.Result) (usedNames : Array Name := #[]) :
    TacticM (Option (ContextSubjectEncoding × Array Name)) := do
  try
    if !state.events.any (·.premises.size > 0) then
      let includeTrailingReflexive := state.events.size > certificateEventCount state.events
      let selectors? ← if includeTrailingReflexive then
          contextReplayEncoding? target state.events result
        else
          replayEncoding? target state.events result
      if let some selectors := selectors? then
        let eventText ← certificateEventListText state.events selectors includeTrailingReflexive
        let infos := namedEncodingInfos state.events selectors includeTrailingReflexive
        let metrics := selectorMetrics state.events selectors
        return some ({
          eventText
          bindings := #[]
          encodingInfos := infos
          premiseEncodingInfos := state.events.map (fun _ => #[])
          metrics
          fallbackReason? := none
          positionsNeeded := metrics.tickSelectorCount > 0
          transitionContinuity? := none
        }, usedNames)
    let plan? ← match (← buildCertificatePlan? target state.events result usedNames) with
      | some plan => pure (some plan)
      | none => buildWholeResultPlan? target result usedNames
    let some plan := plan? | return none
    let continuity? ← if plan.metrics.mode == "event" &&
        plan.metrics.generatedProofEvents == 0 && plan.metrics.termPremiseBindings == 0 then
        pure none
      else if plan.metrics.generatedSimprocEvents > 0 then
        pure none
      else
        buildTransitionContinuity? target state.events result.expr
    let eventText := if plan.metrics.mode == "whole_result_proof" && plan.events.isEmpty then
      match plan.bindings[0]? with
      | some binding => s!"[↓ {binding.name}]"
      | none => "[]"
    else
      certificatePlanEventListText plan.events
    let allUsedNames := usedNames ++ plan.bindings.map (·.name)
    return some ({
      eventText
      bindings := plan.bindings
      encodingInfos := planEncodingInfos plan
      premiseEncodingInfos := planPremiseEncodingInfos plan
      metrics := plan.metrics
      fallbackReason? :=
        if plan.metrics.mode == "whole_result_proof" then some "presentation_gap" else none
      positionsNeeded := plan.positions
      transitionContinuity? := continuity?
    }, allUsedNames)
  catch _ =>
    return none

private def reencodeContextTraces? (traces : Array ContextSubjectTrace)
    (plan : Array LocalRenamePlan) : TacticM (Option ContextEncodingBundle) := do
  try
    let mut usedNames : Array Name := #[]
    let mut allBindings : Array GeneratedBinding := #[]
    let mut aggregateMetrics : EncodingMetrics := {}
    let mut fallbackReason? : Option String := none
    let mut positionsNeeded := false
    let mut renamedTraces : Array ContextSubjectTrace := #[]
    for trace in traces do
      let renamedLctx := renamedLocalContext trace.lctx plan
      let some (encoding, _) ← withLCtx' renamedLctx do
          contextSubjectEncoding? trace.initial trace.state trace.result usedNames
        | return none
      let subject := match contextRenameName? trace.subject plan with
        | some generatedName => { trace.subject with name := some generatedName.toString }
        | none => trace.subject
      usedNames := usedNames ++ encoding.bindings.map (·.name)
      allBindings := allBindings ++ encoding.bindings
      aggregateMetrics := addEncodingMetrics aggregateMetrics encoding.metrics
      fallbackReason? := fallbackReason?.or encoding.fallbackReason?
      positionsNeeded := positionsNeeded || encoding.positionsNeeded
      renamedTraces := renamedTraces.push {
        trace with
          subject
          lctx := renamedLctx
          encodingInfos := encoding.encodingInfos
          premiseEncodingInfos := encoding.premiseEncodingInfos
          metrics := encoding.metrics
          eventText := encoding.eventText
          bindings := encoding.bindings
          transitionContinuity := encoding.transitionContinuity?
        }
    return some {
      traces := renamedTraces
      bindings := allBindings
      metrics := aggregateMetrics
      fallbackReason?
      positionsNeeded
    }
  catch _ =>
    return none

private def emitContextRecordingReport (simpStx reportStx : Syntax)
    (initialTarget : Expr) (initialLctx : LocalContext)
    (finalTarget : Expr) (finalLctx : LocalContext)
    (subjects : Array ContextSubjectTrace) (suggestion : String)
    (positionsNeeded : Bool) (encodingMetrics : EncodingMetrics)
    (encodingFallbackReason? : Option String)
    (localRenames : Array LocalRenameInfo) (closesGoal : Bool)
    (capture? : Option (IO.Ref (Option RecordingReport)) := none)
    (config? : Option Simp.Config := none) : TacticM Unit := do
  let declaration := (← Term.getDeclName?).map (·.toString) |>.getD "<unknown>"
  let originalSyntax := toString simpStx.prettyPrint
  let occurrenceId := explicitLean.simpExplicit.occurrenceId.get (← getOptions)
  let initialState ← withLCtx' initialLctx do stateFingerprint initialTarget
  let finalState ← withLCtx' finalLctx do stateFingerprint finalTarget
  let transitionContinuity? := subjects.foldl
    (fun current subject => current.or subject.transitionContinuity) none
  let admissibility := computeOperationalAdmissibility encodingMetrics suggestion
    none transitionContinuity?
  let acceptedCertificate := if admissibility.accepted && !suggestion.isEmpty then
      some suggestion else none
  let effectiveStatus := if admissibility.accepted then
      if suggestion.isEmpty then "unavailable" else "validated"
    else if admissibility.code.startsWith "deferred_" then "deferred"
    else if admissibility.code == "unavailable" then "unavailable"
    else "inadmissible"
  let mut trace := #[]
  let mut summaries := #[]
  let mut totalCertificateEventCount := 0
  for subject in subjects do
    let reports ← withLCtx' subject.lctx do
      subject.state.events.mapIdxM fun index event =>
        semanticEventReport event subject.encodingInfos[index]?
          (subject.premiseEncodingInfos[index]?.getD #[]) subject.subject
    trace := trace ++ reports
    totalCertificateEventCount := totalCertificateEventCount + certificateEventCount subject.state.events
    let summary ← withLCtx' subject.lctx do
      pure {
        subject := subject.subject
        initial := ← exprFingerprint subject.initial
        result := ← exprFingerprint subject.result.expr
        closesGoal := ← isReflexiveResultEarly subject.result.expr
        eventCount := subject.state.events.size
        transport := subject.transport
        transitionContinuity := subject.transitionContinuity
        operationalAdmissibility := computeOperationalAdmissibility subject.metrics
          subject.eventText none subject.transitionContinuity
      }
    summaries := summaries.push summary
  let execution : ExecutionReport := {
    attemptToken := ""
    executionIndex := 0
    result := "succeeded"
    disposition := none
    certificate := acceptedCertificate
    acceptedCertificate
    legacyCertificate := if admissibility.accepted || suggestion.isEmpty then none else some suggestion
    legacyCertificateBytes := if admissibility.accepted then 0 else suggestion.utf8ByteSize
    certificateBytes := acceptedCertificate.map (·.utf8ByteSize) |>.getD 0
    certificateEventCount := totalCertificateEventCount
    positionsNeeded
    encodingStatus := effectiveStatus
    recordingReason := if suggestion.isEmpty then some "context certificate encoding was not validated" else none
    encoding := { encodingMetrics with totalCertificateBytes := suggestion.utf8ByteSize }
    encodingFallbackReason := encodingFallbackReason?
    operationallyAdmissible := admissibility.accepted
    operationalAdmissibility := admissibility
    transitionContinuity := transitionContinuity?
    localRenames
    closesGoal
    trace
    subjects := summaries
    initialState
    finalState
    failureCategory := none
    failureMessage := none
  }
  let report : RecordingReport := {
    schema := reportSchema
    schemaVersion := reportSchemaVersion
    kind := "simp_explicit.recording"
    occurrenceId
    bodyScopeId := none
    declaration
    originalSyntax
    configuration := simpConfigurationReport simpStx config?
    closesGoal
    traceLength := trace.size
    certificateEventCount := totalCertificateEventCount
    positionsNeeded
    certificateBytes := execution.certificateBytes
    certificate := execution.certificate |>.getD ""
    acceptedCertificate := execution.acceptedCertificate
    legacyCertificate := execution.legacyCertificate
    legacyCertificateBytes := execution.legacyCertificateBytes
    executions := #[execution]
    terminalOutcome := none
    failureCategory := none
    failureMessage := none
    traceAvailable := true
    encodingStatus := effectiveStatus
    recordingReason := if suggestion.isEmpty then some "context certificate encoding was not validated" else none
    encoding := { encodingMetrics with totalCertificateBytes := suggestion.utf8ByteSize }
    encodingFallbackReason := encodingFallbackReason?
    operationallyAdmissible := admissibility.accepted
    operationalAdmissibility := admissibility
    transitionContinuity := transitionContinuity?
    localRenames
    validation := some {
      schemaVersion := reportSchemaVersion
      certificate := if acceptedCertificate.isSome then some 0 else none
      initialState
      finalState
    }
  }
  match capture? with
  | some capture => capture.set (some report)
  | none => logInfoAt reportStx m!"EXPLICIT_LEAN_SIMP_REPORT {(toJson report).compress}"

private def contextCertificateText (subjects : Array ContextSubjectTrace)
    (bindings : Array GeneratedBinding) : String := Id.run do
  let mut lines := #[]
  for binding in bindings do
    lines := lines.push s!"have {binding.name} : {indentSource "  " binding.typeText} :="
    lines := lines.push s!"  {indentSource "  " binding.proofText}"
  if subjects.isEmpty then
    if lines.isEmpty then
      return "simp_explicit_context []"
    lines := lines.push "simp_explicit_context []"
    return String.intercalate "\n" lines.toList
  lines := lines.push "simp_explicit_context ["
  for index in *...subjects.size do
    let some subject := subjects[index]? | continue
    let comma := if index + 1 < subjects.size then "," else ""
    let name := subject.subject.name.getD "target"
    lines := lines.push s!"  at {name} => {subject.eventText}{comma}"
  lines := lines.push "]"
  return String.intercalate "\n" lines.toList

private def sameStateFingerprint (lhs rhs : StateFingerprint) : Bool :=
  toJson lhs == toJson rhs

/- Validate the complete source program, rather than just each subject's event
   plan, against a fresh goal carrying the captured initial local context.  The
   source is parsed and elaborated here so generated `have` bindings and the
   context tactic take the same path as a materialized replacement. -/
private def validateContextCertificate (source : String)
    (initialTarget : Expr) (initialLctx : LocalContext)
    (initialLocalInstances : LocalInstances)
    (actualClosed : Bool) (actualLctx : LocalContext) (actualTarget : Expr) :
    TacticM Bool := do
  try
    withoutModifyingState do
      let parsed ← match Parser.runParserCategory (← getEnv)
          `term s!"by\n{source}" with
        | .ok stx => pure stx
        | .error detail =>
            throwError m!"context certificate parse failed: {detail}"
      let `(term| by $seq:tacticSeq) := parsed
        | throwError "context certificate parser returned a non-tactic term"
      let cloneExpr ← withLCtx' initialLctx do
        mkFreshExprMVarAt initialLctx initialLocalInstances initialTarget
          MetavarKind.syntheticOpaque
      let cloneMVar := cloneExpr.mvarId!
      withLCtx' initialLctx do
        replaceMainGoal [cloneMVar]
        evalTactic seq.raw
      let goals ← getGoals
      let replayClosed := goals.isEmpty
      unless replayClosed == actualClosed do
        return false
      let replayTarget? ← match goals with
        | [goal] => some <$> goal.getType
        | _ => pure none
      let replayLctx ← match goals with
        | [goal] => some <$> (·.lctx) <$> goal.getDecl
        | _ => pure none
      if replayClosed then
        -- The source was parsed and run to completion on a fresh clone.  Once
        -- both executions close there is no remaining target to compare; the
        -- explicit closure result is the observable outcome.
        return true
      let some replayTarget := replayTarget? | return false
      let some replayLctx := replayLctx | return false
      let replayState ← withLCtx' replayLctx do stateFingerprint replayTarget
      let actualState ← withLCtx' actualLctx do stateFingerprint actualTarget
      return sameStateFingerprint replayState actualState
  catch _ =>
    return false

/-- Validate a target certificate, including an optional presentation `change`,
    against a fresh clone of the original goal.  This is intentionally kept
    separate from context validation: target certificates must not recreate a
    context fingerprint from a mutated mvar. -/
private def validateTargetCertificate (source : String)
    (initialTarget : Expr) (initialLctx : LocalContext)
    (initialLocalInstances : LocalInstances) (actualClosed : Bool)
    (actualTarget : Expr) : TacticM Bool := do
  try
    withoutModifyingState do
      let parsed ← match Parser.runParserCategory (← getEnv)
          `term s!"by\n{source}" with
        | .ok stx => pure stx
        | .error detail =>
            throwError m!"target certificate parse failed: {detail}"
      let `(term| by $seq:tacticSeq) := parsed
        | throwError "target certificate parser returned a non-tactic term"
      let cloneExpr ← withLCtx' initialLctx do
        mkFreshExprMVarAt initialLctx initialLocalInstances initialTarget
          MetavarKind.syntheticOpaque
      withLCtx' initialLctx do
        replaceMainGoal [cloneExpr.mvarId!]
        evalTactic seq.raw
      let goals ← getGoals
      let replayClosed := goals.isEmpty
      unless replayClosed == actualClosed do
        return false
      if replayClosed then
        return true
      let some replayGoal := goals[0]? | return false
      let replayTarget ← replayGoal.getType
      withLCtx' initialLctx do
        let replayState ← stateFingerprint replayTarget
        let actualState ← stateFingerprint actualTarget
        let same := sameStateFingerprint replayState actualState
        return same
  catch _ =>
    return false

private def instantiateRecordedResult (result : Simp.Result) : MetaM Simp.Result := do
  return {
    result with
      expr := ← instantiateMVars result.expr
      proof? := ← result.proof?.mapM instantiateMVars
  }

private def instantiateRecordedStep : Simp.Step → MetaM Simp.Step
  | .done result => return .done (← instantiateRecordedResult result)
  | .visit result => return .visit (← instantiateRecordedResult result)
  | .continue result? => return .continue (← result?.mapM instantiateRecordedResult)

private def instantiateRecordedState (state : RecorderState) : MetaM RecorderState := do
  return {
    state with
      events := ← state.events.mapM fun event => do
        return {
          event with
            input := ← instantiateMVars event.input
            step := ← instantiateRecordedStep event.step
            result := ← instantiateRecordedResult event.result
            premises := ← event.premises.mapM fun premise => do
              return {
                premise with
                  proposition := ← instantiateMVars premise.proposition
                  proof := ← instantiateMVars premise.proof
              }
        }
  }

private def buildPresentationPlan? (target : Expr) (mvarId : MVarId)
    (state : RecorderState) (result : Simp.Result)
    (runPresentation : Expr → TacticM (Option (Expr × Array (Expr × Expr)))) :
    TacticM (Option CertificatePlan) := do
  try
    let some (wholeCandidate, candidates) ← runPresentation target
      | return none
    -- The presentation pass may realize several proofless transitions before
    -- returning its whole-goal expression.  Remove only matching proofless
    -- semantic events; proof-bearing events with the same boundary remain
    -- authoritative replay obligations.
    let replayEvents := state.events.filter fun event =>
      !candidates.any (fun candidate =>
        Expr.equal event.input candidate.1 &&
        Expr.equal event.result.expr candidate.2 &&
        event.result.proof?.isNone)
    let some candidatePlan ← buildCertificatePlan? wholeCandidate replayEvents result
      | return none
    let sourceNamespace := ((← Term.getDeclName?).map (·.getPrefix)).getD Name.anonymous
    let rendered ← ProofExport.renderType wholeCandidate (config := {
      sourceNamespace
    })
    -- ProofExport may use a shared `let` sequence.  Parenthesize it after
    -- `change` so the semicolon remains inside the term rather than being
    -- parsed as a tactic-sequence separator.
    let renderedValueText := indentSource "  " rendered.valueText
    let source := s!"change (\n{renderedValueText}\n)\n{candidatePlan.source}"
    let decl ← mvarId.getDecl
    let actualClosed := result.expr.isTrue
    unless ← validateTargetCertificate source target decl.lctx decl.localInstances
        actualClosed result.expr do
      return none
    let metrics := {
      candidatePlan.metrics with
        mode := "presentation_change"
        presentationChangeCount := 1
        totalCertificateBytes := source.utf8ByteSize
    }
    return some {
      candidatePlan with
        source
        metrics
        positions := candidatePlan.positions
    }
  catch _ =>
    return none

private def encodeRecording? (target : Expr) (mvarId : MVarId)
    (state : RecorderState) (result : Simp.Result)
    (runAndRecord : Expr → TacticM (Simp.Result × RecorderState))
    (presentation? : Option (Expr → TacticM (Option (Expr × Array (Expr × Expr)))) := none) :
    TacticM (Option EncodingAttempt) := do
  try
    -- Premise-bearing events must go through the certificate-plan encoder so
    -- their closed provider bindings are printed next to the rule.  The flat
    -- path has no source representation for `using [...]`.
    -- A non-closing, zero-event simplification may still have performed
    -- proofless unfolding in the theorem engine.  It must bypass the flat
    -- empty program: `simp_explicit []` would leave the authored target
    -- unchanged even though the following tactic body observes the unfolded
    -- result.
    let actualClosed := result.expr.isTrue
    let needsPresentation :=
      state.events.isEmpty && !actualClosed && !Expr.equal target result.expr
    let flatEncoding? ← if needsPresentation || state.events.any (·.premises.size > 0) then
      pure none
    else
      replayEncoding? target state.events result
    let mut suggestion := ""
    let mut encodingInfos : Array EventEncodingInfo := #[]
    let mut premiseEncodingInfos : Array (Array PremiseEncodingInfo) := #[]
    let mut encodingMetrics : EncodingMetrics := {}
    let mut encodingFallbackReason? : Option String := none
    let mut transitionContinuity? : Option TransitionContinuityReport := none
    let mut positionsNeeded := flatEncoding?.getD #[] |>.any isTickSelector
    if let some flatSelectors := flatEncoding? then
      let leaveOpen ← if actualClosed then pure false else isReflexiveResult result.expr
      suggestion := ← certificateText state.events flatSelectors leaveOpen
      encodingInfos := namedEncodingInfos state.events flatSelectors
      premiseEncodingInfos := state.events.map (fun _ => #[])
      encodingMetrics := selectorMetrics state.events flatSelectors
    else
      -- Prefer the compact event program whenever it validates.  The
      -- presentation pass is a bounded fallback for targets whose current
      -- syntax cannot be replayed from the original presentation.
      let mut plan? ← if needsPresentation then
        pure none
      else
        buildCertificatePlan? target state.events result
      if plan?.isNone then
        plan? ← match presentation? with
          | some runPresentation =>
              buildPresentationPlan? target mvarId state result runPresentation
          | none => pure none
      if plan?.isNone then
        plan? ← buildWholeResultPlan? target result
      let some plan := plan?
        | return none
      suggestion := plan.source
      encodingInfos := planEncodingInfos plan
      premiseEncodingInfos := planPremiseEncodingInfos plan
      encodingMetrics := plan.metrics
      encodingFallbackReason? :=
        if plan.metrics.mode == "whole_result_proof" ||
            plan.metrics.mode == "presentation_change" then some "presentation_gap" else none
      positionsNeeded := plan.positions
      if plan.metrics.generatedSimprocEvents == 0 &&
          (plan.metrics.mode != "event" || plan.metrics.termPremiseBindings > 0) then
        transitionContinuity? ← buildTransitionContinuity? target state.events result.expr

    -- Search a bounded certificate-program graph breadth first. A node is the
    -- current target plus the phases that produced it. Its outgoing edges
    -- replay an exact prefix and then normalize. Recording afresh at every
    -- node is essential: normalization can expose a different exact suffix.
    if flatEncoding?.isSome then
      let mut frontier : Array (Expr × Array String) := #[(target, #[])]
      let mut stateCount := 1
      for depth in *...(maxMixedNormalizerPhases + 1) do
        let mut nextFrontier := #[]
        for (input, previousPhases) in frontier do
          let (nodeResult, nodeState) ← runAndRecord input
          let closes := nodeResult.expr.isTrue
          let reachesResult ← if closes then pure true else if result.expr.isTrue then
            pure false
          else
            isDefEq nodeResult.expr result.expr
          if reachesResult then
            if let some selectors ← replayEncoding? input nodeState.events nodeResult then
              let mut phases := previousPhases
              if certificateEventCount nodeState.events > 0 then
                let leaveOpen ← if nodeResult.expr.isTrue then pure false else
                  isReflexiveResult nodeResult.expr
                phases := phases.push
                  (← certificateText nodeState.events selectors leaveOpen)
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
                  let some (prefixResult, prefixSelectors) ← replayRecorded? input prefixEvents
                    | return none
                  -- A replay phase would close the goal before the normalizer ran.
                  if prefixCount > 0 && prefixResult.expr.isTrue then
                    return none
                  let normalized ← Normalize.categoryTarget mvarId prefixResult.expr
                  if Expr.equal prefixResult.expr normalized.expr then
                    return none
                  let mut phases := previousPhases
                  if prefixCount > 0 then
                    let leaveOpen ← if prefixResult.expr.isTrue then pure false else
                      isReflexiveResult prefixResult.expr
                    phases := phases.push
                      (← certificateText prefixEvents prefixSelectors leaveOpen)
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
    return some {
      suggestion
      encodingInfos
      premiseEncodingInfos
      encodingMetrics
      encodingFallbackReason?
      positionsNeeded
      transitionContinuity?
    }
  catch _ =>
    return none

private def recordContextSimp (simpStx reportStx : Syntax) (location : Location)
    (passive : Bool := false)
    (capture? : Option (IO.Ref (Option RecordingReport)) := none) :
    TacticM Unit := withMainContext do
  let initialMVarId ← getMainGoal
  let initialTarget ← instantiateMVars (← initialMVarId.getType)
  let initialDecl ← initialMVarId.getDecl
  let initialLctx := initialDecl.lctx
  let initialLocalInstances := initialDecl.localInstances
  let subjects ← contextLocationSubjects initialMVarId location
  let some { ctx, simprocs, dischargeWrapper, .. } ← try
      some <$> mkSimpContext simpStx (eraseLocal := false)
    catch ex =>
      throw ex
    | throwError "simp_explicit recorder failed to construct a context simp context"
  let runRecorded := fun (input : Expr) (subjectCtx : Simp.Context) => do
    let ref ← IO.mkRef ({} : RecorderState)
    let result ← dischargeWrapper.with fun discharge? => do
      let methods := recordingMethods ref simprocs discharge?
      withOptions (·.setBool `diagnostics true) do
        return (← Simp.mainCore input subjectCtx (methods := methods)).1
    let result ← instantiateRecordedResult result
    return (result, ← instantiateRecordedState (← ref.get))
  let mut current := initialMVarId
  let mut pending : Array PendingContextHypothesis := #[]
  let mut traces : Array ContextSubjectTrace := #[]
  let mut usedNames : Array Name := #[]
  let mut allBindings : Array GeneratedBinding := #[]
  let mut aggregateMetrics : EncodingMetrics := {}
  let mut fallbackReason? : Option String := none
  let mut positionsNeeded := false
  let mut closed := false
  let mut closedLctx? : Option LocalContext := none
  let mut resultingFVars : Array (Option FVarId) := Array.replicate subjects.size none
  let mut ordinaryEncodingFailed := false
  for h : index in *...subjects.size do
    let subject := subjects[index]
    if closed then
      throwError "simp_explicit recorder encountered a subject after the goal closed"
    match subject.subject with
    | .local decl =>
        let (subjectLctx, localDecl, type, result, state, encoding?) ← current.withContext do
          let localDecl ← decl.fvarId.getDecl
          let subjectLctx ← getLCtx
          let type ← instantiateMVars localDecl.type
          let subjectCtx := ctx.setSimpTheorems
            (ctx.simpTheorems.eraseTheorem (.fvar decl.fvarId))
          let (result, state) ← runRecorded type subjectCtx
          let encoding? ← contextSubjectEncoding? type state result usedNames
          return (subjectLctx, localDecl, type, result, state, encoding?.map (·.fst))
        let encoding := encoding?.getD {
          eventText := "[]"
          bindings := #[]
          encodingInfos := #[]
          premiseEncodingInfos := #[]
          metrics := {}
          fallbackReason? := some "context_subject_encoding"
          positionsNeeded := false
          transitionContinuity? := ← buildTransitionContinuity? type state.events result.expr
        }
        if encoding?.isNone then
          ordinaryEncodingFailed := true
        usedNames := usedNames ++ encoding.bindings.map (·.name)
        allBindings := allBindings ++ encoding.bindings
        aggregateMetrics := addEncodingMetrics aggregateMetrics encoding.metrics
        fallbackReason? := fallbackReason?.or encoding.fallbackReason?
        positionsNeeded := positionsNeeded || encoding.positionsNeeded
        traces := traces.push {
          subject := subject.report
          fvarId? := some decl.fvarId
          lctx := subjectLctx
          initial := type
          result
          state
          encodingInfos := encoding.encodingInfos
          premiseEncodingInfos := encoding.premiseEncodingInfos
          metrics := encoding.metrics
          eventText := encoding.eventText
          bindings := encoding.bindings
          transport := none
          transitionContinuity := encoding.transitionContinuity?
        }
        if result.proof?.isSome then
          if result.expr.isFalse && index + 1 < subjects.size then
            throwErrorAt reportStx
              "simp_explicit recorder local result closed the goal before all subjects were consumed"
          let applied? ← current.withContext do
            applySimpResult current (mkFVar decl.fvarId) type result
          match applied? with
          | none =>
              closedLctx? := some (← current.getDecl).lctx
              closed := true
          | some (value, type') =>
              resultingFVars := resultingFVars.set! index none
              pending := pending.push {
                subjectIndex := index
                contextIndex := localDecl.index
                fvarId := decl.fvarId
                hypothesis := {
                  userName := localDecl.userName
                  type := type'
                  value
                  binderInfo := localDecl.binderInfo
                  kind := localDecl.kind
                }
              }
        else if result.expr.isFalse then
          if index + 1 < subjects.size then
            throwErrorAt reportStx
              "simp_explicit recorder local result closed the goal before all subjects were consumed"
          current.withContext do
            current.assign (← mkFalseElim (← current.getType) (mkFVar decl.fvarId))
          closedLctx? := some (← current.getDecl).lctx
          closed := true
        else
          current ← current.withContext do
            current.replaceLocalDeclDefEq decl.fvarId result.expr
          resultingFVars := resultingFVars.set! index (some decl.fvarId)
    | .target =>
        let (subjectLctx, target, result, state, encoding?) ← current.withContext do
          let subjectLctx ← getLCtx
          let target ← instantiateMVars (← current.getType)
          let (result, state) ← runRecorded target ctx
          let encoding? ← contextSubjectEncoding? target state result usedNames
          return (subjectLctx, target, result, state, encoding?.map (·.fst))
        let encoding := encoding?.getD {
          eventText := "[]"
          bindings := #[]
          encodingInfos := #[]
          premiseEncodingInfos := #[]
          metrics := {}
          fallbackReason? := some "context_subject_encoding"
          positionsNeeded := false
          transitionContinuity? := ← buildTransitionContinuity? target state.events result.expr
        }
        if encoding?.isNone then
          ordinaryEncodingFailed := true
        usedNames := usedNames ++ encoding.bindings.map (·.name)
        allBindings := allBindings ++ encoding.bindings
        aggregateMetrics := addEncodingMetrics aggregateMetrics encoding.metrics
        fallbackReason? := fallbackReason?.or encoding.fallbackReason?
        positionsNeeded := positionsNeeded || encoding.positionsNeeded
        traces := traces.push {
          subject := subject.report
          fvarId? := none
          lctx := subjectLctx
          initial := target
          result
          state
          encodingInfos := encoding.encodingInfos
          premiseEncodingInfos := encoding.premiseEncodingInfos
          metrics := encoding.metrics
          eventText := encoding.eventText
          bindings := encoding.bindings
          transport := none
          transitionContinuity := encoding.transitionContinuity?
        }
        let current? ← current.withContext do
          applyContextTargetResult current target result
        match current? with
        | none =>
            closedLctx? := some (← current.getDecl).lctx
            closed := true
        | some current' => current := current'
  if !closed then
    let (assertedFVars, asserted) ← current.withContext do
      current.assertHypotheses (pending.map (·.hypothesis))
    for h : index in *...pending.size do
      if let some pendingHypothesis := pending[index]? then
        if let some assertedFVar := assertedFVars[index]? then
          resultingFVars := resultingFVars.set! pendingHypothesis.subjectIndex (some assertedFVar)
    current ← asserted.withContext do asserted.tryClearMany (pending.map (·.fvarId))
  let finalLctx ← if closed then
      pure (closedLctx?.getD (← current.getDecl).lctx)
    else
      pure (← current.getDecl).lctx
  let finalTarget ← if closed then pure (mkConst ``True) else current.getType
  let ordinaryTraces := contextTransportTraces traces resultingFVars finalLctx
  let ordinarySuggestion := contextCertificateText traces allBindings
  let ordinaryValid ← validateContextCertificate ordinarySuggestion initialTarget initialLctx
      initialLocalInstances closed finalLctx finalTarget
  let stableRenamePlan ← localRenamePlan initialLctx
  let report : ContextReportBundle ← if !ordinaryEncodingFailed && ordinaryValid &&
      stableRenamePlan.isEmpty then
      pure {
        initialLctx
        finalLctx
        traces := ordinaryTraces
        bindings := allBindings
        metrics := aggregateMetrics
        fallbackReason?
        positionsNeeded
        suggestion := ordinarySuggestion
        localRenames := #[]
      }
    else if passive then
      -- Passive recording must not turn a recorder validation gap into a
      -- copied-module failure.  Preserve the observed traces and continuity
      -- diagnostics, but withhold every candidate source; the caller runs the
      -- original `simp` exactly once after this speculative pass.
      pure {
        initialLctx
        finalLctx
        traces := ordinaryTraces
        bindings := #[]
        metrics := aggregateMetrics
        fallbackReason? := fallbackReason?.or (some "context_certificate_unavailable")
        positionsNeeded
        suggestion := ""
        localRenames := #[]
      }
    else do
      let renamePlan := stableRenamePlan
      if renamePlan.isEmpty then
        throwErrorAt reportStx
          "simp_explicit recorder could not encode or validate the complete context certificate"
      let some encoded ← reencodeContextTraces? traces renamePlan
        | throwErrorAt reportStx
            "simp_explicit recorder could not encode the context under stable local names"
      let renamedInitialLctx := renamedLocalContext initialLctx renamePlan
      let renamePairs := contextReportRenamePairs traces resultingFVars renamePlan
      let renamedFinalLctx := renamedLocalContextByFVars
        (renamedLocalContext finalLctx renamePlan) renamePairs
      let renamedTraces := contextTransportTraces encoded.traces resultingFVars renamedFinalLctx
      let suggestion := localRenamePrefix renamePlan ++
        contextCertificateText encoded.traces encoded.bindings
      unless ← validateContextCertificate suggestion initialTarget initialLctx
          initialLocalInstances closed renamedFinalLctx finalTarget do
        throwErrorAt reportStx
          "simp_explicit recorder could not validate the renamed context certificate"
      pure {
        initialLctx := renamedInitialLctx
        finalLctx := renamedFinalLctx
        traces := renamedTraces
        bindings := encoded.bindings
        metrics := encoded.metrics
        fallbackReason? := encoded.fallbackReason?
        positionsNeeded := encoded.positionsNeeded
        suggestion
        localRenames := localRenameInfos renamePlan
      }
  let finalMetrics := { report.metrics with totalCertificateBytes := report.suggestion.utf8ByteSize }
  let reportContinuity? := report.traces.foldl
    (fun current trace => current.or trace.transitionContinuity) none
  let reportAdmissibility := computeOperationalAdmissibility finalMetrics report.suggestion
    none reportContinuity?
  unless explicitLean.simpExplicit.passive.get (← getOptions) do
    if reportAdmissibility.accepted then
      logInfoAt reportStx m!"Try this deterministic replay:\n{report.suggestion}"
  let shouldReport := passive || explicitLean.simpExplicit.report.get (← getOptions)
  if shouldReport then
    emitContextRecordingReport simpStx reportStx initialTarget report.initialLctx finalTarget
      report.finalLctx report.traces report.suggestion report.positionsNeeded finalMetrics
      report.fallbackReason? report.localRenames closed capture? (some ctx.config)
  if closed then
    replaceMainGoal []
  else
    replaceMainGoal [current]

private def passiveContextSimp (simpStx reportStx : Syntax) (target : Expr)
    (location : Location)
    (capture? : Option (IO.Ref (Option RecordingReport)) := none) : TacticM Unit := do
  let reportRef ← IO.mkRef (none : Option RecordingReport)
  let recordingError? ← try
    withoutModifyingState do
      recordContextSimp simpStx reportStx location true (some reportRef)
      pure none
  catch ex =>
    some <$> exceptionText ex
  match recordingError? with
  | some detail =>
      passiveOriginalSimp simpStx reportStx target "context" detail capture?
  | none =>
      let report? ← reportRef.get
      if report?.isNone then
        passiveOriginalSimp simpStx reportStx target "context"
          "passive context recorder produced no report" capture?
      else
        match capture? with
        | some capture => capture.set report?
        | none =>
            let some report := report? | throwError "passive context recorder produced no report"
            logInfoAt reportStx m!"EXPLICIT_LEAN_SIMP_REPORT {(toJson report).compress}"
        try
          evalSimp simpStx
        catch ex =>
          let detail ← exceptionText ex
          try
            emitRecordingReport simpStx reportStx target {} none "" false
              (some "context_original_failure") (some detail) none false "unavailable"
              (some detail) (capture? := capture?)
          catch _ => pure ()
          throw ex

private def recordSimp (simpStx reportStx : Syntax) : TacticM Unit := withMainContext do
  unless simpStx.getKind == ``Lean.Parser.Tactic.simp do
    throwErrorAt simpStx "simp_explicit? currently accepts one `simp` tactic"
  let mvarId ← getMainGoal
  let target ← instantiateMVars (← mvarId.getType)
  let passive := explicitLean.simpExplicit.passive.get (← getOptions)
  let scopedAttempt? ← if passive then beginScopedAttempt? else pure none
  let scopedCapture? := scopedAttempt?.map (·.reportRef)
  let runScoped := fun (action : TacticM Unit) => do
    action
    if let some attempt := scopedAttempt? then
      commitScopedAttempt attempt
  if !simpStx[2].isNone then
    if passive then
      return ← runScoped (passiveOriginalSimp simpStx reportStx target "deferred_custom_discharger"
        "passive recorder preserves custom dischargers through the original tactic"
        scopedCapture?)
    else
      throwErrorAt simpStx[2] "simp_explicit? does not yet encode a custom discharger"
  if !simpStx[5].isNone then
    if passive then
      return ← runScoped (passiveContextSimp simpStx reportStx target
        (expandLocation simpStx[5][0]) scopedCapture?)
    else
      return ← recordContextSimp simpStx reportStx (expandLocation simpStx[5][0])
  let context? ← try
    some <$> mkSimpContext simpStx (eraseLocal := false)
  catch ex =>
    if passive then
      let detail ← exceptionText ex
      return ← runScoped (passiveOriginalSimp simpStx reportStx target "recording" detail
        scopedCapture?)
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
    let result ← instantiateRecordedResult result
    return (result, ← instantiateRecordedState (← ref.get))
  let recording? ← try
    some <$> runAndRecord target
  catch ex =>
    if passive then
      let detail ← exceptionText ex
      return ← runScoped (passiveOriginalSimp simpStx reportStx target "recording" detail
        scopedCapture? (some ctx.config))
    else
      throw ex
  let some (result, state) := recording?
    | throwError "simp_explicit recorder did not return a simplifier result"
  let presentationRunner := some (fun (input : Expr) =>
    presentationCandidate? input ctx simprocs state.events)
  let mut localRenames : Array LocalRenamePlan := #[]
  let mut reportLctx? : Option LocalContext := none
  let mut attempt? ← encodeRecording? target mvarId state result runAndRecord
    presentationRunner
  if attempt?.isNone then
    let renamePlan ← localRenamePlan (← mvarId.getDecl).lctx
    if !renamePlan.isEmpty then
      let mvarDecl ← mvarId.getDecl
      let renamedLctx := renamedLocalContext mvarDecl.lctx renamePlan
      let renamedAttempt? ← withLCtx' renamedLctx do
        encodeRecording? target mvarId state result runAndRecord presentationRunner
      if let some renamedAttempt := renamedAttempt? then
        localRenames := renamePlan
        reportLctx? := some renamedLctx
        attempt? := some renamedAttempt
      else
        -- If the already-recorded proof refers to private compiler-generated
        -- declarations, rerun the recorder only in a speculative mvar under
        -- the renamed context.  This mvar is never installed as the tactic's
        -- goal; the original result remains authoritative for proof-state
        -- application below.
        let speculativeAttempt? ← withoutModifyingState do
          withLCtx' renamedLctx do
            let some {
              ctx := renamedCtx
              simprocs := renamedSimprocs
              dischargeWrapper := renamedDischargeWrapper
              ..
            } ← try
              some <$> mkSimpContext simpStx (eraseLocal := false)
            catch _ =>
              pure none
            | return none
            let renamedRunAndRecord := fun (input : Expr) => do
              let ref ← IO.mkRef ({} : RecorderState)
              let result ← renamedDischargeWrapper.with fun discharge? => do
                let methods := recordingMethods ref renamedSimprocs discharge?
                withOptions (·.setBool `diagnostics true) do
                  return (← Simp.mainCore input renamedCtx (methods := methods)).1
              let result ← instantiateRecordedResult result
              return (result, ← instantiateRecordedState (← ref.get))
            let speculativeExpr ← mkFreshExprMVarAt renamedLctx mvarDecl.localInstances
              target MetavarKind.syntheticOpaque
            let speculativeMVarId := speculativeExpr.mvarId!
            let (speculativeResult, speculativeState) ← renamedRunAndRecord target
            let renamedPresentationRunner := some (fun (input : Expr) =>
              presentationCandidate? input renamedCtx renamedSimprocs speculativeState.events)
            encodeRecording? target speculativeMVarId speculativeState
              speculativeResult renamedRunAndRecord renamedPresentationRunner
        if let some speculativeAttempt := speculativeAttempt? then
          localRenames := renamePlan
          reportLctx? := some renamedLctx
          attempt? := some speculativeAttempt
  let some attempt := attempt?
    | if passive then
        return ← runScoped (passiveOriginalSimp simpStx reportStx target "recording"
          "proof-result fallback could not be validated" scopedCapture? (some ctx.config))
      else
        throwErrorAt reportStx "simp_explicit recorder cannot encode this simplification as a deterministic replay"
  let suggestion := localRenamePrefix localRenames ++ attempt.suggestion
  let encodingInfos := attempt.encodingInfos
  let premiseEncodingInfos := attempt.premiseEncodingInfos
  let encodingMetrics := attempt.encodingMetrics
  let encodingFallbackReason? := attempt.encodingFallbackReason?
  let transitionContinuity? := attempt.transitionContinuity?
  let operationalAdmissibility := computeOperationalAdmissibility encodingMetrics suggestion
    none transitionContinuity?
  let positionsNeeded := attempt.positionsNeeded
  let shouldReport := passive || explicitLean.simpExplicit.report.get (← getOptions)
  if shouldReport then
    -- Recording cannot assign a terminal outcome: `materialized` requires the
    -- coverage driver to compile the replacement in its complete body.
    let failureCategory? : Option String := none
    let terminalOutcome? : Option String := none
    let encodingStatus := if operationalAdmissibility.accepted then
        if suggestion.isEmpty then "unavailable" else "validated"
      else if operationalAdmissibility.code.startsWith "deferred_" then "deferred"
      else "inadmissible"
    let recordingReason? := if suggestion.isEmpty then some "compact certificate encoding was not validated" else none
    let emitReport := fun () => do
      match reportLctx? with
      | some reportLctx =>
          withLCtx' reportLctx do
            emitRecordingReport simpStx reportStx target state (some result) suggestion
              positionsNeeded failureCategory? none none
              (traceAvailable := true) (encodingStatus := encodingStatus)
              (recordingReason? := recordingReason?) (encodings := encodingInfos)
              (premiseEncodings := premiseEncodingInfos)
              (encodingMetrics := encodingMetrics)
              (encodingFallbackReason? := encodingFallbackReason?)
              (localRenames := localRenameInfos localRenames)
              (transitionContinuity? := transitionContinuity?)
              (admissibilityCode? := transitionContinuity?.map (·.reasonCode))
              (capture? := scopedCapture?) (config? := some ctx.config)
      | none =>
          emitRecordingReport simpStx reportStx target state (some result) suggestion
            positionsNeeded failureCategory? none none
            (traceAvailable := true) (encodingStatus := encodingStatus)
            (recordingReason? := recordingReason?) (encodings := encodingInfos)
            (premiseEncodings := premiseEncodingInfos)
            (encodingMetrics := encodingMetrics)
            (encodingFallbackReason? := encodingFallbackReason?)
            (localRenames := localRenameInfos localRenames)
            (transitionContinuity? := transitionContinuity?)
            (admissibilityCode? := transitionContinuity?.map (·.reasonCode))
            (capture? := scopedCapture?) (config? := some ctx.config)
    if passive then
      try
        emitReport ()
      catch ex =>
        let detail ← exceptionText ex
        -- A trace may mention locals introduced only inside the simplifier's
        -- temporary binder context.  If those locals cannot be rendered in
        -- the surrounding tactic context, retain a conservative execution
        -- record so the enclosing body scope can still classify committed
        -- versus backtracked execution.  The closed placeholder state and
        -- empty suggestion make this report permanently inadmissible.
        try
          let placeholder := mkConst ``True
          let placeholderResult : Simp.Result := { expr := placeholder }
          emitRecordingReport simpStx reportStx placeholder {} (some placeholderResult) "" false
            (some "recording_report") (some detail) none false "unavailable"
            (some detail) (admissibilityCode? := some "unclassified_recorder_failure")
            (capture? := scopedCapture?) (config? := some ctx.config)
        catch fallbackEx =>
          logWarningAt reportStx m!"passive simp recording report failed: {detail}; conservative report failed: {← exceptionText fallbackEx}"
    else
      emitReport ()
  unless passive do
    if operationalAdmissibility.accepted then
      logInfoAt reportStx m!"Try this deterministic replay:\n{suggestion}"
  mvarId.withContext do
    applyResultToTarget mvarId target result (closeReflexive := result.expr.isTrue)
  if let some attempt := scopedAttempt? then
    commitScopedAttempt attempt

private def runBodyScope (scopeId : String) (body : Syntax) (reportStx : Syntax)
    (exportProof := false) : TacticM Unit := withMainContext do
  let main ← getMainGoal
  let initialTarget ← instantiateMVars (← main.getType)
  let sourceNamespace := ((← Term.getDeclName?).map (·.getPrefix)).getD Name.anonymous
  let frameId ← enterScopedFrame scopeId
  try
    withOptions (·.set `explicitLean.simpExplicit.bodyScopeFrame frameId) do
      evalTactic body
    if exportProof then
      Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let bodyRenamePlan ← if exportProof then
      localRenamePlan (← main.getDecl).lctx
    else
      pure #[]
    let bodyProofReport? ← if exportProof then
      let goals ← getGoals
      if !goals.isEmpty then
        pure (some ({
          scopeId
          proof := none
          proofBytes := 0
          closesGoal := false
          failureReason := some "body_did_not_close"
          localRenames := localRenameInfos bodyRenamePlan
        } : BodyScopeProofReport))
      else if !(← main.isAssigned) then
        pure (some ({
          scopeId
          proof := none
          proofBytes := 0
          closesGoal := false
          failureReason := some "body_goal_unassigned"
          localRenames := localRenameInfos bodyRenamePlan
        } : BodyScopeProofReport))
      else
        let some proof ← getExprMVarAssignment? main
          | pure (some ({
              scopeId
              proof := none
              proofBytes := 0
              closesGoal := false
              failureReason := some "body_assignment_missing"
              localRenames := localRenameInfos bodyRenamePlan
            } : BodyScopeProofReport))
        let proof ← instantiateMVars proof
        let proofType ← inferType proof
        if !(← isDefEq proofType initialTarget) then
          pure (some ({
            scopeId
            proof := none
            proofBytes := 0
            closesGoal := true
            failureReason := some "body_proof_type_mismatch"
            localRenames := localRenameInfos bodyRenamePlan
          } : BodyScopeProofReport))
        else
          try
            let (exportedProof, exportedType?, argumentCount) ← if proof.hasMVar then
              let abstracted ← abstractMVars proof
              if abstracted.expr.hasMVar then
                throwError "whole-body proof contains metavariables from an outer elaboration depth"
              pure (abstracted.expr, none, abstracted.mvars.size)
            else
              pure (proof, some initialTarget, 0)
            let renamedLctx := renamedLocalContext (← main.getDecl).lctx bodyRenamePlan
            let rendered ← withLCtx' renamedLctx do
              ProofExport.render exportedProof (type? := exportedType?) {
                sourceNamespace
              }
            let proofText := if argumentCount == 0 then
              rendered.valueText
            else
              let arguments := Array.replicate argumentCount "_"
              s!"({rendered.valueText}) {String.intercalate " " arguments.toList}"
            pure (some ({
              scopeId
              proof := some proofText
              proofBytes := proofText.utf8ByteSize
              closesGoal := true
              failureReason := none
              localRenames := localRenameInfos bodyRenamePlan
            } : BodyScopeProofReport))
          catch ex =>
            pure (some ({
              scopeId
              proof := none
              proofBytes := 0
              closesGoal := true
              failureReason := some (← exceptionText ex)
              localRenames := localRenameInfos bodyRenamePlan
            } : BodyScopeProofReport))
    else
      pure none
    publishScopedFrame scopeId frameId reportStx
    if let some report := bodyProofReport? then
      logInfoAt reportStx m!"EXPLICIT_LEAN_BODY_SCOPE_PROOF_REPORT {(toJson report).compress}"
  catch ex =>
    leaveScopedFrame frameId
    throw ex

end SimpExplicit

open SimpExplicit

elab_rules : tactic
  | `(tactic| simp_explicit_body_scope $scope:str in $body:tacticSeq) => do
      let some scopeId := scope.raw.isStrLit?
        | throwErrorAt scope "body scope id must be a string literal"
      runBodyScope scopeId body.raw (← getRef)
  | `(tactic| simp_explicit_body_scope_proof $scope:str in $body:tacticSeq) => do
      let some scopeId := scope.raw.isStrLit?
        | throwErrorAt scope "body scope id must be a string literal"
      runBodyScope scopeId body.raw (← getRef) (exportProof := true)
  | `(tactic| simp_explicit_first_scope $owner:str in $body:tacticSeq) => do
      let some ownerId := owner.raw.isStrLit?
        | throwErrorAt owner "first owner id must be a string literal"
      runFirstOwnerScope ownerId body.raw (← getRef)
  | `(tactic| simp_explicit_record $occurrence:str $args:simpExplicitTraceArgs) => do
      let some occurrenceId := occurrence.raw.isStrLit?
        | throwErrorAt occurrence "occurrence id must be a string literal"
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      withOptions (fun options =>
          options
            |>.set `explicitLean.simpExplicit.passive true
            |>.set `explicitLean.simpExplicit.occurrenceId occurrenceId) do
        recordSimp inner (← getRef)
  | `(tactic| simp_explicit? $args:simpExplicitTraceArgs) => do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordSimp inner (← getRef)
  | `(tactic| simp_explicit [$events:simpExplicitEvent,*]) =>
      replaySimp (events.getElems.map (·.raw))
  | `(tactic| simp_explicit leave_open [$events:simpExplicitEvent,*]) =>
      replaySimp (events.getElems.map (·.raw)) (closeReflexive := false)
  | `(tactic| simp_explicit_context [$groups:simpExplicitContextGroup,*]) =>
      replayContext (groups.getElems.map (·.raw))
  | `(tactic| simp_explicit_rename [$renames:simpExplicitLocalRename,*]) => do
      let mut parsed : Array (Nat × Name) := #[]
      for rename in renames.getElems do
        match rename with
        | `(simpExplicitLocalRename| $index:num => $name:ident) =>
            let some contextIndex := index.raw.isNatLit?
              | throwErrorAt index "local-context index must be a natural-number literal"
            parsed := parsed.push (contextIndex, name.getId)
        | _ => throwUnsupportedSyntax
      exactLocalRenames parsed

end ExplicitLean
