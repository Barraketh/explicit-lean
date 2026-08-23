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
declare_syntax_cat simpExplicitRule
syntax (name := simpExplicitLocalRule)
  (simpExplicitPre <|> simpExplicitPost)? "local_rule " num
  (simpExplicitPremiseArgs)? : simpExplicitRule
syntax (name := simpExplicitOrdinaryRule)
  (simpExplicitPre <|> simpExplicitPost)? "← "? term (simpExplicitPremiseArgs)? : simpExplicitRule
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
syntax (name := simpExplicitPremiseTerminal) "simp_explicit_premise" ident : tactic
declare_syntax_cat simpExplicitLocalRename
syntax num " => " ident : simpExplicitLocalRename
/-- Give recorded local-context entries stable printable names. Unlike
`rename_i`, this operation addresses exact context indices and is idempotent,
so independently generated certificates can be composed in one declaration. -/
syntax (name := simpExplicitRename) "simp_explicit_rename" " ["
  simpExplicitLocalRename,* "]" : tactic
syntax (name := simpExplicitBodyScope) "simp_explicit_body_scope" str " in " tacticSeq : tactic
/-- Instrument one closed `first` owner while materializing a body. Child
    occurrences are recorded in a scoped frame; the enclosing owner proof is
    never inspected or exported. -/
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
def reportSchemaVersion : Nat := 15

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
  | projectionFunction (name : Name)
  /-- Expand exactly one ambient local `let` declaration.  The declaration
      identity and its stored value are kept in the replay operation rather
      than rediscovered from the simplifier or the local context. -/
  | localDef (fvarId : FVarId) (contextIndex : Nat) (name : Name) (value : Expr)
  | eta
  deriving Repr

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

structure PremiseTerminalReport where
  kind : String
  localContextIndex : Option Nat := none
  localName : Option String := none
  deriving ToJson

mutual
  structure PremiseReport where
    proposition : ExprFingerprint
    origins : Array OriginCandidate
    commands : Array SemanticEventReport
    terminal : PremiseTerminalReport
    encodingKind : Option String
    encodingReason : Option String
    bindingName : Option String
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

end

structure EncodingMetrics where
  mode : String := "event"
  /-- Number of emitted presentation-only `change` prepasses. -/
  presentationChangeCount : Nat := 0
  namedRuleEvents : Nat := 0
  reductionEvents : Nat := 0
  deltaReductionEvents : Nat := 0
  /-- Raw callbacks whose exact local transition was represented by another
      member of the same structural-match group. -/
  nonmaterialInternalEvents : Nat := 0
  generatedProofEvents : Nat := 0
  generatedSimprocEvents : Nat := 0
  /-- Raw recorder events whose hierarchy contains a simproc callback.  These
      are deferred before any source/proof encoder is attempted. -/
  deferredSimprocEvents : Nat := 0
  generatedSpecialEvents : Nat := 0
  wholeResultProofCount : Nat := 0
  generatedBindingCount : Nat := 0
  generatedBindingBytes : Nat := 0
  premiseBindingCount : Nat := 0
  premiseBindingBytes : Nat := 0
  nestedPremiseBindings : Nat := 0
  termPremiseBindings : Nat := 0
  /-- Premise-bearing traces for which no complete operational child program
      could be validated.  These remain explicit coverage failures and may
      never fall through to an exported event or whole-result proof. -/
  premiseProgramFailures : Nat := 0
  /-- Recorded events for which no source-replayable operational program could
      be constructed.  This is a fail-closed coverage result, never a proof
      or presentation fallback. -/
  operationalProgramFailures : Nat := 0
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
    if metrics.deferredSimprocEvents > 0 || metrics.generatedSimprocEvents > 0 then
      some "deferred_simproc"
    else if let some continuity := transitionContinuity? then
      some continuity.reasonCode
    else if let some overrideCode := overrideCode? then
      some overrideCode
    else if metrics.termPremiseBindings > 0 then
      some "inadmissible_direct_term_premise"
    else if metrics.premiseProgramFailures > 0 then
      some "inadmissible_premise_program"
    else if metrics.operationalProgramFailures > 0 then
      some "inadmissible_operational_program"
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

mutual
  private structure PremiseEncodingInfo where
    kind : String
    reason : Option String
    bindingName : Option Name
    bytes : Nat
    /-- Encoding metadata for the executable child program owned by this
        premise.  It is recursive so nested premise programs remain visible
        in the report at their actual scope. -/
    commands : Array EventEncodingInfo := #[]

  private structure EventEncodingInfo where
    kind : String
    reason : Option String
    selectorKind : Option String := none
    selectorValue : Option Nat := none
    deltaReduction : Bool := false
    /-- Per-premise encoding trees aligned with the event's raw premises. -/
    premises : Array PremiseEncodingInfo := #[]
end

private inductive PremiseTerminal where
  | isTrue (result : Expr)
  | dischargeRfl (result : Expr)
  | localAssumption (fvarId : FVarId) (contextIndex : Nat) (name : Name)
  | equationHypothesis
  | custom

mutual
  private structure RecordedPremise where
    proposition : Expr
    proof : Expr
    origins : Array Origin
    events : Array RecordedEvent
    terminal : PremiseTerminal

  private structure RecordedEvent where
    tick : Nat
    phase : Phase
    input : Expr
    step : Simp.Step
    result : Simp.Result
    origins : Array Origin
    premises : Array RecordedPremise
    reduction : Option ReductionIdentity := none
    /-- Positive declaration-index slot for a callback-local simp theorem. -/
    localRuleSlot : Option Nat := none
end

private structure PremiseFrame where
  proposition : Expr
  events : Array RecordedEvent := #[]
  pendingPremises : Array RecordedPremise := #[]
  deriving Inhabited

private structure RecorderState where
  tick : Nat := 0
  /-- Number of reentrant simplifier methods currently executing. Nested
      calls contribute ticks and diagnostics to their enclosing method, but
      are not independent semantic replay events. -/
  activeDepth : Nat := 0
  events : Array RecordedEvent := #[]
  premises : Array RecordedPremise := #[]
  premiseFrames : Array PremiseFrame := #[]
  premiseStack : Array Nat := #[]
  /-- Exact theorem origins captured by the committed rewrite interposer.
      Slots are scoped by `trackedMethod`, so nested discharge rewrites do not
      overwrite the enclosing method's selected candidate. -/
  rewriteOrigins : Array (Option Origin) := #[]

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

/-! `Simp.rewrite?` records the selected theorem in the simplifier state, but
    that state is intentionally an aggregate diagnostic.  The recorder needs
    the candidate that actually returned `some result`, including when an
    earlier candidate was tried and abandoned.  Keep that one bit of
    provenance in a slot owned by the tracked method invocation. -/
private def rememberRewriteOrigin (ref : IO.Ref RecorderState) (origin : Origin) :
    Simp.SimpM Unit := do
  let state ← ref.get
  if !state.rewriteOrigins.isEmpty then
    let index := state.rewriteOrigins.size - 1
    ref.set { state with rewriteOrigins := state.rewriteOrigins.set! index (some origin) }

/-! This is a public-API mirror of the pinned `Simp.rewrite?` candidate loop.
    It deliberately delegates theorem matching and proof construction to
    `Simp.tryTheoremWithExtraArgs?`; the recorder only captures the origin of
    the candidate for which that operation returned `some`. -/
private def exactRewrite? (ref : IO.Ref RecorderState) (e : Expr)
    (s : DiscrTree SimpTheorem) (erased : PHashSet Origin) (tag : String) :
    Simp.SimpM (Option Simp.Result) := do
  if (← Simp.getConfig).index then
    let candidates ← Simp.withSimpIndexConfig <| DiscrTree.getMatchWithExtra s e
    if candidates.isEmpty then
      trace[Debug.Meta.Tactic.simp] "no theorems found for {tag}-rewriting {e}"
      return none
    let candidates := Array.insertionSort candidates fun e₁ e₂ => e₁.1.priority > e₂.1.priority
    for (thm, numExtraArgs) in candidates do
      checkSystem "simp"
      if erased.contains thm.origin then
        continue
      let recorderSnapshot ← ref.get
      let metaSnapshot ← liftM Meta.saveState
      let simpSnapshot ← get
      let result? ← try
        Simp.tryTheoremWithExtraArgs? e thm numExtraArgs
      catch ex =>
        ref.set recorderSnapshot
        liftM metaSnapshot.restore
        set simpSnapshot
        throw ex
      if let some result := result? then
        trace[Debug.Meta.Tactic.simp] "rewrite result {e} => {result.expr}"
        rememberRewriteOrigin ref thm.origin
        return some result
      ref.set recorderSnapshot
      liftM metaSnapshot.restore
      set simpSnapshot
    return none
  else
    let (candidates, numArgs) ← Simp.withSimpIndexConfig <| DiscrTree.getMatchLiberal s e
    if candidates.isEmpty then
      trace[Debug.Meta.Tactic.simp] "no theorems found for {tag}-rewriting {e}"
      return none
    let candidates := Array.insertionSort candidates fun e₁ e₂ => e₁.priority > e₂.priority
    for thm in candidates do
      checkSystem "simp"
      unless erased.contains thm.origin do
        -- `getMatchLiberal` gives the number of root application arguments,
        -- while `tryTheoremWithExtraArgs?` needs the number of arguments past
        -- the theorem lhs.  Derive it in an isolated metavariable probe and
        -- explicitly restore that probe before trying the authoritative
        -- candidate, so no inferred telescope state can leak between them.
        let probeMetaSnapshot ← liftM Meta.saveState
        let numExtraArgs? ← try
          withNewMCtxDepth do
            let val ← thm.getValue
            let type ← inferType val
            let (_, _, type) ← forallMetaTelescopeReducing type
            let type ← whnf (← instantiateMVars type)
            let lhs := type.appFn!.appArg!
            pure (some (numArgs - lhs.getAppNumArgs))
        finally
          liftM probeMetaSnapshot.restore
        let some numExtraArgs := numExtraArgs? | continue
        let recorderSnapshot ← ref.get
        let metaSnapshot ← liftM Meta.saveState
        let simpSnapshot ← get
        let result? ← try
          Simp.tryTheoremWithExtraArgs? e thm numExtraArgs
        catch ex =>
          ref.set recorderSnapshot
          liftM metaSnapshot.restore
          set simpSnapshot
          throw ex
        if let some result := result? then
          trace[Debug.Meta.Tactic.simp] "rewrite result {e} => {result.expr}"
          if (← isDiagnosticsEnabled) then
            let indexed ← Simp.withSimpIndexConfig <| DiscrTree.getMatchWithExtra s e
            unless indexed.any (fun candidate => unsafe ptrEq thm candidate.1) do
              Simp.recordTheoremWithBadKeys thm
          rememberRewriteOrigin ref thm.origin
          return some result
        ref.set recorderSnapshot
        liftM metaSnapshot.restore
        set simpSnapshot
    return none

private def exactRewritePre (ref : IO.Ref RecorderState) : Simp.Simproc := fun e => do
  for thms in (← Simp.getContext).simpTheorems do
    if let some result ← exactRewrite? ref e thms.pre thms.erased "pre" then
      return .visit result
  return .continue

private def exactRewritePost (ref : IO.Ref RecorderState) : Simp.Simproc := fun e => do
  for thms in (← Simp.getContext).simpTheorems do
    if let some result ← exactRewrite? ref e thms.post thms.erased "post" then
      return .visit result
  return .continue

private def replayZeta? (input : Expr) : MetaM (Option Expr) := do
  match input with
  | .letE _ _ value body _ =>
      return some (expandLet body #[value] (zetaHave := true))
  | _ => return none

/-! This is a local clone of the pinned Lean 4.32.2 `reduceProjFn?` branch.
    The upstream helper is private, so keeping the branch here makes the
    observed and replayed operation explicit without invoking ambient simp or
    exporting a proof fallback. -/
private def unfoldProjectionFunctionAny? (input : Expr) : MetaM (Option Expr) := do
  if let .const declarationName _ := input.getAppFn then
    if (← isIrreducible declarationName) then
      return none
  unfoldDefinition? input (ignoreTransparency := true)

private def reduceProjectionFunction? (input : Expr) : Simp.SimpM (Option Expr) := do
  matchConst input.getAppFn (fun _ => pure none) fun constantInfo _ => do
    let some projectionInfo ← getProjectionFnInfo? constantInfo.name | return none
    let reduceProjectionContinuation? (input? : Option Expr) : Simp.SimpM (Option Expr) := do
      match input? with
      | none => pure none
      | some input =>
          match (← Simp.withSimpMetaConfig <| reduceProj? input.getAppFn) with
          | some function => return some (mkAppN function input.getAppArgs)
          | none => return none
    if projectionInfo.fromClass then
      if (← Simp.getContext).isDeclToUnfold constantInfo.name then
        let input? ← withReducibleAndInstances <| unfoldDefinition? input
        if input?.isSome then
          Simp.recordSimpTheorem (.decl constantInfo.name)
        return input?
      else
        unless input.getAppNumArgs > projectionInfo.numParams do
          return none
        let major := input.getArg! projectionInfo.numParams
        unless (← isConstructorApp major) do
          return none
        if backward.whnf.reducibleClassField.get (← getOptions) then
          unfoldProjectionFunctionAny? input
        else
          reduceProjectionContinuation? (← unfoldProjectionFunctionAny? input)
    else
      reduceProjectionContinuation? (← unfoldDefinition? input)

/-! Replay uses the same pinned projection-function branches, but must not let
    the nested `reduceProj?` call restore `Simp.neutralConfig` through
    `withSimpMetaConfig`. The caller supplies the replay-local beta/projection
    Meta configuration; keeping this helper separate leaves the recorder's
    ordinary-simp clone above unchanged. -/
private def reduceProjectionFunctionReplay? (input : Expr) : Simp.SimpM (Option Expr) := do
  matchConst input.getAppFn (fun _ => pure none) fun constantInfo _ => do
    let some projectionInfo ← getProjectionFnInfo? constantInfo.name | return none
    let reduceProjectionContinuation? (input? : Option Expr) : Simp.SimpM (Option Expr) := do
      match input? with
      | none => pure none
      | some input =>
          match (← reduceProj? input.getAppFn) with
          | some function => return some (mkAppN function input.getAppArgs)
          | none => return none
    if projectionInfo.fromClass then
      -- The certificate has already named this exact class projection.  That
      -- explicit identity replaces ordinary `simp`'s `isDeclToUnfold` bit;
      -- consulting the replay context here would incorrectly reject commands
      -- recorded from `simp only [..., default]`.  Keep the pinned unfolding
      -- operation itself unchanged and do not install any ambient simp rule.
      let input? ← withReducibleAndInstances <| unfoldDefinition? input
      if input?.isSome then
        return input?
      unless input.getAppNumArgs > projectionInfo.numParams do
        return none
      let major := input.getArg! projectionInfo.numParams
      unless (← isConstructorApp major) do
        return none
      if backward.whnf.reducibleClassField.get (← getOptions) then
        unfoldProjectionFunctionAny? input
      else
        reduceProjectionContinuation? (← unfoldProjectionFunctionAny? input)
    else
      reduceProjectionContinuation? (← unfoldDefinition? input)

/-! This public pre-method interposer implements the supported prefix branches
    in pinned `reduceStep` precedence. The upstream `Simp.mainCore` remains
    authoritative; a successful `.visit` makes it recurse on the observed
    result, so its private transition is not run a second time. Unsupported
    private branches remain unrecorded and therefore fail exact closed replay;
    they cannot become accepted certificates accidentally. -/
private def selectedReduction? (input : Expr) : Simp.SimpM (Option (ReductionIdentity × Expr)) := do
  let metaSnapshot ← liftM Meta.saveState
  let simpSnapshot ← get
  let restore := do
    liftM metaSnapshot.restore
    set simpSnapshot
  try
    let cfg ← Simp.getConfig
    let f := input.getAppFn
    if cfg.beta && f.isHeadBetaTargetFn false then
      let output := f.betaRev input.getAppRevArgs
      if !Expr.equal input output then
        return some ({ kind := .beta }, output)
      restore
      return none
    if cfg.proj then
      match input with
      | .proj structureName field _ =>
          match (← Simp.withSimpMetaConfig <| reduceProj? input) with
          | some output =>
              if !Expr.equal input output then
                return some ({ kind := .projection structureName field }, output)
              restore
              return none
          | none => pure ()
      | _ => pure ()
      match f with
      | .const projectionFunctionName _ =>
          match (← Simp.withSimpMetaConfig <| reduceProjectionFunction? input) with
          | some output =>
              if !Expr.equal input output then
                return some ({ kind := .projectionFunction projectionFunctionName }, output)
              restore
              return none
          | none => pure ()
      | _ => pure ()
    if cfg.iota then
      match (← Simp.withSimpMetaConfig <| reduceRecMatcher? input) with
      | some output =>
          if !Expr.equal input output then
            return some ({ kind := .iota }, output)
          restore
          return none
      | none => pure ()
    if let .letE _ _ value body nondep := input then
      let zetaOutput? ← if cfg.zeta && (!nondep || cfg.zetaHave) then
          pure (some (expandLet body #[value] (zetaHave := cfg.zetaHave)))
        else if cfg.zetaUnused && !body.hasLooseBVars then
          pure (some (consumeUnusedLet body))
        else
          pure none
      if let some zetaOutput := zetaOutput? then
        if !Expr.equal input zetaOutput then
          let replayOutput? ← liftM <| replayZeta? input
          if let some replayOutput := replayOutput? then
            if Expr.equal zetaOutput replayOutput then
              return some ({ kind := .zeta }, zetaOutput)
        restore
        return none
    let .const head _ := f | restore; return none
    let ctx ← Simp.getContext
    if input.isProj then
      restore
      return none
    if ← isProjectionFn head then
      restore
      return none
    if cfg.autoUnfold then
      restore
      return none
    unless ctx.isDeclToUnfold head do
      restore
      return none
    if ← isIrreducible head then
      restore
      return none
    let options ← getOptions
    let smart := smartUnfolding.get options && (← getEnv).contains (mkSmartUnfoldingNameFor head)
    unless cfg.unfoldPartialApp || smart do
      let some cinfo := (← getEnv).find? head
        | restore
          return none
      let some value := cinfo.value?
        | restore
          return none
      if value.getNumHeadLambdas > input.getAppNumArgs then
        restore
        return none
    let some output ← Simp.withSimpMetaConfig <| unfoldDefinition? input (ignoreTransparency := true)
      | restore
        return none
    if Expr.equal input output then
      restore
      return none
    Simp.recordSimpTheorem (.decl head)
    return some ({ kind := .delta head }, output)
  catch _ =>
    restore
    return none

/- The pinned `Simp.simpMatch` pre-simproc invokes the same
   `reduceRecMatcher?` operation before the private `reduceStep` boundary.
   Classify only that exact proofless, origin-free result; the original
   simproc step remains authoritative and the probe's temporary state is
   restored before recording continues. -/
private def classifyObservedIota? (input : Expr) (result : Simp.Result)
    (preMeta postMeta : Meta.SavedState) (preSimp postSimp : Simp.State) : Simp.SimpM Bool := do
  let isMatch ← try
    liftM preMeta.restore
    set preSimp
    let cfg ← Simp.getConfig
    if !cfg.iota then
      pure false
    else
      let output? ← Simp.withSimpMetaConfig <| reduceRecMatcher? input
      pure <| output?.any (Expr.equal result.expr)
  catch _ =>
    pure false
  liftM postMeta.restore
  set postSimp
  return isMatch

/- The built-in premise discharger mirrors the pinned `Simp.dischargeDefault?`
   branch order.  The local-assumption branch is intentionally duplicated here
   rather than delegated to an opaque helper: its contextual and initial-lctx
   filtering is part of the recorded terminal's semantics. -/
private def dischargeUsingAssumption? (e : Expr) : Simp.SimpM
    (Option (Expr × PremiseTerminal)) := do
  let context ← Simp.getContext
  let lctxInitIndices := context.lctxInitIndices
  let contextual := (← Simp.getConfig).contextual
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if !contextual && localDecl.index >= lctxInitIndices then
      return none
    else if (← Simp.withSimpMetaConfig <| isDefEq e localDecl.type) then
      return some (localDecl.toExpr,
        .localAssumption localDecl.fvarId localDecl.index localDecl.userName)
    else
      return none

private def commitRecordedPremise (state : RecorderState) (premise : RecordedPremise) :
    RecorderState :=
  let frames := state.premiseFrames.pop
  let stack := state.premiseStack.pop
  match stack.back? with
  | some parentIndex =>
      let parent := frames[parentIndex]!
      {
        state with
          premiseFrames := frames.set! parentIndex
            { parent with pendingPremises := parent.pendingPremises.push premise }
          premiseStack := stack
      }
  | none =>
      { state with
          premiseFrames := frames
          premiseStack := stack
          premises := state.premises.push premise }

private def recordedDischarge? (ref : IO.Ref RecorderState) (proposition : Expr) :
    Simp.SimpM (Option Expr) := do
  let recorderSnapshot ← ref.get
  let metaSnapshot ← liftM Meta.saveState
  let simpSnapshot ← get
  let cleaned := proposition.cleanupAnnotations
  let frameIndex := recorderSnapshot.premiseFrames.size
  ref.set {
    recorderSnapshot with
      premiseFrames := recorderSnapshot.premiseFrames.push { proposition := proposition }
      premiseStack := recorderSnapshot.premiseStack.push frameIndex
  }
  let diagBefore := (← get).diag
  let restore := do
    ref.set recorderSnapshot
    liftM metaSnapshot.restore
    set simpSnapshot
  try
    let outcome? ← if Simp.isEqnThmHypothesis cleaned then
      if let some result ← dischargeUsingAssumption? cleaned then
        pure (some result)
      else if let some proof ← liftM <| Simp.dischargeEqnThmHypothesis? cleaned then
        pure (some (proof, .equationHypothesis))
      else
        pure none
    else
      pure none
    let outcome? ← match outcome? with
      | some outcome => pure (some outcome)
      | none => do
          let result ← Simp.simp cleaned
          let some rflProof ← Simp.dischargeRfl result.expr
            | if result.expr.isTrue then
                let equality ← liftM result.getProof
                let proof ← liftM <| mkOfEqTrue equality
                pure (some (proof, .isTrue result.expr))
              else
                pure none
          let equality ← liftM result.getProof
          let proof := mkApp4 (mkConst ``Eq.mpr [Level.zero]) cleaned result.expr equality rflProof
          pure (some (proof, .dischargeRfl result.expr))
    match outcome? with
    | none =>
        restore
        return none
    | some (proof, terminal) =>
        let state ← ref.get
        let some frame := state.premiseFrames[frameIndex]?
          | restore
            return none
        let diagAfter := (← get).diag
        let proposition0 ← liftM (m := MetaM) <| instantiateMVars proposition
        let proofType ← liftM (m := MetaM) <| inferType proof
        let proposition := if proposition0.hasMVar then proofType else proposition0
        let premise : RecordedPremise := {
          proposition
          proof
          origins := changedOrigins diagBefore diagAfter
          events := frame.events
          terminal
        }
        ref.set (commitRecordedPremise state premise)
        return some proof
  catch ex =>
    restore
    throw ex

private def trackedMethod (ref : IO.Ref RecorderState) (phase : Phase)
    (method : Simp.Simproc) (captureRewriteOrigin : Bool := false)
    (detectReduction : Bool := true) : Simp.Simproc := fun input => do
  let state ← ref.get
  let position := state.tick + 1
  let depth := state.activeDepth
  let premiseFrameIndex? := state.premiseStack.back?
  ref.set {
    state with
      tick := position
      activeDepth := depth + 1
      rewriteOrigins := state.rewriteOrigins.push none
  }
  let premiseStart := match premiseFrameIndex? with
    | some frameIndex => state.premiseFrames[frameIndex]!.pendingPremises.size
    | none => state.premises.size
  try
    let before := (← get).diag
    let preMetaSnapshot ← liftM Meta.saveState
    let preSimpSnapshot ← get
    let originalStep ← try
      method input
    finally
      let state ← ref.get
      ref.set { state with activeDepth := state.activeDepth - 1 }
    let mut step := originalStep
    let mut reduction? : Option ReductionIdentity := none
    if detectReduction && (depth == 0 || premiseFrameIndex?.isSome) && phase == .pre then
      match originalStep with
      | .continue none =>
          if let some (reduction, output) ← selectedReduction? input then
            let result : Simp.Result := { expr := output }
            step := .visit result
            reduction? := some reduction
      | _ => pure ()
    let after := (← get).diag
    let postMetaSnapshot ← liftM Meta.saveState
    let postSimpSnapshot ← get
    let stateAfterMethod ← ref.get
    let selectedOrigin? :=
      if captureRewriteOrigin then stateAfterMethod.rewriteOrigins.back? |>.bind id else none
    let localRuleSlot? ← if captureRewriteOrigin then
        match selectedOrigin? with
        | some (.fvar fvarId) => do
            let context ← Simp.getContext
            let localDecl? ← try
              some <$> fvarId.getDecl
            catch _ =>
              pure none
            match localDecl? with
            | some localDecl =>
                if localDecl.index >= context.lctxInitIndices then
                  pure (some (localDecl.index - context.lctxInitIndices + 1))
                else
                  pure none
            | none => pure none
        | _ => pure none
      else
        pure none
    if depth == 0 || premiseFrameIndex?.isSome then
      if let some result := changedResult? input step then
        let state ← ref.get
        let premises := match premiseFrameIndex? with
          | some frameIndex =>
              let frame := state.premiseFrames[frameIndex]!
              frame.pendingPremises.extract premiseStart frame.pendingPremises.size
          | none => state.premises.extract premiseStart state.premises.size
        let state := match premiseFrameIndex? with
          | some frameIndex =>
              let frame := state.premiseFrames[frameIndex]!
              let updatedFrame : PremiseFrame :=
                { frame with pendingPremises := frame.pendingPremises.take premiseStart }
              let updatedFrames := state.premiseFrames.set! frameIndex updatedFrame
              { state with premiseFrames := updatedFrames }
          | none =>
              { state with premises := state.premises.take premiseStart }
        let premiseOrigins := premises.foldl (fun result premise => result ++ premise.origins) #[]
        let origins := if captureRewriteOrigin then
            selectedOrigin?.toArray
          else
            subtractOrigins (changedOrigins before after) premiseOrigins
        if reduction?.isNone && phase == .pre && result.proof?.isNone && origins.isEmpty then
          if ← classifyObservedIota? input result preMetaSnapshot postMetaSnapshot
              preSimpSnapshot postSimpSnapshot then
            reduction? := some { kind := .iota }
        let event : RecordedEvent := {
          tick := position
          phase
          input
          step
          result
          origins := if reduction?.isSome then #[] else origins
          premises
          reduction := reduction?
          localRuleSlot := if reduction?.isSome then none else localRuleSlot?
        }
        match premiseFrameIndex? with
        | some frameIndex =>
            let frame := state.premiseFrames[frameIndex]!
            ref.set { state with
              premiseFrames := state.premiseFrames.set! frameIndex
                ({ frame with events := frame.events.push event }) }
        | none =>
            ref.set { state with events := state.events.push event }
      else
        -- A candidate that does not change its input is observationally
        -- abandoned.  Discharge probes and their nested frames must not leak
        -- into the next candidate or into the enclosing event.
        ref.set state
        return step
    let state ← ref.get
    ref.set { state with rewriteOrigins := state.rewriteOrigins.pop }
    return step
  catch ex =>
    -- A recovered recorder must not retain a stale outer candidate slot when
    -- a method exits exceptionally before the normal pop below.
    ref.set state
    throw ex

private def recordingMethods (ref : IO.Ref RecorderState)
    (simprocs : Simp.SimprocsArray) (_discharge? : Option Simp.Discharge) : Simp.Methods :=
  let methods := match _discharge? with
    | none => Simp.mkDefaultMethodsCore simprocs
    | some discharge => Simp.mkMethods simprocs discharge (wellBehavedDischarge := false)
  let pre :=
    trackedMethod ref .pre (exactRewritePre ref)
        (captureRewriteOrigin := true) (detectReduction := false) >>
      trackedMethod ref .pre
        (Simp.simpMatch >> Simp.userPreSimprocs simprocs >> Simp.simpUsingDecide)
  let post :=
    trackedMethod ref .post (exactRewritePost ref)
        (captureRewriteOrigin := true) (detectReduction := false) >>
      trackedMethod ref .post
        (Simp.userPostSimprocs simprocs >> Simp.simpGround >> Simp.simpArith >>
          Simp.simpUsingDecide)
  { methods with
    pre
    post
    discharge? := recordedDischarge? ref }

private def declarationRuleName (name : Name) : MetaM Name := do
  let direct := mkIdent name
  let resolved? ← try
    some <$> resolveGlobalConstNoOverload direct
  catch _ =>
    pure none
  if resolved? == some name then
    return name
  -- `_root_` is syntax, not part of the declaration's kernel name.  Add it
  -- only when the replacement site's namespace/open context would resolve
  -- the ordinary fully dotted spelling to a different declaration.
  return (Name.mkSimple "_root_").append name

private def ruleText (origin : Origin) : MetaM String := do
  match origin with
  | .decl name _ inverse =>
      if (← Simp.isBuiltinSimproc name) || (← Simp.isSimproc name) then
        throwError "simp_explicit cannot yet encode simproc '{name}'"
      -- Keep the declaration's dotted kernel name and add `_root_.` when the
      -- replacement namespace/open state would resolve that spelling to a
      -- different theorem.
      let printedName ← declarationRuleName name
      return (if inverse then "← " else "") ++ printedName.toString
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

private def recordedRuleText (event : RecordedEvent) : MetaM String := do
  if let some slot := event.localRuleSlot then
    return s!"local_rule {slot}"
  let some origin := event.origins[0]?
    | throwError "simp_explicit cannot encode a semantic event without a named origin"
  ruleText origin

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
  | .projectionFunction name => {
      kind := "projection_function"
      name := some name.toString
      field := none
    }
  | .localDef _ _ name _ => {
      kind := "local_def"
      name := some name.toString
      field := none
    }
  | .eta => { kind := "eta", name := none, field := none }

private def reductionText (reduction : ReductionIdentity) : MetaM String := do
  match reduction.kind with
  | .delta name =>
      let printedName ← declarationRuleName name
      return s!"reduce delta {printedName}"
  | .beta => return "reduce beta"
  | .zeta => return "reduce zeta"
  | .iota => return "reduce iota"
  | .projection structureName field =>
      return s!"reduce projection {structureName} {field}"
  | .projectionFunction name =>
      let printedName ← declarationRuleName name
      return s!"reduce projection_fn {printedName}"
  | .localDef _ _ name _ =>
      if name.isInaccessibleUserName then
        throwError "simp_explicit cannot print inaccessible local definition '{name}'"
      return s!"reduce local_def {name}"
  | .eta => return "reduce eta"

private def reductionSource (reduction : ReductionIdentity) (phase : Phase) : MetaM String := do
  let phasePrefix := if phase == .pre then "" else "↑ "
  return phasePrefix ++ (← reductionText reduction)

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
      | some reduction => reductionSource reduction event.phase
      | none => do
          unless event.localRuleSlot.isSome || event.origins.size == 1 do
            throwError "simp_explicit cannot encode semantic event {index}: observed {event.origins.size} diagnostic origin candidates"
          let rule ← recordedRuleText event
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
  /-- Singleton discrimination indexes, built once when the source or recorded
      event is elaborated rather than once per traversal callback. -/
  indexedRules : Array SimpTheorems := #[]
  premises : Array Expr := #[]
  reduction : Option ReductionIdentity := none
  /-- Deferred identity for a theorem local to the current simplifier traversal. -/
  localRuleSlot : Option Nat := none
  source : Syntax

private def indexReplayRules (rules : Array SimpTheorem) : Array SimpTheorems :=
  rules.map fun rule => ({} : SimpTheorems).addSimpTheorem rule

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
  /-- Event metadata remains aligned with the complete recorder trace.  The
      executable certificate in `events` may be an order-preserving projection
      of that trace. -/
  rawEncodingInfos : Array EventEncodingInfo := #[]
  rawPremiseEncodingInfos : Array (Array PremiseEncodingInfo) := #[]

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

/-- Premise-provider and diagnostic definitional equality must remain bounded,
    but the bound must also accommodate instance-heavy propositions reached by
    ordinary Mathlib `simp`.  Core heartbeat counts are 1000 times the
    user-facing value, so this is a 2000-heartbeat local budget. -/
private def premiseDefEqHeartbeatBudget : Nat := 2000000

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

private def resolveReductionDeclaration (stx : Syntax) : TacticM Name := do
  resolveGlobalConstNoOverload stx

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
    if operation == `delta then
      let name ← resolveReductionDeclaration stx[3]
      return (phase, { kind := .delta name })
    if operation == `projection_fn then
      let name ← resolveReductionDeclaration stx[3]
      return (phase, { kind := .projectionFunction name })
    if operation == `local_def then
      let some localExpr ← Term.isLocalIdent? stx[3]
        | throwErrorAt stx[3]
            "expected an accessible local let identifier for `reduce local_def`"
      let .fvar fvarId := localExpr
        | throwErrorAt stx[3]
            "expected an accessible local let identifier for `reduce local_def`"
      let localDecl ← try
        fvarId.getDecl
      catch _ =>
        throwErrorAt stx[3] "local definition is no longer available"
      if localDecl.userName.isInaccessibleUserName then
        throwErrorAt stx[3]
          "`reduce local_def` requires an accessible local let identifier"
      match localDecl with
      | .ldecl contextIndex declarationFVarId name _ value _ _ =>
          unless declarationFVarId == fvarId do
            throwErrorAt stx[3] "local definition identity changed during elaboration"
          return (phase, { kind := .localDef fvarId contextIndex name value })
      | .cdecl .. =>
          throwErrorAt stx[3]
            "`reduce local_def` requires a local let declaration, not a variable"
    throwErrorAt stx[2]
      "expected `delta`, `projection_fn`, or `local_def` for a named reduction command"
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
  -- Match `simp`'s declaration-argument path.  Elaborating a bare polymorphic
  -- theorem as an unconstrained term can default its type and instance
  -- metavariables (for example, specializing `Set.mem_neg` to `Set Int`).
  -- `simp` resolves such an identifier as a declaration and constructs the
  -- theorem from the constant, preserving its universe and type parameters.
  let localIdent? ← if term.isIdent then Term.isLocalIdent? term else pure none
  let declaration? ← if term.isIdent && localIdent?.isNone then
    try
      some <$> resolveGlobalConstNoOverload term
    catch _ =>
      pure none
  else
    pure none
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
    | match declaration? with
      | some declaration =>
          return ← mkSimpTheoremFromConst declaration
            (inv := inverse) (post := phase == .post)
      | none => throwErrorAt term "could not elaborate explicit simp rule"
  let origin := Origin.stx (← mkFreshId) rule
  let contextualRules ← mkSimpTheoremFromExpr origin levelParams proof
    (inv := inverse) (post := phase == .post)
  match declaration? with
  | none => return contextualRules
  | some declaration =>
      -- Build the generic rules after contextual elaboration so no temporary
      -- metavariable assignments from the latter can specialize their keys.
      let genericRules ← mkSimpTheoremFromConst declaration
        (inv := inverse) (post := phase == .post)
      -- A plain constant reconstructs the same declaration rules.  An applied
      -- term carries deterministic context specialization and may have the
      -- discrimination keys used by a registered coercion theorem.
      return if proof.isConst then genericRules else genericRules ++ contextualRules

private def elaborateRecordedDeclRule (name : Name) (post inverse : Bool) : TacticM (Array SimpTheorem) := do
  -- Validate the exact printed name in the replacement namespace/open state,
  -- then use the same dual declaration/contextual path as a freshly compiled
  -- certificate.
  let printedName ← declarationRuleName name
  let term : TSyntax `term := ⟨mkIdent printedName⟩
  let resolved ← resolveGlobalConstNoOverload term
  unless resolved == name do
    throwErrorAt term "printed simp rule resolved to '{resolved}' instead of '{name}'"
  let rule ← if inverse then
      `(simpExplicitRule| ← $term:term)
    else
      `(simpExplicitRule| $term:term)
  elaborateRule (if post then .post else .pre) rule

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
  else if rule.getKind == ``Lean.Parser.Tactic.simpExplicitLocalRule then
    let phase ← if rule[0].isNone then pure .post else parsePhase rule[0][0]
    let some slot := rule[2].isNatLit?
      | throwErrorAt rule[2] "expected a positive local simp-rule slot"
    if slot == 0 then
      throwErrorAt rule[2] "local simp-rule slots start at 1"
    let premises ← premiseSyntaxes rule |>.mapM elaboratePremise
    return {
      selector
      phase
      rules := #[]
      premises
      localRuleSlot := some slot
      source := stx
    }
  else
    let phase ← if rule[0].isNone then pure .post else parsePhase rule[0][0]
    let rules ← elaborateRule phase rule
    let premises ← premiseSyntaxes rule |>.mapM elaboratePremise
    return { selector, phase, rules, indexedRules := indexReplayRules rules, premises, source := stx }

private def recordedReplayEvent (event : RecordedEvent)
    (selector : ReplaySelector := .next)
    (premiseProofs? : Option (Array Expr) := none) : TacticM ReplayEvent := do
  if let some reduction := event.reduction then
    return {
      selector
      phase := event.phase
      rules := #[]
      premises := #[]
      reduction := some reduction
      source := (mkIdent `reduce).raw
    }
  if let some slot := event.localRuleSlot then
    return {
      selector
      phase := event.phase
      rules := #[]
      premises := premiseProofs?.getD (event.premises.map (·.proof))
      localRuleSlot := some slot
      source := (mkIdent `local_rule).raw
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
        pure (← elaborateRecordedDeclRule name post inverse, (mkIdent name).raw)
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
    indexedRules := indexReplayRules rules
    premises := premiseProofs?.getD (event.premises.map (·.proof))
    reduction := none
    source
  }

private def traversalLocalRules? (slot : Nat) (phase : Phase) : Simp.SimpM (Array SimpTheorem) := do
  if slot == 0 then
    return #[]
  let context ← Simp.getContext
  let declarationIndex := context.lctxInitIndices + slot - 1
  let localContext ← getLCtx
  if declarationIndex >= localContext.numIndices then
    return #[]
  let some localDecl := localContext.getAt? declarationIndex
    | return #[]
  unless localDecl.index == declarationIndex do
    return #[]
  let metaSnapshot ← liftM Meta.saveState
  try
    liftM <| mkSimpTheoremFromExpr (.fvar localDecl.fvarId) #[] (mkFVar localDecl.fvarId)
      (post := phase == .post)
  catch _ =>
    liftM metaSnapshot.restore
    return #[]

private def applyRecordedRules? (input : Expr) (event : ReplayEvent)
    (ref : IO.Ref ReplayState) : Simp.SimpM (Option Simp.Result) := do
  let initial ← ref.get
  let mut lastFailure? : Option String := initial.premiseFailure?
  let indexedRules ← match event.localRuleSlot with
    | some slot => pure <| indexReplayRules (← traversalLocalRules? slot event.phase)
    | none => pure event.indexedRules
  for singleton in indexedRules do
    let snapshot ← ref.get
    ref.set { snapshot with premiseNext := 0, premiseFailure? := none }
    let metaSnapshot ← liftM Meta.saveState
    let result? ← try
      Simp.withDischarger (premiseProvider event.premises ref) false <|
        -- Replay the rule through the same discrimination index used by
        -- `simp`.  Calling `tryTheorem?` directly is observably broader: a
        -- constructor theorem such as `AddConstMap.coe_mk` can unify with an
        -- arbitrary structure fvar by eta-expanding it, even though the simp
        -- index would never offer that theorem at that site.  Match ordinals
        -- count actual simp-rule sites, so candidate selection is part of the
        -- operation being replayed.
        let tree := if event.phase == .post then singleton.post else singleton.pre
        Simp.rewrite? input tree singleton.erased (tag := "simp_explicit") (rflOnly := false)
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
          return some (if event.localRuleSlot.isSome then { result with cache := false } else result)
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

/- Recorded callback expressions below structural binders contain fvar ids
   whose local declarations no longer exist when certificate discovery runs.
   Compare those expressions modulo a first-occurrence renaming of free and
   metavariables.  This is only a selector anchor: the chosen operation still
   has to reproduce both the local result and the exact final subject state. -/
private structure ReplayCanonicalState where
  /-- Free variables from the tactic's ambient local context are semantic
      identities, not traversal binders, and must never be alpha-renamed. -/
  ambientFVars : Array FVarId := #[]
  fvars : Std.HashMap FVarId Nat := {}
  mvars : Std.HashMap MVarId Nat := {}
  levelMVars : Std.HashMap LMVarId Nat := {}
  nextFVar : Nat := 0
  nextMVar : Nat := 0
  nextLevelMVar : Nat := 0

private abbrev ReplayCanonicalM := StateM ReplayCanonicalState

private def replayCanonicalLevel : Level → ReplayCanonicalM String
  | .zero => pure "0"
  | .succ level => return s!"(succ {← replayCanonicalLevel level})"
  | .max lhs rhs => return s!"(max {← replayCanonicalLevel lhs} {← replayCanonicalLevel rhs})"
  | .imax lhs rhs => return s!"(imax {← replayCanonicalLevel lhs} {← replayCanonicalLevel rhs})"
  | .param name => pure s!"(param {name})"
  | .mvar mvarId => do
      let state ← get
      if let some ordinal := state.levelMVars.get? mvarId then
        return s!"l{ordinal}"
      modify fun _ => { state with
        levelMVars := state.levelMVars.insert mvarId state.nextLevelMVar
        nextLevelMVar := state.nextLevelMVar + 1 }
      return s!"l{state.nextLevelMVar}"

private partial def replayCanonicalExpr : Expr → ReplayCanonicalM String
  | .bvar index => pure s!"b{index}"
  | .fvar fvarId => do
      let state ← get
      if state.ambientFVars.contains fvarId then
        return s!"ambient:{repr fvarId}"
      if let some ordinal := state.fvars.get? fvarId then
        return s!"f{ordinal}"
      modify fun _ => { state with
        fvars := state.fvars.insert fvarId state.nextFVar
        nextFVar := state.nextFVar + 1 }
      return s!"f{state.nextFVar}"
  | .mvar mvarId => do
      let state ← get
      if let some ordinal := state.mvars.get? mvarId then
        return s!"m{ordinal}"
      modify fun _ => { state with
        mvars := state.mvars.insert mvarId state.nextMVar
        nextMVar := state.nextMVar + 1 }
      return s!"m{state.nextMVar}"
  | .sort level => return s!"(sort {← replayCanonicalLevel level})"
  | .const name levels =>
      return s!"(const {name} [{String.intercalate "," (← levels.mapM replayCanonicalLevel)}])"
  | .app fn arg => return s!"(app {← replayCanonicalExpr fn} {← replayCanonicalExpr arg})"
  | .lam _ type body binderInfo =>
      return s!"(lam {← replayCanonicalExpr type} {← replayCanonicalExpr body} {repr binderInfo})"
  | .forallE _ type body binderInfo =>
      return s!"(forall {← replayCanonicalExpr type} {← replayCanonicalExpr body} {repr binderInfo})"
  | .letE _ type value body nondep =>
      return s!"(let {← replayCanonicalExpr type} {← replayCanonicalExpr value} {← replayCanonicalExpr body} {nondep})"
  | .lit literal => pure s!"(lit {repr literal})"
  | .mdata _ expression => replayCanonicalExpr expression
  | .proj name index expression =>
      return s!"(proj {name} {index} {← replayCanonicalExpr expression})"

/- The projection key is deliberately local to one recording run.  It keeps
   the exact operation provenance, while the expression portions use the
   first-occurrence binder normalization above so callback-local fvar/mvar
   identifiers do not make identical transitions look different. -/
private def replayCanonicalOrigin : Origin → String
  | .decl name post inverse => s!"decl:{name}:{post}:{inverse}"
  | .fvar fvarId => s!"fvar:{repr fvarId}"
  | .stx id ref => s!"stx:{id}:{toString ref.prettyPrint}"
  | .other name => s!"other:{name}"

private def replayCanonicalReduction : ReductionKind → String
  | .delta name => s!"delta:{name}"
  | .beta => "beta"
  | .zeta => "zeta"
  | .iota => "iota"
  | .projection structureName field => s!"projection:{structureName}:{field}"
  | .projectionFunction name => s!"projection_function:{name}"
  | .localDef fvarId contextIndex name _ =>
      s!"local_def:{repr fvarId}:{contextIndex}:{name}"
  | .eta => "eta"

private def replayCanonicalEventKey (ambientFVars : Array FVarId)
    (event : RecordedEvent) : String :=
  let phase := match event.phase with
    | .pre => "pre"
    | .post => "post"
  let operation := match event.reduction with
    | some reduction => s!"reduction:{replayCanonicalReduction reduction.kind}"
    | none =>
        let origins := event.origins.map replayCanonicalOrigin
        s!"theorem:{String.intercalate "," origins.toList}"
  let initialState : ReplayCanonicalState := { ambientFVars }
  let (input, state) := (replayCanonicalExpr event.input).run initialState
  let (result, _) := (replayCanonicalExpr event.result.expr).run state
  s!"{phase}|{operation}|input={input}|result={result}"

private def replayAmbientFVars : Simp.SimpM (Array FVarId) := do
  let context ← Simp.getContext
  let localContext ← getLCtx
  let mut result := #[]
  for index in *...min context.lctxInitIndices localContext.numIndices do
    if let some declaration := localContext.getAt? index then
      if declaration.index == index then
        result := result.push declaration.fvarId
  return result

private def replayCanonicalExprMatches? (actual expected : Expr) : Simp.SimpM Bool := do
  let ambientFVars ← replayAmbientFVars
  let initialState : ReplayCanonicalState := { ambientFVars }
  let (actualKey, _) := (replayCanonicalExpr actual).run initialState
  let (expectedKey, _) := (replayCanonicalExpr expected).run initialState
  return actualKey == expectedKey

private def replayExprMatches? (actual expected : Expr) : Simp.SimpM Bool := do
  if Expr.equal actual expected then
    return true
  -- Historical callback expressions can contain traversal-local fvar ids
  -- whose declarations no longer exist.  Compare them modulo a stable
  -- first-occurrence renaming while preserving every ambient fvar identity.
  -- This is only a discovery anchor; replay still validates the selected
  -- operation and the final subject independently.
  if (← replayCanonicalExprMatches? actual expected) then
    return true
  -- Discovery is allowed a bounded reducible-definitional fallback, but the
  -- comparison itself must not leak assignments into either a skipped probe
  -- or the selected theorem application.
  let metaSnapshot ← liftM Meta.saveState
  try
    let result ← liftM (premiseDefEq? actual expected)
    liftM metaSnapshot.restore
    match result with
    | .ok true => return true
    | .ok false | .error _ => return false
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

private def replayIota? (input : Expr) : Simp.SimpM (Option Expr) := do
  let snapshot ← Meta.saveState
  try
    let output? ← Simp.withSimpMetaConfig <|
      withConfig (fun config => { config with beta := true, iota := true }) <|
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

private def replayProjectionFunction? (input : Expr) (name : Name) : Simp.SimpM (Option Expr) := do
  let .const head _ := input.getAppFn | return none
  unless head == name do
    return none
  let snapshot ← liftM Meta.saveState
  try
    let output? ← withConfig (fun config =>
      { config with beta := true, proj := .yesWithDelta }) <|
        reduceProjectionFunctionReplay? input
    match output? with
    | some output => return some output
    | none =>
        liftM snapshot.restore
        return none
  catch _ =>
    liftM snapshot.restore
    return none

private def replayEta? (input : Expr) : MetaM (Option Expr) := do
  let output := input.eta
  return if Expr.equal input output then none else some output

/-! A local-definition reduction is intentionally narrower than zeta.  It
    recognizes one exact ambient fvar/declaration and returns the value stored
    in the certificate identity.  No simplifier reduction, whnf, or local-name
    search is allowed here. -/
private def replayLocalDef? (input : Expr) (fvarId : FVarId)
    (contextIndex : Nat) (name : Name) (value : Expr) : Simp.SimpM (Option Expr) := do
  let .fvar inputFVarId := input | return none
  unless inputFVarId == fvarId do
    return none
  let localDecl ← try
    liftM fvarId.getDecl
  catch _ =>
    return none
  match localDecl with
  | .ldecl actualIndex actualFVarId actualName _ actualValue _ _ =>
      unless actualFVarId == fvarId && actualIndex == contextIndex && actualName == name do
        return none
      unless Expr.equal actualValue value do
        return none
      return some value
  | .cdecl .. =>
      return none

private def applyRecordedReduction? (input : Expr) (reduction : ReductionIdentity) :
    Simp.SimpM (Option Simp.Result) := do
  let output? ← match reduction.kind with
    | .delta name => replayDelta? input name
    | .beta => liftM <| replayBeta? input
    | .zeta => liftM <| replayZeta? input
    | .iota => replayIota? input
    | .projection structureName field => replayProjection? input structureName field
    | .projectionFunction name => replayProjectionFunction? input name
    | .localDef fvarId contextIndex name value =>
        replayLocalDef? input fvarId contextIndex name value
    | .eta => liftM <| replayEta? input
  return output?.bind (prooflessReductionResult? input)

private def hasUncommandedReduction (input : Expr) : Simp.SimpM Bool := do
  let iotaSnapshot ← liftM Meta.saveState
  let iota? ← replayIota? input
  liftM iotaSnapshot.restore
  if iota?.isSome then
    return true
  match input with
  | .proj structureName field _ =>
      let snapshot ← liftM Meta.saveState
      let output? ← replayProjection? input structureName field
      liftM snapshot.restore
      if output?.isSome then
        return true
  | _ => pure ()
  let .const _ _ := input.getAppFn | return false
  let snapshot ← liftM Meta.saveState
  -- Guard only reductions available to the neutral traversal. The explicit
  -- projection-function command has a stronger, locally scoped beta/proj
  -- configuration; using it here would reject expressions that the ambient
  -- replay engine cannot itself reduce.
  let output? ← Simp.withSimpMetaConfig <| reduceProjectionFunction? input
  liftM snapshot.restore
  return output?.isSome

private def applyReplayEvent? (input : Expr) (event : ReplayEvent)
    (ref : IO.Ref ReplayState) : Simp.SimpM (Option Simp.Result) := do
  match event.reduction with
  | some reduction => applyRecordedReduction? input reduction
  | none => applyRecordedRules? input event ref

/- `Simp.neutralConfig` deliberately keeps `contextual := false`, because
   enabling it would install every implication hypothesis into the ambient
   simp theorem collection.  A certificate containing `local_rule` still
   needs the pinned contextual implication *traversal* so that its exact slot
   exists.  Mirror that one congruence branch without `withNewLemmas`: the
   hypothesis enters the local context, but only an explicit `local_rule n`
   command can use it. -/
private def replayContextualArrow (input : Expr) : Simp.SimpM Simp.Result := do
  let .forallE binderName proposition consequence _ := input
    | return { expr := input }
  let propositionResult ← Simp.simp proposition
  withLocalDeclD binderName propositionResult.expr fun hypothesis => do
    -- Pinned `withNewLemmas` gives each contextual binder a fresh cache. Keep
    -- that structural boundary even though this replay deliberately omits
    -- its ambient-theorem insertion branch.
    Simp.withFreshCache do
      let consequenceResult ← Simp.simp consequence
      match consequenceResult.proof? with
      | none =>
          Simp.mkImpCongr input propositionResult consequenceResult
      | some consequenceProof =>
          let consequenceProof ← mkLambdaFVars #[hypothesis] consequenceProof
          if consequenceResult.expr.containsFVar hypothesis.fvarId! then
            return {
              expr := ← mkForallFVars #[hypothesis] consequenceResult.expr
              proof? := ← withDefault <|
                mkImpDepCongrCtx (← propositionResult.getProof) consequenceProof
            }
          else
            return {
              expr := input.updateForallE! propositionResult.expr consequenceResult.expr
              proof? := ← withDefault <|
                mkImpCongrCtx (← propositionResult.getProof) consequenceProof
            }

private def replayMethod (events : Array ReplayEvent) (hasLocalRules : Bool)
    (ref : IO.Ref ReplayState) (phase : Phase) : Simp.Simproc := fun input => do
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
    throwError "simp_explicit encountered a reducible iota, native projection, or projection function without an explicit reduction command"
  if phase == .pre && hasLocalRules then
    match input with
    | .forallE _ proposition consequence _ =>
        if !consequence.hasLooseBVars && (← isProp proposition) && (← isProp consequence) then
          -- `continue` preserves the contextual congruence proof while allowing the
          -- ordinary post hook to consume a following command on the rebuilt arrow.
          return .continue (some (← replayContextualArrow input))
    | _ => pure ()
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
  let hasLocalRules := events.any (fun event => event.localRuleSlot.isSome)
  let methods : Simp.Methods := {
    pre := replayMethod events hasLocalRules ref .pre
    post := replayMethod events hasLocalRules ref .post
    discharge? := fun _ => return none
  }
  let (result, _) ← Simp.mainCore target ctx (methods := methods)
  return (result, ← ref.get)

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
  if event.localRuleSlot.isSome then
    return "unvalidated_named_rule"
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

private def originIsSimproc (origin : Origin) : TacticM Bool := do
  match origin with
  | .decl name _ _ =>
      return (← Simp.isBuiltinSimproc name) || (← Simp.isSimproc name)
  | _ =>
      return false

/- The simproc boundary is recursive.  A simproc used only while discharging
   a theorem premise still makes the enclosing source program non-operational;
   do not let a flat replay/proof fallback hide that child callback. -/
mutual
  private partial def deferredSimprocEventEncoding (event : RecordedEvent) :
      TacticM (EventEncodingInfo × Nat) := do
    let mut ownSimproc := false
    for origin in event.origins do
      if !ownSimproc && (← originIsSimproc origin) then
        ownSimproc := true
    let mut premiseInfos : Array PremiseEncodingInfo := #[]
    let mut nestedCount := 0
    for premise in event.premises do
      let mut commands : Array EventEncodingInfo := #[]
      let mut premiseCount := 0
      for child in premise.events do
        let (childInfo, childCount) ← deferredSimprocEventEncoding child
        commands := commands.push childInfo
        premiseCount := premiseCount + childCount
      let premiseKind := if premiseCount > 0 then "deferred_nested" else "unencoded"
      let premiseReason := if premiseCount > 0 then some "deferred_simproc" else none
      premiseInfos := premiseInfos.push {
        kind := premiseKind
        reason := premiseReason
        bindingName := none
        bytes := 0
        commands
      }
      nestedCount := nestedCount + premiseCount
    let total := nestedCount + (if ownSimproc then 1 else 0)
    let kind := if ownSimproc then "deferred_simproc"
      else if nestedCount > 0 then "deferred_nested" else "unencoded"
    let reason := if total > 0 then some "simproc" else none
    return ({
      kind
      reason
      premises := premiseInfos
    }, total)

  private partial def deferredSimprocEncoding (events : Array RecordedEvent) :
      TacticM (Option (Array EventEncodingInfo × Array (Array PremiseEncodingInfo) × Nat)) := do
    let mut infos : Array EventEncodingInfo := #[]
    let mut premiseInfos : Array (Array PremiseEncodingInfo) := #[]
    let mut total := 0
    for event in events do
      let (info, count) ← deferredSimprocEventEncoding event
      infos := infos.push info
      premiseInfos := premiseInfos.push info.premises
      total := total + count
    if total == 0 then
      return none
    return some (infos, premiseInfos, total)
end

/-- Preserve the complete recursive trace shape when a premise-bearing event
    cannot yet be compiled.  The simproc partition has already run, so every
    node produced here is an ordinary unencoded operational coverage gap. -/
private def unencodedHierarchy (events : Array RecordedEvent) :
    TacticM (Array EventEncodingInfo × Array (Array PremiseEncodingInfo)) := do
  let mut infos : Array EventEncodingInfo := #[]
  let mut premiseInfos : Array (Array PremiseEncodingInfo) := #[]
  for event in events do
    let (info, _) ← deferredSimprocEventEncoding event
    infos := infos.push info
    premiseInfos := premiseInfos.push info.premises
  return (infos, premiseInfos)

/- Once the authoritative `Simp.dischargeRfl` has assigned its temporary
   theorem metavariables, the recorded residual is a closed proposition.  The
   source replay therefore uses only the fixed reflexive proof for that exact
   residual; it does not rediscover a terminal by trying arbitrary closure
   procedures. -/
private def rebuildRecordedDischargeRfl? (residual : Expr) : TacticM (Option Expr) := do
  try
    let proof? ← forallTelescope residual fun xs body => do
      let some (type, lhs, rhs) := body.eq? | pure none
      if !(← isDefEq lhs rhs) then
        pure none
      else
        let level ← getLevel type
        let proof := mkApp2 (.const ``rfl [level]) type lhs
        some <$> mkLambdaFVars xs proof
    return proof?
  catch _ =>
    return none

private def rebuildEquationHypothesis? (proposition : Expr) :
    TacticM (Option Expr) := do
  unless Simp.isEqnThmHypothesis proposition do
    return none
  let snapshot ← Meta.saveState
  try
    let some proof ← Simp.dischargeEqnThmHypothesis? proposition
      | snapshot.restore
        return none
    let proof ← instantiateMVars proof
    unless ← isDefEq (← inferType proof) proposition do
      snapshot.restore
      return none
    return some proof
  catch _ =>
    snapshot.restore
    return none

private def rebuildPremiseProof? (premise : RecordedPremise)
    (nestedResult : Simp.Result) : TacticM (Option Expr) := do
  let proposition ← instantiateMVars premise.proposition
  let resultExpr ← instantiateMVars nestedResult.expr
  let proof? ← match premise.terminal with
    | .isTrue _ =>
        if !resultExpr.isTrue then
          pure none
        else
          match nestedResult.proof? with
          | some equality => some <$> mkOfEqTrue equality
          | none => pure (some (mkConst ``True.intro))
    | .dischargeRfl recordedResult =>
        let recordedResult ← instantiateMVars recordedResult
        let residual := if recordedResult.hasMVar then proposition else recordedResult
        if !(← isDefEq residual resultExpr) then
          pure none
        else
          let some rflProof ← rebuildRecordedDischargeRfl? resultExpr
            | pure none
          let equality ← Simp.Result.getProof' proposition nestedResult
          pure <| some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) proposition resultExpr
            equality rflProof)
    | .localAssumption fvarId _ _ =>
        pure (some (mkFVar fvarId))
    | .equationHypothesis =>
        rebuildEquationHypothesis? proposition
    | .custom => pure none
  let some proof := proof? | return none
  let proof ← instantiateMVars proof
  unless ← isDefEq (← inferType proof) proposition do
    return none
  return some proof

private def isReflexiveResultEarly (expr : Expr) : MetaM Bool := do
  if expr.isTrue then
    return true
  if expr.isAppOfArity ``Eq 3 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  if expr.isAppOfArity ``Iff 2 then
    return ← isDefEq expr.appFn!.appArg! expr.appArg!
  return false

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
      lines := lines.push s!"have {binding.name} : (\n{indentSource "  " binding.typeText}\n) :="
      lines := lines.push s!"  {indentSource "  " binding.proofText}"
    let eventList := certificatePlanEventListText events
    let command := if leaveOpen then "simp_explicit leave_open " else "simp_explicit "
    if bindings.isEmpty then
      return command ++ eventList
    lines := lines.push (command ++ eventList)
    return String.intercalate "\n" lines.toList

private inductive CertificateSelectorMode where
  | next
  | discover
  | ticks

private def reachesSearchedResult? (searchedResult replayedResult : Simp.Result) : TacticM Bool := do
  if searchedResult.expr.isTrue then
    isReflexiveResultEarly replayedResult.expr
  else
    isDefEq searchedResult.expr replayedResult.expr

private def replayResultWellFormed? (result : Simp.Result) : MetaM Bool := do
  let localContext ← getLCtx
  unless ← MetavarContext.isWellFormed localContext result.expr do
    return false
  match result.proof? with
  | none => return true
  | some proof => return ← MetavarContext.isWellFormed localContext proof

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
    unless ← replayResultWellFormed? replayedResult do
      return none
    let reaches ← reachesSearchedResult? searchedResult replayedResult
    unless reaches do
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

private structure ProjectedSelection where
  selected : Array EncodedEvent
  seen : Array String
  selectedRawIndices : Array Nat

private def projectSelectedEvents? (target : Expr) (searchedResult : Simp.Result)
    (encoded : Array EncodedEvent) : TacticM (Option ProjectedSelection) := do
  try
    if encoded.any (fun event => event.info.kind == "generated_proof") then
      return none
    let mut deduplicated : Array EncodedEvent := #[]
    let mut seen : Array String := #[]
    let mut selectedRawIndices : Array Nat := #[]
    let ambientFVars := (← getLCtx).getFVarIds
    for index in *...encoded.size do
      let some event := encoded[index]? | return none
      let key := replayCanonicalEventKey ambientFVars event.event
      match seen.findIdx? (· == key) with
      | some groupIndex =>
          deduplicated := deduplicated.set! groupIndex event
          selectedRawIndices := selectedRawIndices.set! groupIndex index
      | none =>
          seen := seen.push key
          deduplicated := deduplicated.push event
          selectedRawIndices := selectedRawIndices.push index
    deduplicated := deduplicated.map fun event =>
      let key := replayCanonicalEventKey ambientFVars event.event
      let multiplicity := encoded.foldl (fun count candidate =>
        if replayCanonicalEventKey ambientFVars candidate.event == key then count + 1 else count) (0 : Nat)
      if multiplicity > 1 then
        { event with replay := { event.replay with selector := .matchSite multiplicity } }
      else
        event
    -- Historical transition identity is authoritative for source selection:
    -- discover each recorded input/result before considering generic first-site
    -- replay. A generic declaration can otherwise rewrite an earlier site and
    -- coincidentally reach the same final state.
    let selected? ← match (← selectCertificateEvents? target searchedResult deduplicated .discover) with
      | some selected => pure (some selected)
      | none =>
          match (← selectCertificateEvents? target searchedResult deduplicated .next) with
          | some selected => pure (some selected)
          | none => selectCertificateEvents? target searchedResult deduplicated .ticks
    let some selected := selected? | return none
    return some {
      selected := annotateSelectorInfo selected
      seen
      selectedRawIndices
    }
  catch _ =>
    return none

private def projectedRawEncodingInfos (encoded : Array EncodedEvent)
    (projection : ProjectedSelection) : TacticM (Array EventEncodingInfo × Nat) := do
  let ambientFVars := (← getLCtx).getFVarIds
  let mut infos : Array EventEncodingInfo := #[]
  let mut nonmaterial := 0
  for index in *...encoded.size do
    let some rawEvent := encoded[index]? | throwError "missing projected raw event"
    let key := replayCanonicalEventKey ambientFVars rawEvent.event
    let some groupIndex := projection.seen.findIdx? (· == key)
      | throwError "projected raw event was not assigned to a selector group"
    if projection.selectedRawIndices[groupIndex]? == some index then
      let some selectedEvent := projection.selected[groupIndex]? | throwError "missing selected event"
      infos := infos.push selectedEvent.info
    else
      nonmaterial := nonmaterial + 1
      infos := infos.push {
        kind := "nonmaterial_internal_execution"
        reason := some "nonmaterial_internal_execution"
      }
  return (infos, nonmaterial)

private partial def buildEncodedEvents? (recorded : Array RecordedEvent)
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
      -- Simproc callbacks remain a deferred boundary.  Do this classification
      -- before the compact named-rule path: exact attribution gives a
      -- simproc callback one origin, but that origin is not a source replay
      -- theorem and must not be mistaken for an ordinary named rule.
      let fallbackReason? ← try
        some <$> fallbackReason event
      catch _ =>
        pure none
      -- A named event may be under a traversal binder, so its isolated
      -- callback input is not necessarily replayable in the current local
      -- context.  Construct the named rule without claiming that this local
      -- probe validates it; the complete ordered program below remains the
      -- acceptance check.
      let replay? ← try
        if fallbackReason? == some "simproc" then
          pure none
        else if event.reduction.isSome || event.origins.size == 1 then
          pure (some ())
        else
          pure none
      catch _ =>
        pure none
      if replay?.isSome then
        let rule ← match event.reduction with
          | some reduction => reductionSource reduction event.phase
          | none => do
              unless event.localRuleSlot.isSome || event.origins.size == 1 do
                throwError "simp_explicit cannot encode semantic event {index}: observed {event.origins.size} diagnostic origin candidates"
              let rule ← recordedRuleText event
              pure rule
        let mut premiseNames := #[]
        let mut premiseEncodings := #[]
        let mut premiseProofs := #[]
        for premiseIndex in *...event.premises.size do
          let some premise := event.premises[premiseIndex]? | return none
          let proposition ← instantiateMVars premise.proposition
          let some (nestedEncoded, nestedBindings, _) ←
              buildEncodedEvents? premise.events usedNames
            | return none
          let terminalResult := match premise.terminal with
            | .isTrue result => result
            | .dischargeRfl result => result
            | _ => proposition
          let (nestedSelected, nestedResult, nestedCommands) ← if premise.events.isEmpty then
              let (replayedResult, _) ← runReplay proposition #[]
              pure ((#[] : Array EncodedEvent), replayedResult, #[])
            else
              let some projection ← projectSelectedEvents? proposition
                  { expr := terminalResult } nestedEncoded
                | return none
              let selected := projection.selected
              let (replayedResult, replayState) ←
                runReplay proposition (selected.map (·.replay))
              unless replayState.next == selected.size do
                return none
              let (commands, _) ← projectedRawEncodingInfos nestedEncoded projection
              pure (selected, replayedResult, commands)
          let some rebuiltProof ← rebuildPremiseProof? premise nestedResult
            | return none
          let name ← freshPremiseBindingName premiseIndex usedNames
          let sourceNamespace := ((← Term.getDeclName?).map (·.getPrefix)).getD Name.anonymous
          let rendered ← ProofExport.renderType proposition (config := {
            sourceNamespace
            shareSubterms := false
          })
          let leaveOpen := match premise.terminal with
            | .dischargeRfl _ => true
            | _ => false
          let nestedSource := certificatePlanText nestedSelected nestedBindings leaveOpen
          let (kind, proofText) ← match premise.terminal with
            | .isTrue _ =>
                pure ("premise_nested", s!"by\n  {indentSource "  " nestedSource}")
            | .dischargeRfl _ =>
                pure ("premise_dischargeRfl",
                  s!"by\n  {indentSource "  " nestedSource}\n  simp_explicit_premise dischargeRfl")
            | .localAssumption fvarId _ storedName =>
                let localName ← try
                  pure (← fvarId.getDecl).userName
                catch _ =>
                  pure storedName
                pure ("premise_local_assumption", s!"by\n  exact {localName}")
            | .equationHypothesis =>
                pure ("premise_equation_hypothesis",
                  "by\n  simp_explicit_premise equationHypothesis")
            | .custom => return none
          let typeText := rendered.valueText
          let bytes := typeText.utf8ByteSize + proofText.utf8ByteSize
          let binding : GeneratedBinding := {
            name
            kind
            type := proposition
            proof := rebuiltProof
            typeText
            proofText
            bytes
          }
          usedNames := usedNames.push binding.name
          bindings := bindings.push binding
          premiseNames := premiseNames.push binding.name
          premiseProofs := premiseProofs.push binding.proof
          premiseEncodings := premiseEncodings.push {
            kind
            reason := none
            bindingName := some name
            bytes
            commands := nestedCommands
          }
        let replay ← recordedReplayEvent event .next (some premiseProofs)
        encoded := encoded.push {
          event
          replay
          info := {
            kind := if event.reduction.isSome then "reduction" else "named_rule"
            reason := none
            selectorKind := some "next"
            deltaReduction := match event.reduction with
              | some { kind := .delta .. } => true
              | _ => false
            premises := premiseEncodings
          }
          ruleText := rule
          premiseNames
          premiseEncodings
          binding? := none
        }
      else
        let reason ← match fallbackReason? with
          | some reason => pure reason
          | none => fallbackReason event
        if reason == "multiple_origins" || reason == "special_rule" then
          -- These are precise coverage failures.  They must not be hidden by
          -- a generated theorem binding: either candidate attribution was
          -- incomplete or the rule has no source-reachable identity.
          return none
        unless event.premises.isEmpty do
          -- Premise-bearing events are accepted only with an operational
          -- terminal program; an authoritative proof-term fallback is never
          -- an admissible encoding.
          return none
        -- Every accepted event must be replayable from a recorded theorem or
        -- explicit reduction.  The historical generated-proof branch is
        -- deliberately removed: its authoritative proof is not an
        -- operational certificate and must never become source.
        return none
    return some (encoded, bindings, usedNames)
  catch _ =>
    return none

private structure ProjectedCertificateEvents where
  selected : Array EncodedEvent
  rawEncodingInfos : Array EventEncodingInfo
  rawPremiseEncodingInfos : Array (Array PremiseEncodingInfo)
  nonmaterialInternalEvents : Nat

/-- Select an order-preserving executable projection of the raw trace.
    Repeated callbacks with the same exact canonical local transition are
    represented by one command selecting the last successful matching site;
    this skips speculative congruence executions while retaining the committed
    transition. Ambient free-variable identities remain part of the key. The
    complete projected sequence must still reach the exact recorded result. -/
private def projectCertificateEvents? (target : Expr) (searchedResult : Simp.Result)
    (encoded : Array EncodedEvent) : TacticM (Option ProjectedCertificateEvents) := do
  try
    let some projection ← projectSelectedEvents? target searchedResult encoded
      | return none
    let selected := projection.selected
    let (rawInfos, nonmaterialInternalEvents) ← projectedRawEncodingInfos encoded projection
    let mut rawPremiseInfos : Array (Array PremiseEncodingInfo) := #[]
    for index in *...encoded.size do
      let some _ := encoded[index]? | return none
      let some info := rawInfos[index]? | return none
      rawPremiseInfos := rawPremiseInfos.push info.premises
    return some {
      selected
      rawEncodingInfos := rawInfos
      rawPremiseEncodingInfos := rawPremiseInfos
      nonmaterialInternalEvents
    }
  catch _ =>
    return none

/- Recursive premise counts describe the operational tree, while byte fields
   remain the source footprint of the outer binding that owns each nested
   program.  Summing nested bytes would count embedded source twice. -/
private structure RecursiveEncodingTotals where
  premiseBindingCount : Nat := 0
  nestedPremiseBindings : Nat := 0
  termPremiseBindings : Nat := 0
  namedRuleEvents : Nat := 0
  reductionEvents : Nat := 0
  deltaReductionEvents : Nat := 0
  nonmaterialInternalEvents : Nat := 0
  generatedProofEvents : Nat := 0
  generatedSimprocEvents : Nat := 0
  generatedSpecialEvents : Nat := 0
  nextSelectorCount : Nat := 0
  matchSelectorCount : Nat := 0
  tickSelectorCount : Nat := 0
  deriving Nonempty

private def addRecursiveEncodingTotals (lhs rhs : RecursiveEncodingTotals) : RecursiveEncodingTotals := {
  premiseBindingCount := lhs.premiseBindingCount + rhs.premiseBindingCount
  nestedPremiseBindings := lhs.nestedPremiseBindings + rhs.nestedPremiseBindings
  termPremiseBindings := lhs.termPremiseBindings + rhs.termPremiseBindings
  namedRuleEvents := lhs.namedRuleEvents + rhs.namedRuleEvents
  reductionEvents := lhs.reductionEvents + rhs.reductionEvents
  deltaReductionEvents := lhs.deltaReductionEvents + rhs.deltaReductionEvents
  nonmaterialInternalEvents := lhs.nonmaterialInternalEvents + rhs.nonmaterialInternalEvents
  generatedProofEvents := lhs.generatedProofEvents + rhs.generatedProofEvents
  generatedSimprocEvents := lhs.generatedSimprocEvents + rhs.generatedSimprocEvents
  generatedSpecialEvents := lhs.generatedSpecialEvents + rhs.generatedSpecialEvents
  nextSelectorCount := lhs.nextSelectorCount + rhs.nextSelectorCount
  matchSelectorCount := lhs.matchSelectorCount + rhs.matchSelectorCount
  tickSelectorCount := lhs.tickSelectorCount + rhs.tickSelectorCount
}

private def directRecursiveEncodingTotals (event : EventEncodingInfo) : RecursiveEncodingTotals := {
  namedRuleEvents := if event.kind == "named_rule" then 1 else 0
  reductionEvents := if event.kind == "reduction" then 1 else 0
  deltaReductionEvents := if event.deltaReduction then 1 else 0
  nonmaterialInternalEvents :=
    if event.kind == "nonmaterial_internal_execution" then 1 else 0
  generatedProofEvents := if event.kind == "generated_proof" then 1 else 0
  generatedSimprocEvents := if event.reason == some "simproc" &&
      event.kind == "generated_proof" then 1 else 0
  generatedSpecialEvents := if event.reason == some "special_rule" then 1 else 0
  nextSelectorCount := if event.selectorKind == some "next" then 1 else 0
  matchSelectorCount := if event.selectorKind == some "match" then 1 else 0
  tickSelectorCount := if event.selectorKind == some "tick" then 1 else 0
}

mutual
  private partial def premiseEncodingTotals (premises : Array PremiseEncodingInfo) :
      RecursiveEncodingTotals := Id.run do
    let mut totals : RecursiveEncodingTotals := {}
    for premise in premises do
      let childTotals := eventEncodingTotals premise.commands
      let direct : RecursiveEncodingTotals := {
        premiseBindingCount := if premise.bindingName.isSome then 1 else 0
        nestedPremiseBindings := if premise.kind == "premise_nested" then 1 else 0
        termPremiseBindings := if premise.kind == "premise_term" then 1 else 0
      }
      totals := addRecursiveEncodingTotals totals
        (addRecursiveEncodingTotals direct childTotals)
    return totals

  private partial def eventEncodingTotals (events : Array EventEncodingInfo) :
      RecursiveEncodingTotals := Id.run do
    let mut totals : RecursiveEncodingTotals := {}
    for event in events do
      totals := addRecursiveEncodingTotals totals (directRecursiveEncodingTotals event)
      totals := addRecursiveEncodingTotals totals (premiseEncodingTotals event.premises)
    return totals
end

private def makeCertificatePlan (searchedResult : Simp.Result)
    (encoded : Array EncodedEvent) (bindings : Array GeneratedBinding)
    (rawEncodingInfos : Array EventEncodingInfo := #[])
    (rawPremiseEncodingInfos : Array (Array PremiseEncodingInfo) := #[])
    (nonmaterialInternalEvents : Nat := 0) : TacticM CertificatePlan := do
  let leaveOpen ← if searchedResult.expr.isTrue then pure false else
    isReflexiveResultEarly searchedResult.expr
  let source := certificatePlanText encoded bindings leaveOpen
  let recursiveTotals := eventEncodingTotals (encoded.map (·.info))
  let generatedBindingBytes := bindings.foldl (fun n binding => n + binding.bytes) 0
  let premiseEncodings := encoded.foldl (fun result event => result ++ event.premiseEncodings) #[]
  let premiseBindingCount := recursiveTotals.premiseBindingCount
  let nestedPremiseBindings := recursiveTotals.nestedPremiseBindings
  let termPremiseBindings := recursiveTotals.termPremiseBindings
  let directPremiseBindingCount := premiseEncodings.foldl (fun n encoding =>
    if encoding.bindingName.isSome then n + 1 else n) 0
  let premiseBindingBytes := premiseEncodings.foldl (fun n encoding => n + encoding.bytes) 0
  let rawEncodingInfos := if rawEncodingInfos.isEmpty && !encoded.isEmpty then
      encoded.map (·.info)
    else
      rawEncodingInfos
  let rawPremiseEncodingInfos := if rawPremiseEncodingInfos.isEmpty && !encoded.isEmpty then
      encoded.map (·.premiseEncodings)
    else
      rawPremiseEncodingInfos
  return {
    events := encoded
    bindings
    positions := recursiveTotals.tickSelectorCount > 0
    source
    metrics := {
      namedRuleEvents := recursiveTotals.namedRuleEvents
      reductionEvents := recursiveTotals.reductionEvents
      deltaReductionEvents := recursiveTotals.deltaReductionEvents
      -- The projection count covers raw top-level callbacks; this recursive
      -- total adds only nonmaterial command metadata nested under selected
      -- premise programs.
      nonmaterialInternalEvents :=
        nonmaterialInternalEvents + recursiveTotals.nonmaterialInternalEvents
      generatedProofEvents := recursiveTotals.generatedProofEvents
      generatedSimprocEvents := recursiveTotals.generatedSimprocEvents
      generatedSpecialEvents := recursiveTotals.generatedSpecialEvents
      -- `bindings` owns the source text at this scope; add only descendant
      -- premise bindings to avoid counting direct premise bindings twice.
      generatedBindingCount := bindings.size + (premiseBindingCount - directPremiseBindingCount)
      generatedBindingBytes
      premiseBindingCount
      premiseBindingBytes
      nestedPremiseBindings
      termPremiseBindings
      nextSelectorCount := recursiveTotals.nextSelectorCount
      matchSelectorCount := recursiveTotals.matchSelectorCount
      tickSelectorCount := recursiveTotals.tickSelectorCount
      totalCertificateBytes := source.utf8ByteSize
    }
    rawEncodingInfos
    rawPremiseEncodingInfos
  }

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
      unless ← replayResultWellFormed? replayedResult do
        return false
      return ← reachesSearchedResult? searchedResult replayedResult
  catch _ =>
    return false

private def replayEncoding? (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) : TacticM (Option (Array ReplaySelector)) := do
  if let some discovered ← discoverSelectors? target recorded then
    if ← canReplayWithSelectors target recorded searchedResult discovered then
      return some discovered
  let next := nextSelectors recorded
  if ← canReplayWithSelectors target recorded searchedResult next then
    return some next
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
  if let some discovered ← discoverSelectors? target recorded then
    if ← contextCanReplayWithSelectors target recorded searchedResult discovered then
      return some discovered
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

private def maxBridgeCandidates : Nat := 8

private partial def projectionFunctionNameOccurrences (expression : Expr)
    (fuel : Nat := 256) : MetaM (Array Name) := do
  if fuel == 0 then
    return #[]
  let mut result := #[]
  if let .const name _ := expression.getAppFn then
    if expression.isApp && (← isProjectionFn name) then
      result := result.push name
  for (_, child) in expressionChildren expression do
    result := result ++ (← projectionFunctionNameOccurrences child (fuel - 1))
  return result

private def boundedProjectionFunctionCandidates (expression : Expr) : MetaM (Array Name) := do
  let occurrences ← projectionFunctionNameOccurrences expression
  let mut result := #[]
  for name in occurrences do
    if result.size >= maxBridgeCandidates then
      break
    unless result.contains name do
      result := result.push name
  return result

/- The local-definition bridge is deliberately not a search over the ambient
   context.  A candidate must be an fvar structurally present in the already
   matched gap expression, and its declaration must be an accessible local
   let with a value. -/
private def localDefReduction? (expression : Expr) : MetaM (Option ReductionIdentity) := do
  let .fvar fvarId := expression | return none
  let localDecl ← try
    fvarId.getDecl
  catch _ =>
    return none
  match localDecl with
  | .ldecl contextIndex declarationFVarId name _ value _ _ =>
      if declarationFVarId == fvarId && !name.isInaccessibleUserName then
        return some { kind := .localDef fvarId contextIndex name value }
      return none
  | .cdecl .. =>
      return none

private partial def localDefOccurrences (expression : Expr)
    (fuel : Nat := 256) : MetaM (Array (Expr × ReductionIdentity)) := do
  if fuel == 0 then
    return #[]
  let mut result := #[]
  if let some reduction ← localDefReduction? expression then
    result := result.push (expression, reduction)
  for (_, child) in expressionChildren expression do
    result := result ++ (← localDefOccurrences child (fuel - 1))
  return result

private def boundedLocalDefCandidates (expression : Expr) : MetaM
    (Array (Expr × ReductionIdentity)) := do
  let occurrences ← localDefOccurrences expression
  let mut result := #[]
  let mut seen : Array FVarId := #[]
  for occurrence in occurrences do
    if result.size >= maxBridgeCandidates then
      break
    let (_, reduction) := occurrence
    let .localDef fvarId _ _ _ := reduction.kind | continue
    unless seen.contains fvarId do
      seen := seen.push fvarId
      result := result.push occurrence
  return result

private structure CertificateBridgePrefix where
  firstUnconsumed : Nat
  selectors : Array ReplaySelector
  prefixExpr : Expr
  matched : DefEqSubexpression
  event : RecordedEvent

private def certificateBridgePrefix? (target : Expr) (recorded : Array RecordedEvent) :
    TacticM (Option CertificateBridgePrefix) := do
  let count := certificateEventCount recorded
  if count == 0 then
    return none
  let nextSelectors : Array ReplaySelector := Array.replicate recorded.size (.next : ReplaySelector)
  let matchSelectors : Array ReplaySelector := recorded.map
    (fun event => .discover event.input event.result.expr)
  let tickSelectors : Array ReplaySelector := recorded.map
    (fun event => .tickPos event.tick)
  let nextConsumedCount := (← continuityReplayCount? target recorded nextSelectors).getD 0
  let matchConsumedCount := (← continuityReplayCount? target recorded matchSelectors).getD 0
  let tickConsumedCount := (← continuityReplayCount? target recorded tickSelectors).getD 0
  let bestCount := max nextConsumedCount (max matchConsumedCount tickConsumedCount)
  if bestCount >= count then
    return none
  let bestSelectors :=
    if nextConsumedCount >= matchConsumedCount && nextConsumedCount >= tickConsumedCount then
      nextSelectors
    else if matchConsumedCount >= tickConsumedCount then
      matchSelectors
    else
      tickSelectors
  let some event := recorded[bestCount]? | return none
  -- A missing transition can precede either a named theorem (the O6e/O6g
  -- projection bridges) or an already recorded reduction (local-let
  -- expansion followed by zeta).  In both cases the next event itself must
  -- still have a single explicit replay identity.
  unless event.reduction.isSome || event.origins.size == 1 do
    return none
  let some prefixExpr ← continuityPrefixReplay? target recorded bestSelectors bestCount
    | return none
  let some matched ← firstDefEqSubexpression? prefixExpr event.input
    | return none
  return some {
    firstUnconsumed := bestCount
    selectors := bestSelectors
    prefixExpr
    matched
    event
  }

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
  -- Continuity-gap diagnosis starts with the first-applicable operational
  -- prefix.  This helper locates omitted reductions; it does not select the
  -- final source selectors, whose accepted paths prefer historical discovery.
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
  let lctx ← getLCtx
  let (canonical, _) := (canonicalExpr lctx expression).run {}
  let printable ← try
    let rendered ← withOptions
        (pp.mvars.set · false |>.set pp.mvars.levels.name false
          |>.set pp.fvars.anonymous.name false) <| ppExpr expression
    pure (toString rendered)
  catch _ =>
    -- Contextual simplification records callbacks below temporary binders.
    -- Their local declarations are gone by report time, but their normalized
    -- expression remains useful diagnostic data and contains no raw ids.
    pure s!"<callback-local expression> {canonical}"
  -- A free variable that is not present in the diagnostic reader can otherwise
  -- be rendered as Lean's internal `_fvar._` placeholder.  Keep that
  -- diagnostic stable and explicitly non-identity-bearing in persistent JSON;
  -- source rendering uses the original expression and is unaffected.
  let printable := printable.replace "_fvar._" "<free-variable>"
  let printable := if printable.length > 512 then (printable.take 512).toString ++ "…" else printable
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
      let decl? ← try
        some <$> fvarId.getDecl
      catch _ =>
        pure none
      match decl? with
      | some decl =>
          return {
            kind := "fvar"
            name := decl.userName.toString
            inverse := false
            source := none
          }
      | none =>
          -- The source certificate encoder has already decided whether this
          -- origin is replayable.  Persistent diagnostics must not fail only
          -- because a contextual callback's binder has left the local context.
          return {
            kind := "fvar"
            name := "<callback-local>"
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

private def syntheticBridgeReductionEvent (input : Expr)
    (reduction : ReductionIdentity) : TacticM EncodedEvent := do
  let event : RecordedEvent := {
    tick := 0
    phase := .pre
    input
    step := .visit { expr := input }
    result := { expr := input }
    origins := #[]
    premises := #[]
    reduction := some reduction
  }
  let replay : ReplayEvent := {
    selector := .next
    phase := .pre
    rules := #[]
    premises := #[]
    reduction := some reduction
    source := (mkIdent `reduce).raw
  }
  return {
    event
    replay
    info := {
      kind := "reduction"
      reason := none
      selectorKind := some "next"
      selectorValue := none
      deltaReduction := match reduction.kind with
        | .delta _ => true
        | _ => false
    }
    ruleText := ← reductionSource reduction .pre
    binding? := none
  }

private def bridgeCertificatePlan? (target : Expr) (searchedResult : Simp.Result)
    (baseEncoded : Array EncodedEvent) (bindings : Array GeneratedBinding)
    (bridge : CertificateBridgePrefix) : TacticM (Option CertificatePlan) := do
  unless bridge.firstUnconsumed <= baseEncoded.size do
    return none
  let rawWithNext := annotateSelectorInfo <| baseEncoded.map fun event =>
    { event with replay := { event.replay with selector := .next } }
  let rawEncodingInfos := baseEncoded.map (·.info)
  let rawPremiseEncodingInfos := baseEncoded.map (·.premiseEncodings)
  -- A local let is the shortest possible continuity bridge. Its identity is
  -- taken only from fvars structurally present in the matched expression; no
  -- ambient declaration search is performed. Validate the complete augmented
  -- program before returning it.
  let localDefCandidates ← boundedLocalDefCandidates bridge.matched.expression
  for (subject, reduction) in localDefCandidates do
    let localDef0 ← syntheticBridgeReductionEvent subject reduction
    let .localDef _ _ _ value := reduction.kind | return none
    -- Discovery needs the real transition endpoints.  Unlike the older
    -- projection bridge, this operation knows its exact output without
    -- executing a simplifier reduction: it is the stored local-let value.
    let localDef := {
      localDef0 with
        event := {
          localDef0.event with
            step := .visit { expr := value }
            result := { expr := value }
        }
    }
    let mut augmented := baseEncoded.take bridge.firstUnconsumed
    augmented := augmented.push localDef
    augmented := augmented ++ baseEncoded.drop bridge.firstUnconsumed
    -- The newly exposed value can change which occurrence of a later theorem
    -- is historical.  Re-run the already bounded selector discovery on the
    -- complete augmented trace; do not guess by choosing the first site.
    for mode in #[CertificateSelectorMode.discover, CertificateSelectorMode.next,
        CertificateSelectorMode.ticks] do
      let selected? ← withoutModifyingState do
        selectCertificateEvents? target searchedResult augmented mode
      if let some selected := selected? then
        return some (← makeCertificatePlan searchedResult
          (annotateSelectorInfo selected) bindings
          rawEncodingInfos rawPremiseEncodingInfos)
  let candidates ← boundedProjectionFunctionCandidates bridge.matched.expression
  for name in candidates do
    let zeta ← syntheticBridgeReductionEvent bridge.matched.expression {
      kind := .zeta
    }
    let projection ← syntheticBridgeReductionEvent bridge.matched.expression {
      kind := .projectionFunction name
    }
    -- The replay-specific projection operation can perform the beta-WHNF
    -- needed by `reduceProj?`; prefer the shortest validated bridge. Keep the
    -- older zeta/projection pair as a bounded compatibility candidate.
    for inserted in #[#[projection], #[zeta, projection]] do
      let mut augmented := rawWithNext.take bridge.firstUnconsumed
      augmented := augmented ++ inserted
      augmented := augmented ++ rawWithNext.drop bridge.firstUnconsumed
      let accepted ← try
        withoutModifyingState do
          let replayEvents := augmented.map (·.replay)
          let (replayedResult, replayState) ← runReplay target replayEvents
          unless replayState.next == replayEvents.size do
            return false
          unless ← replayResultWellFormed? replayedResult do
            return false
          reachesSearchedResult? searchedResult replayedResult
      catch _ =>
        pure false
      if accepted then
        return some (← makeCertificatePlan searchedResult augmented bindings
          rawEncodingInfos rawPremiseEncodingInfos)
  return none

private def buildCertificatePlan? (target : Expr) (recorded : Array RecordedEvent)
    (searchedResult : Simp.Result) (initialUsedNames : Array Name := #[]) :
    TacticM (Option CertificatePlan) := do
  let base? ← withoutModifyingState do
    buildEncodedEvents? recorded initialUsedNames
  let some (baseEncoded, bindings, _) := base?
    | return none
  let projection? ← withoutModifyingState do
    projectCertificateEvents? target searchedResult baseEncoded
  if let some projection := projection? then
    let encoded := projection.selected
    return some (← makeCertificatePlan searchedResult encoded bindings
      projection.rawEncodingInfos projection.rawPremiseEncodingInfos
      projection.nonmaterialInternalEvents)
  for mode in #[CertificateSelectorMode.discover, CertificateSelectorMode.next,
      CertificateSelectorMode.ticks] do
    let selected? ← withoutModifyingState do
      selectCertificateEvents? target searchedResult baseEncoded mode
    if let some selected := selected? then
      let encoded := annotateSelectorInfo selected
      return some (← makeCertificatePlan searchedResult encoded bindings)
  let bridge? ← try
    certificateBridgePrefix? target recorded
  catch _ =>
    pure none
  let some bridge := bridge?
    | return none
  bridgeCertificatePlan? target searchedResult baseEncoded bindings bridge

/-! Encode one semantic simp result using the same event fallback and closed
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

private def premiseTerminalReport : PremiseTerminal → MetaM PremiseTerminalReport
  | .isTrue _ => return { kind := "isTrue" }
  | .dischargeRfl _ => return { kind := "dischargeRfl" }
  | .localAssumption _ contextIndex name => return {
      kind := "localAssumption"
      localContextIndex := some contextIndex
      localName := some name.toString
    }
  | .equationHypothesis => return { kind := "equationHypothesis" }
  | .custom => return { kind := "custom" }

private partial def semanticEventReport (event : RecordedEvent)
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
    let encoding? := match premiseEncodings[index]? with
      | some encoding => some encoding
      | none => encoding?.bind (fun eventEncoding => eventEncoding.premises[index]?)
    let commandInfos := encoding?.map (·.commands) |>.getD #[]
    let commands ← premise.events.mapIdxM fun childIndex child => do
      let childEncoding? := commandInfos[childIndex]?
      let childPremises := childEncoding?.map (·.premises) |>.getD #[]
      semanticEventReport child childEncoding? childPremises
    let terminal ← premiseTerminalReport premise.terminal
    return {
      proposition := ← exprFingerprint premise.proposition
      origins := premiseOrigins
      commands
      terminal
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
  if plan.rawEncodingInfos.isEmpty then plan.events.map (·.info) else plan.rawEncodingInfos

private def planPremiseEncodingInfos (plan : CertificatePlan) :
    Array (Array PremiseEncodingInfo) :=
  if plan.rawPremiseEncodingInfos.isEmpty then
    plan.events.map (·.premiseEncodings)
  else
    plan.rawPremiseEncodingInfos

private structure ContextSubjectEncoding where
  eventText : String
  bindings : Array GeneratedBinding
  encodingInfos : Array EventEncodingInfo
  premiseEncodingInfos : Array (Array PremiseEncodingInfo)
  metrics : EncodingMetrics
  fallbackReason? : Option String
  positionsNeeded : Bool
  transitionContinuity? : Option TransitionContinuityReport

private def operationalUnavailableContextEncoding (target : Expr)
    (state : RecorderState) (result : Simp.Result) (usedNames : Array Name) :
    TacticM (ContextSubjectEncoding × Array Name) := do
  let (rawInfos, rawPremiseInfos) ← unencodedHierarchy state.events
  let hasPremises := state.events.any (·.premises.size > 0)
  let transitionContinuity? ← try
    buildTransitionContinuity? target state.events result.expr
  catch _ =>
    pure none
  pure ({
    eventText := ""
    bindings := #[]
    encodingInfos := rawInfos
    premiseEncodingInfos := rawPremiseInfos
    metrics := if hasPremises then
      { premiseProgramFailures := 1 }
    else
      { operationalProgramFailures := 1 }
    fallbackReason? := some (if hasPremises then
      "premise_program_unavailable" else "operational_program_unavailable")
    positionsNeeded := false
    transitionContinuity?
  }, usedNames)

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
  nonmaterialInternalEvents := lhs.nonmaterialInternalEvents + rhs.nonmaterialInternalEvents
  generatedProofEvents := lhs.generatedProofEvents + rhs.generatedProofEvents
  generatedSimprocEvents := lhs.generatedSimprocEvents + rhs.generatedSimprocEvents
  deferredSimprocEvents := lhs.deferredSimprocEvents + rhs.deferredSimprocEvents
  generatedSpecialEvents := lhs.generatedSpecialEvents + rhs.generatedSpecialEvents
  wholeResultProofCount := lhs.wholeResultProofCount + rhs.wholeResultProofCount
  generatedBindingCount := lhs.generatedBindingCount + rhs.generatedBindingCount
  generatedBindingBytes := lhs.generatedBindingBytes + rhs.generatedBindingBytes
  premiseBindingCount := lhs.premiseBindingCount + rhs.premiseBindingCount
  premiseBindingBytes := lhs.premiseBindingBytes + rhs.premiseBindingBytes
  nestedPremiseBindings := lhs.nestedPremiseBindings + rhs.nestedPremiseBindings
  termPremiseBindings := lhs.termPremiseBindings + rhs.termPremiseBindings
  premiseProgramFailures := lhs.premiseProgramFailures + rhs.premiseProgramFailures
  operationalProgramFailures := lhs.operationalProgramFailures + rhs.operationalProgramFailures
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

private def runFirstOwnerScope (ownerId : String) (body : Syntax) (reportStx : Syntax) :
    TacticM Unit := withMainContext do
  let frameId ← enterScopedFrame ownerId
  try
    -- A `first` owner is only a scope for its child occurrences.  Its
    -- enclosing proof is deliberately not inspected or exported.
    withOptions (·.set `explicitLean.simpExplicit.bodyScopeFrame frameId) do
      evalTactic body
    publishScopedFrame ownerId frameId reportStx
  catch ex =>
    leaveScopedFrame frameId
    throw ex

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
    let deferred? ← deferredSimprocEncoding state.events
    if let some (deferredInfos, deferredPremiseInfos, deferredCount) := deferred? then
      return some ({
        eventText := ""
        bindings := #[]
        encodingInfos := deferredInfos
        premiseEncodingInfos := deferredPremiseInfos
        metrics := { deferredSimprocEvents := deferredCount }
        fallbackReason? := some "deferred_simproc"
        positionsNeeded := false
        transitionContinuity? := none
      }, usedNames)
    -- Use the same anchored event projection as ordinary target encoding
    -- before considering the legacy flat context selector path.  This keeps
    -- raw context metadata aligned when internal theorem callbacks are
    -- omitted from the executable whole-subject certificate.
    if !state.events.any (·.premises.size > 0) then
      if let some plan ← buildCertificatePlan? target state.events result usedNames then
        let continuity? ← if plan.metrics.mode == "event" &&
            plan.metrics.generatedProofEvents == 0 && plan.metrics.termPremiseBindings == 0 then
            pure none
          else if plan.metrics.generatedSimprocEvents > 0 then
            pure none
          else
            buildTransitionContinuity? target state.events result.expr
        let eventText := certificatePlanEventListText plan.events
        let allUsedNames := usedNames ++ plan.bindings.map (·.name)
        return some ({
          eventText
          bindings := plan.bindings
          encodingInfos := planEncodingInfos plan
          premiseEncodingInfos := planPremiseEncodingInfos plan
          metrics := plan.metrics
          fallbackReason? := none
          positionsNeeded := plan.positions
          transitionContinuity? := continuity?
        }, allUsedNames)
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
    let mut plan? ← buildCertificatePlan? target state.events result usedNames
    if plan?.isNone && state.events.any (·.premises.size > 0) then
      return some (← operationalUnavailableContextEncoding target state result usedNames)
    let some plan := plan? |
      return some (← operationalUnavailableContextEncoding target state result usedNames)
    let continuity? ← if plan.metrics.mode == "event" &&
        plan.metrics.generatedProofEvents == 0 && plan.metrics.termPremiseBindings == 0 then
        pure none
      else if plan.metrics.generatedSimprocEvents > 0 then
        pure none
      else
        buildTransitionContinuity? target state.events result.expr
    let eventText := certificatePlanEventListText plan.events
    let allUsedNames := usedNames ++ plan.bindings.map (·.name)
    return some ({
      eventText
      bindings := plan.bindings
      encodingInfos := planEncodingInfos plan
      premiseEncodingInfos := planPremiseEncodingInfos plan
      metrics := plan.metrics
      fallbackReason? := none
      positionsNeeded := plan.positions
      transitionContinuity? := continuity?
    }, allUsedNames)
  catch _ =>
    try
      return some (← operationalUnavailableContextEncoding target state result usedNames)
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

private def instantiatePremiseTerminal : PremiseTerminal → MetaM PremiseTerminal
  | .isTrue result => return .isTrue (← instantiateMVars result)
  | .dischargeRfl result => return .dischargeRfl (← instantiateMVars result)
  | .localAssumption fvarId contextIndex name =>
      return .localAssumption fvarId contextIndex name
  | .equationHypothesis => return .equationHypothesis
  | .custom => return .custom

mutual
  private partial def instantiateRecordedPremise (premise : RecordedPremise) :
      MetaM RecordedPremise := do
    return {
      premise with
        proposition := ← instantiateMVars premise.proposition
        proof := ← instantiateMVars premise.proof
        events := ← premise.events.mapM instantiateRecordedEvent
        terminal := ← instantiatePremiseTerminal premise.terminal
    }

  private partial def instantiateRecordedEvent (event : RecordedEvent) : MetaM RecordedEvent := do
    return {
      event with
        input := ← instantiateMVars event.input
        step := ← instantiateRecordedStep event.step
        result := ← instantiateRecordedResult event.result
        premises := ← event.premises.mapM instantiateRecordedPremise
    }
end

private def instantiateRecordedState (state : RecorderState) : MetaM RecorderState := do
  return {
    state with
      events := ← state.events.mapM instantiateRecordedEvent
      premises := ← state.premises.mapM instantiateRecordedPremise
  }

private def operationalUnavailableAttempt (target : Expr) (state : RecorderState)
    (result : Simp.Result) : TacticM EncodingAttempt := do
  let (rawInfos, rawPremiseInfos) ← unencodedHierarchy state.events
  let hasPremises := state.events.any (·.premises.size > 0)
  let transitionContinuity? ← try
    buildTransitionContinuity? target state.events result.expr
  catch _ =>
    pure none
  pure {
    suggestion := ""
    encodingInfos := rawInfos
    premiseEncodingInfos := rawPremiseInfos
    encodingMetrics := if hasPremises then
      { premiseProgramFailures := 1 }
    else
      { operationalProgramFailures := 1 }
    encodingFallbackReason? := some (if hasPremises then
      "premise_program_unavailable" else "operational_program_unavailable")
    positionsNeeded := false
    transitionContinuity?
  }

private def encodeRecording? (target : Expr) (mvarId : MVarId)
    (state : RecorderState) (result : Simp.Result)
    (runAndRecord : Expr → TacticM (Simp.Result × RecorderState)) :
    TacticM (Option EncodingAttempt) := do
  try
    let deferred? ← deferredSimprocEncoding state.events
    if let some (deferredInfos, deferredPremiseInfos, deferredCount) := deferred? then
      -- Simproc callbacks are diagnostic-only.  In particular, do not let a
      -- source-identifiable single origin fall through to generated proof or
      -- whole-result encoding after this point.
      return some {
        suggestion := ""
        encodingInfos := deferredInfos
        premiseEncodingInfos := deferredPremiseInfos
        encodingMetrics := { deferredSimprocEvents := deferredCount }
        encodingFallbackReason? := some "deferred_simproc"
        positionsNeeded := false
        transitionContinuity? := none
      }
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
      -- Prefer the compact event program whenever it validates.  A failed
      -- operational plan is a coverage result; presentation and whole-result
      -- proof exporters are intentionally outside the materialization path.
      let mut plan? ← if needsPresentation then
        pure none
      else
        buildCertificatePlan? target state.events result
      let some plan := plan?
        | return some (← operationalUnavailableAttempt target state result)
      suggestion := plan.source
      encodingInfos := planEncodingInfos plan
      premiseEncodingInfos := planPremiseEncodingInfos plan
      encodingMetrics := plan.metrics
      positionsNeeded := plan.positions

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
    try
      return some (← operationalUnavailableAttempt target state result)
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
        if encoding?.isNone || encoding.metrics.operationalProgramFailures > 0 ||
            encoding.metrics.premiseProgramFailures > 0 then
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
        if encoding?.isNone || encoding.metrics.operationalProgramFailures > 0 ||
            encoding.metrics.premiseProgramFailures > 0 then
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
  let report : ContextReportBundle ← if aggregateMetrics.deferredSimprocEvents > 0 then
      -- A context subject with a nested simproc is deferred as a whole.  A
      -- speculative stable-name pass is still permitted for diagnostics: it
      -- only rebuilds the raw trace metadata through the deferred subject
      -- encoder, never a flat replay, presentation, generated proof, or
      -- whole-result source program.
      let renamed? ← if stableRenamePlan.isEmpty then pure none else
        reencodeContextTraces? traces stableRenamePlan
      match renamed? with
      | some renamed =>
          let renamePairs := contextReportRenamePairs traces resultingFVars stableRenamePlan
          let renamedFinalLctx := renamedLocalContextByFVars
            (renamedLocalContext finalLctx stableRenamePlan) renamePairs
          pure {
            initialLctx := renamedLocalContext initialLctx stableRenamePlan
            finalLctx := renamedFinalLctx
            traces := contextTransportTraces renamed.traces resultingFVars renamedFinalLctx
            bindings := #[]
            metrics := renamed.metrics
            fallbackReason? := some "deferred_simproc"
            positionsNeeded := false
            suggestion := ""
            localRenames := localRenameInfos stableRenamePlan
          }
      | none =>
          pure {
            initialLctx
            finalLctx
            traces := ordinaryTraces
            bindings := #[]
            metrics := aggregateMetrics
            fallbackReason? := some "deferred_simproc"
            positionsNeeded := false
            suggestion := ""
            localRenames := #[]
          }
    else if !ordinaryEncodingFailed && ordinaryValid &&
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
    else if (aggregateMetrics.operationalProgramFailures > 0 ||
        aggregateMetrics.premiseProgramFailures > 0) && stableRenamePlan.isEmpty then
      -- Keep the complete raw context trace, but never synthesize a context
      -- tactic containing empty subject programs or an enclosing proof.
      pure {
        initialLctx
        finalLctx
        traces := ordinaryTraces
        bindings := #[]
        metrics := aggregateMetrics
        fallbackReason?
        positionsNeeded := false
        suggestion := ""
        localRenames := #[]
      }
    else do
      -- Passive context recording is already enclosed by
      -- `withoutModifyingState`, so it can validate the same stable-renaming
      -- certificate as the interactive recorder without affecting the
      -- original simp execution that follows.
      let renamePlan := stableRenamePlan
      let fallbackMetrics := if aggregateMetrics.operationalProgramFailures == 0 &&
          aggregateMetrics.premiseProgramFailures == 0 then
          { aggregateMetrics with operationalProgramFailures := 1 }
        else
          aggregateMetrics
      let fallback : ContextReportBundle := {
        initialLctx
        finalLctx
        traces := ordinaryTraces
        bindings := #[]
        metrics := fallbackMetrics
        fallbackReason? := some "operational_program_unavailable"
        positionsNeeded := false
        suggestion := ""
        localRenames := #[]
      }
      if renamePlan.isEmpty then
        pure fallback
      else
        let encoded? ← reencodeContextTraces? traces renamePlan
        match encoded? with
        | none => pure fallback
        | some encoded =>
            let renamedInitialLctx := renamedLocalContext initialLctx renamePlan
            let renamePairs := contextReportRenamePairs traces resultingFVars renamePlan
            let renamedFinalLctx := renamedLocalContextByFVars
              (renamedLocalContext finalLctx renamePlan) renamePairs
            let renamedTraces := contextTransportTraces encoded.traces resultingFVars renamedFinalLctx
            if encoded.metrics.operationalProgramFailures > 0 ||
                encoded.metrics.premiseProgramFailures > 0 then
              pure {
                initialLctx := renamedInitialLctx
                finalLctx := renamedFinalLctx
                traces := renamedTraces
                bindings := #[]
                metrics := encoded.metrics
                fallbackReason? := encoded.fallbackReason?.or
                  (some "operational_program_unavailable")
                positionsNeeded := false
                suggestion := ""
                localRenames := localRenameInfos renamePlan
              }
            else
              let suggestion := localRenamePrefix renamePlan ++
                contextCertificateText encoded.traces encoded.bindings
              let valid ← validateContextCertificate suggestion initialTarget initialLctx
                initialLocalInstances closed renamedFinalLctx finalTarget
              if !valid then
                pure {
                  initialLctx := renamedInitialLctx
                  finalLctx := renamedFinalLctx
                  traces := renamedTraces
                  bindings := #[]
                  metrics := fallbackMetrics
                  fallbackReason? := some "operational_program_unavailable"
                  positionsNeeded := false
                  suggestion := ""
                  localRenames := localRenameInfos renamePlan
                }
              else
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
  let mut localRenames : Array LocalRenamePlan := #[]
  let mut reportLctx? : Option LocalContext := none
  let mut attempt? ← encodeRecording? target mvarId state result runAndRecord
  let shouldProbeRenamed := match attempt? with
    | none => true
    | some attempt =>
        attempt.encodingMetrics.deferredSimprocEvents > 0 ||
        attempt.encodingMetrics.operationalProgramFailures > 0 ||
        attempt.encodingMetrics.premiseProgramFailures > 0
  if shouldProbeRenamed then
    let renamePlan ← localRenamePlan (← mvarId.getDecl).lctx
    if !renamePlan.isEmpty then
      let mvarDecl ← mvarId.getDecl
      let renamedLctx := renamedLocalContext mvarDecl.lctx renamePlan
      let renamedAttempt? ← withLCtx' renamedLctx do
        encodeRecording? target mvarId state result runAndRecord
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
            encodeRecording? target speculativeMVarId speculativeState
              speculativeResult renamedRunAndRecord
        if let some speculativeAttempt := speculativeAttempt? then
          localRenames := renamePlan
          reportLctx? := some renamedLctx
          attempt? := some speculativeAttempt
  let attempt ← match attempt? with
    | some attempt => pure attempt
    | none => operationalUnavailableAttempt target state result
  let encodingInfos := attempt.encodingInfos
  let premiseEncodingInfos := attempt.premiseEncodingInfos
  let encodingMetrics := attempt.encodingMetrics
  let encodingFallbackReason? := attempt.encodingFallbackReason?
  let transitionContinuity? := attempt.transitionContinuity?
  let operationalFailure := encodingMetrics.operationalProgramFailures > 0 ||
    encodingMetrics.premiseProgramFailures > 0 ||
    encodingMetrics.termPremiseBindings > 0 ||
    encodingMetrics.generatedProofEvents > 0 ||
    encodingMetrics.generatedSpecialEvents > 0 ||
    encodingMetrics.wholeResultProofCount > 0 ||
    encodingMetrics.presentationChangeCount > 0
  let suggestion := if operationalFailure then
      ""
    else
      localRenamePrefix localRenames ++ attempt.suggestion
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

private def runBodyScope (scopeId : String) (body : Syntax) (reportStx : Syntax) :
    TacticM Unit := withMainContext do
  let frameId ← enterScopedFrame scopeId
  try
    withOptions (·.set `explicitLean.simpExplicit.bodyScopeFrame frameId) do
      evalTactic body
    publishScopedFrame scopeId frameId reportStx
  catch ex =>
    leaveScopedFrame frameId
    throw ex

end SimpExplicit

open SimpExplicit

elab_rules : tactic
  | `(tactic| simp_explicit_premise $kind:ident) => withMainContext do
      let mvarId ← getMainGoal
      let target ← instantiateMVars (← mvarId.getType)
      let proof? ← match kind.getId with
        | `dischargeRfl => rebuildRecordedDischargeRfl? target
        | `equationHypothesis => rebuildEquationHypothesis? target
        | _ => throwErrorAt kind "unknown simp_explicit premise terminal"
      let some proof := proof?
        | throwErrorAt kind "recorded simp_explicit premise terminal did not apply"
      mvarId.assign proof
      replaceMainGoal []
  | `(tactic| simp_explicit_body_scope $scope:str in $body:tacticSeq) => do
      let some scopeId := scope.raw.isStrLit?
        | throwErrorAt scope "body scope id must be a string literal"
      runBodyScope scopeId body.raw (← getRef)
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
