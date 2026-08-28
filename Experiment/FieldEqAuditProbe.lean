import Mathlib
import ExplicitLean.SimpEngine.Replay
import ExplicitLeanMathlibAudit.FieldEq

open Lean Meta Elab Tactic

namespace FieldEqAuditProbe

open Lean.Meta.Simp.Engine

def fieldEqSets : MetaM Simp.SimprocsArray := do
  let set ← ({} : Simp.Simprocs).add `fieldEq true
  pure #[set]

def fieldEqMethods : MetaM (Simp.Context × Simp.Engine.Methods) := do
  let sets ← fieldEqSets
  let base := { Simp.mkDefaultMethodsCore #[] with
    pre := Simp.userPostSimprocs sets
    post := fun e => pure (.done { expr := e })
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }
  let methods := { Simp.Engine.mkDefaultMethodsCore #[] with
    pre := Simp.Engine.userPostSimprocsRecorded sets
    post := fun e => pure (.done { expr := e })
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue
    base }
  pure (← Simp.mkContext (simpTheorems := {}) (congrTheorems := {}),
    FieldEqAudit.withFieldEqAudit methods)

structure CaseArtifacts where
  target : Expr
  context : Simp.Context
  config : Simp.Engine.ReplayConfig
  reference : Simp.Result
  recording : Simp.Engine.Recording

def jsonRoundtrip {α : Type} [BEq α] [ToJson α] [FromJson α]
    (label : String) (value : α) : MetaM Unit := do
  let decoded ← match Lean.fromJson? (Lean.toJson value) with
    | .ok decoded => pure decoded
    | .error message => throwError "{label}: JSON decode failed: {message}"
  unless decoded == value do
    throwError "{label}: JSON roundtrip changed payload"

def expectFailure (label : String) (action : MetaM Unit) : MetaM Unit := do
  let saved ← Meta.saveState
  let succeeded ← try
    action
    pure true
  catch _ =>
    pure false
  saved.restore
  unless !succeeded do
    throwError "{label}: expected rejection"

def nonempty (value : String) : Bool := !value.isEmpty

def checkProcedureParity (label : String) (audit : FieldEqAudit) : MetaM Unit := do
  unless audit.initialMetaEffectFingerprint.startsWith "fieldEq-meta-v1:" &&
      audit.authoritativeFinalMetaEffectFingerprint.startsWith "fieldEq-meta-v1:" &&
      audit.shadowFinalMetaEffectFingerprint.startsWith "fieldEq-meta-v1:" do
    throwError "{label}: missing audit Meta evidence"
  unless audit.authoritativeFinalMetaEffectFingerprint ==
      audit.shadowFinalMetaEffectFingerprint do
    throwError "{label}: authoritative/shadow final Meta evidence differs"
  unless audit.shadow.exact && audit.shadow.diagnostic.isNone do
    throwError "{label}: authoritative/shadow audit is not exact: {repr audit.shadow}"
  let authoritative := audit.shadow.authoritative
  let shadow := audit.shadow.shadow
  unless authoritative.disposition == shadow.disposition &&
      authoritative.outputFingerprint == shadow.outputFingerprint &&
      authoritative.proofFingerprint == shadow.proofFingerprint &&
      authoritative.cache == shadow.cache &&
      authoritative.simpState == shadow.simpState &&
      authoritative.metaEffectFingerprint == shadow.metaEffectFingerprint do
    throwError "{label}: procedure evidence mismatch: {repr audit.shadow}"
  unless authoritative.outputFingerprint.startsWith "fieldEq-state-expr-v1:" &&
      authoritative.proofFingerprint.all
        (·.startsWith "fieldEq-state-expr-v1:") &&
      authoritative.metaEffectFingerprint.startsWith "fieldEq-meta-v1:" do
    throwError "{label}: incomplete procedure evidence: {repr authoritative}"

def checkAttempt (label : String) (index : Nat) (attempt : FieldEqAttempt) : MetaM Unit := do
  let expected : Array FieldEqStrategy :=
    #[.assumption, .normNum, .positivity, .recursiveSimp]
  unless index < expected.size && attempt.strategy == expected[index]! do
    throwError "{label}: strategy order mismatch at {index}: {repr attempt}"
  unless attempt.beforeMetaEffectFingerprint.startsWith "fieldEq-meta-v1:" &&
      attempt.afterMetaEffectFingerprint.startsWith "fieldEq-meta-v1:" do
    throwError "{label}: missing attempt Meta evidence at {index}"
  match attempt.outcome with
  | .success =>
      unless match attempt.proofFingerprint with
        | some fingerprint => fingerprint.startsWith "fieldEq-state-expr-v1:"
        | none => false do
        throwError "{label}: successful attempt lacks proof fingerprint at {index}"
  | _ =>
      unless attempt.proofFingerprint.isNone do
        throwError "{label}: failed attempt has proof fingerprint at {index}"
  match attempt.strategy with
  | .recursiveSimp =>
      unless attempt.beforeSimpState.isSome && attempt.afterSimpState.isSome do
        throwError "{label}: recursive attempt lacks complete state summaries"
      let before := attempt.beforeSimpState.get!
      let after := attempt.afterSimpState.get!
      unless before.cache.startsWith "stage1=" && after.cache.startsWith "stage1=" &&
          before.numSteps ≤ after.numSteps do
        throwError "{label}: malformed recursive state summaries"
      match attempt.outcome with
      | .terminalNotTrue =>
          unless (match attempt.terminalExpressionFingerprint with
            | some fingerprint => fingerprint.startsWith "fieldEq-state-expr-v1:"
            | none => false) && attempt.terminalProofFingerprint.isNone &&
              attempt.terminalCache.isSome do
            throwError "{label}: terminal recursive evidence incomplete"
      | _ => pure ()
  | _ =>
      unless attempt.beforeSimpState.isNone && attempt.afterSimpState.isNone &&
          attempt.terminalExpressionFingerprint.isNone &&
          attempt.terminalProofFingerprint.isNone && attempt.terminalCache.isNone do
        throwError "{label}: nonrecursive attempt has terminal/state evidence"

def checkCall (label : String) (index : Nat) (call : FieldEqDischargeCall) : MetaM Unit := do
  unless call.ordinal == index && call.parentOrdinal.isNone && call.recursionDepth == 0 do
    throwError "{label}: unexpected call tree/ordinal: {repr call}"
  unless !call.proposition.printable.isEmpty &&
      call.proposition.fingerprint.startsWith "expr-v2:" &&
      call.size.treeNodes ≥ call.size.dagNodes && call.size.dagNodes > 0 do
    throwError "{label}: incomplete proposition/size evidence: {repr call}"
  unless !call.attempts.isEmpty && call.attempts.size ≤ 4 do
    throwError "{label}: invalid attempt count: {repr call}"
  for h : attemptIndex in [:call.attempts.size] do
    checkAttempt label attemptIndex call.attempts[attemptIndex]
  let finalAttempt := call.attempts[call.attempts.size - 1]!
  unless call.outcome == finalAttempt.outcome do
    throwError "{label}: call outcome is not the final attempt outcome"
  match call.outcome with
  | .success =>
      unless (match call.proofFingerprint with
          | some fingerprint => fingerprint.startsWith "fieldEq-state-expr-v1:"
          | none => false) && call.terminalExpressionFingerprint.isNone &&
          call.terminalProofFingerprint.isNone && call.terminalCache.isNone do
        throwError "{label}: successful call evidence incomplete: {repr call}"
  | .terminalNotTrue =>
      unless call.proofFingerprint.isNone &&
          (match call.terminalExpressionFingerprint with
            | some fingerprint => fingerprint.startsWith "fieldEq-state-expr-v1:"
            | none => false) &&
          call.terminalExpressionFingerprint == finalAttempt.terminalExpressionFingerprint &&
          call.terminalProofFingerprint == finalAttempt.terminalProofFingerprint &&
          call.terminalCache == finalAttempt.terminalCache do
        throwError "{label}: terminal call evidence incomplete: {repr call}"
  | _ => pure ()

def attemptSequenceMatches (call : FieldEqDischargeCall)
    (expected : Array (FieldEqStrategy × FieldEqOutcome)) : Bool :=
  if call.attempts.size != expected.size then
    false
  else
    (Array.range expected.size).all fun index =>
      let attempt := call.attempts[index]!
      let expectedAttempt := expected[index]!
      attempt.strategy == expectedAttempt.1 && attempt.outcome == expectedAttempt.2

def checkCallSequence (label : String) (audit : FieldEqAudit)
    (expected : Array (String × Array (FieldEqStrategy × FieldEqOutcome))) : MetaM Unit := do
  unless audit.dischargeCalls.size == expected.size do
    throwError "{label}: unexpected discharge-call count: {audit.dischargeCalls.size}"
  for h : index in [:expected.size] do
    let call := audit.dischargeCalls[index]!
    let (proposition, attempts) := expected[index]
    unless call.proposition.printable == proposition &&
        attemptSequenceMatches call attempts do
      throwError "{label}: unexpected strategy sequence at call {index}: {repr call}"

def checkFixtureStrategy (label : String) (audit : FieldEqAudit) : MetaM Unit := do
  match label with
  | "assumption" =>
      checkCallSequence label audit
        #[("x ≠ 0", #[(.assumption, .success)]),
          ("x ≠ 0", #[(.assumption, .success)]),
          ("1 + x ≠ 0", #[(.assumption, .notApplicable), (.normNum, .threw),
            (.positivity, .threw), (.recursiveSimp, .terminalNotTrue)]),
          ("x ≠ 0", #[(.assumption, .success)])]
  | "normNum" =>
      checkCallSequence label audit
        #[("3 ≠ 0", #[(.assumption, .notApplicable), (.normNum, .success)]),
          ("3 ≠ 0", #[(.assumption, .notApplicable), (.normNum, .success)]),
          ("1 + 3 ≠ 0", #[(.assumption, .notApplicable), (.normNum, .success)])]
  | "positivity" =>
      checkCallSequence label audit
        #[("x ≠ 0", #[(.assumption, .notApplicable), (.normNum, .threw),
            (.positivity, .success)]),
          ("x ≠ 0", #[(.assumption, .notApplicable), (.normNum, .threw),
            (.positivity, .success)]),
          ("1 + x ≠ 0", #[(.assumption, .notApplicable), (.normNum, .threw),
            (.positivity, .success)])]
  | "kept-denominator" =>
      checkCallSequence label audit
        #[("x ≠ 0", #[(.assumption, .success)]),
          ("x ≠ 0", #[(.assumption, .success)]),
          ("1 + x ^ 2 ≠ 0", #[(.assumption, .notApplicable), (.normNum, .threw),
            (.positivity, .threw), (.recursiveSimp, .terminalNotTrue)]),
          ("x ≠ 0", #[(.assumption, .success)])]
  | _ => throwError "unknown fieldEq audit fixture {label}"

def makeCertificate (artifacts : CaseArtifacts) (initial final : StateFingerprint) :
    Simp.Engine.Certificate := {
  config := artifacts.config
  subjects := #[{
    subject := .target
    initialFingerprint := artifacts.recording.program.initialFingerprint
    program := artifacts.recording.program
    terminal := .targetTransport (if artifacts.reference.proof?.isSome then
      .explicit else .definitional)
    deferred := artifacts.recording.deferred
    simprocs := artifacts.recording.simprocs
  }]
  initialState := initial
  finalState := final
}

def checkNoFieldEqCandidate (label : String) (program : Simp.Engine.Program) : MetaM Unit := do
  for event in program.events do
    match event.operation with
    | .semanticSimproc fold =>
        unless !fold.candidates.any fun candidate => candidate.declaration == `fieldEq do
          throwError "{label}: fieldEq was emitted as a semantic candidate"
    | _ => pure ()

def checkAuditObservation (label : String) (artifacts : CaseArtifacts)
    (initial : StateFingerprint)
    (terminalPrintable? : Option String := none) : MetaM Unit := do
  let observations := artifacts.recording.simprocs.observations
  unless observations.size == 1 do
    throwError "{label}: expected one fieldEq observation, got {observations.size}"
  let observation := observations[0]!
  unless observation.name == `fieldEq && observation.phase == .pre &&
      observation.phaseInvocationOrdinal == 0 && observation.setIndex == 0 &&
      observation.procedureKind == .simp && observation.numExtraArgs == 0 &&
      observation.inputFingerprint.startsWith "expr-v2:" &&
      observation.outputFingerprint.startsWith "expr-v2:" &&
      observation.executed && observation.outputChanged &&
      observation.stepDisposition == .visit && observation.proofPresent &&
      observation.cache == some true && observation.outputSize.isSome do
    throwError "{label}: invalid fieldEq observation: {repr observation}"
  let outputSize := observation.outputSize.get!
  unless outputSize.treeNodes ≥ outputSize.dagNodes && outputSize.dagNodes > 0 do
    throwError "{label}: invalid fieldEq output size: {repr outputSize}"
  let some audit := observation.fieldEqAudit
    | throwError "{label}: fieldEq observation lacks audit"
  checkProcedureParity label audit
  unless !audit.dischargeCalls.isEmpty do
    throwError "{label}: audit recorded no discharge calls"
  for h : index in [:audit.dischargeCalls.size] do
    checkCall label index audit.dischargeCalls[index]
  unless audit.dischargeCalls.map (·.ordinal) ==
      (List.range audit.dischargeCalls.size).toArray do
    throwError "{label}: discharge ordinals are not flat and ordered"
  checkFixtureStrategy label audit
  if let some expected := terminalPrintable? then
    unless audit.dischargeCalls.any fun call => call.proposition.printable == expected &&
        call.outcome == .terminalNotTrue do
      throwError "{label}: expected terminal proposition {expected} not observed"
  jsonRoundtrip (label ++ ":observation-json") observation
  jsonRoundtrip (label ++ ":audit-json") audit
  jsonRoundtrip (label ++ ":trace-json") artifacts.recording.simprocs
  jsonRoundtrip (label ++ ":program-json") artifacts.recording.program
  let certificate := makeCertificate artifacts initial initial
  jsonRoundtrip (label ++ ":certificate-json") certificate
  unless artifacts.recording.deferred == some (.simproc `fieldEq .pre) do
    throwError "{label}: recording was not deferred specifically by fieldEq: {repr artifacts.recording.deferred}"
  checkNoFieldEqCandidate label artifacts.recording.program
  expectFailure (label ++ ":validation-authority") <|
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations
      artifacts.recording.program artifacts.recording.simprocs
  let noAuditTrace : Simp.Engine.SimprocTrace := {
    observations := observations.map fun value => { value with fieldEqAudit := none } }
  expectFailure (label ++ ":audit-not-replay-authority") <|
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations
      artifacts.recording.program noAuditTrace
  expectFailure (label ++ ":replay-without-fieldEq-authority") do
    let _ ← Simp.Engine.mainCoreReplay artifacts.target artifacts.context artifacts.config
      artifacts.recording.program

def recordCase (target : Expr) : TacticM CaseArtifacts := do
  let (context, methods) ← fieldEqMethods
  let (reference, _, recording) ←
    ExplicitLean.SimpEngine.Recording.recordExpression target context methods {}
  let config ← Simp.Engine.replayConfigOfContext context
  pure { target, context, config, reference, recording }

def checkCase (label : String) (target : Expr)
    (terminalPrintable? : Option String := none) : TacticM Unit := do
  let goals ← getGoals
  let initial ← Simp.Engine.proofStateFingerprint goals
  let artifacts ← recordCase target
  checkAuditObservation label artifacts initial terminalPrintable?

syntax (name := checkFieldEqAudit) "check_field_eq_audit" str : tactic

elab_rules : tactic
  | `(tactic| check_field_eq_audit $label:str) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let label := label.raw.isStrLit?.get!
      let terminalPrintable? :=
        if label == "kept-denominator" then some "1 + x ^ 2 ≠ 0" else none
      checkCase label target terminalPrintable?

elab "check_field_eq_audit_done" : tactic => do
  logInfo "FIELD_EQ_AUDIT assumption,normNum,positivity,kept-denominator: ok"

section

set_option maxHeartbeats 3000000 in
example (x : ℚ) (hx : x ≠ 0) : 1 / x + 1 = (1 + x) / x := by
  check_field_eq_audit "assumption"
  field_simp [hx]

example : (1 : ℚ) / 3 + 1 = (1 + 3) / 3 := by
  check_field_eq_audit "normNum"
  norm_num

example (x : ℝ) (hx : 0 < x) : 1 / x + 1 = (1 + x) / x := by
  check_field_eq_audit "positivity"
  field_simp [ne_of_gt hx]

set_option maxHeartbeats 3000000 in
example {K : Type*} [Field K] (x : K) (hx : x ≠ 0) :
    1 / x ^ 2 + 1 = (1 + x ^ 2) / x ^ 2 := by
  check_field_eq_audit "kept-denominator"
  check_field_eq_audit_done
  field_simp [hx]

end

end FieldEqAuditProbe
