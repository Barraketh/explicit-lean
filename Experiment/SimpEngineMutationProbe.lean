import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

opaque replayPairAdd : Nat → Nat → Nat
axiom replayTwoPremises {a b : Nat} (ha : a = 0) (hb : b = 0) :
  replayPairAdd a b = 0

private def expectReplayReject (label : String)
    (recording : ExplicitLean.SimpEngine.Recording.TacticRecording) : TacticM Unit := do
  let saved ← Meta.saveState
  let goals ← getGoals
  let succeeded ← try
    ExplicitLean.SimpEngine.Replay.replayCertificate recording
    pure true
  catch _ => pure false
  saved.restore
  setGoals goals
  if succeeded then
    throwError "replay mutation was accepted: {label}"

private def replaceFirstSubject
    (recording : ExplicitLean.SimpEngine.Recording.TacticRecording)
    (subject : Simp.Engine.SubjectProgram) :
    ExplicitLean.SimpEngine.Recording.TacticRecording :=
  { recording with certificate.subjects := recording.certificate.subjects.set! 0 subject }

private def replaceEvent
    (recording : ExplicitLean.SimpEngine.Recording.TacticRecording)
    (index : Nat)
    (event : Simp.Engine.Event) :
    ExplicitLean.SimpEngine.Recording.TacticRecording :=
  let subject := recording.certificate.subjects[0]!
  let subject := { subject with program.events := subject.program.events.set! index event }
  replaceFirstSubject recording subject

private def replaceFirstEvent
    (recording : ExplicitLean.SimpEngine.Recording.TacticRecording)
    (event : Simp.Engine.Event) :
    ExplicitLean.SimpEngine.Recording.TacticRecording :=
  replaceEvent recording 0 event

private def replaceStructural
    (recording : ExplicitLean.SimpEngine.Recording.TacticRecording)
    (index : Nat)
    (structural : Simp.Engine.StructuralWitness) :
    ExplicitLean.SimpEngine.Recording.TacticRecording :=
  let subject := recording.certificate.subjects[0]!
  let subject := {
    subject with program.structural := subject.program.structural.set! index structural }
  replaceFirstSubject recording subject

elab "check_replay_mutations" ha:ident hb:ident : tactic => withMainContext do
  let haLemma ← `(Parser.Tactic.simpLemma| $ha:ident)
  let hbLemma ← `(Parser.Tactic.simpLemma| $hb:ident)
  let simpStx ← `(tactic| simp only [replayTwoPremises, $haLemma, $hbLemma])
  let recording ← ExplicitLean.SimpEngine.Recording.recordCertificate simpStx.raw
  let some subject := recording.certificate.subjects[0]?
    | throwError "mutation fixture has no subject"
  let mut selected? : Option (Nat × Simp.Engine.Event × Simp.Engine.RuleRef ×
      Simp.Engine.MatchEnvelope × Array Simp.Engine.PremiseProgram) := none
  for h : index in *...subject.program.events.size do
    let event := subject.program.events[index]
    if let .rewrite rule envelope premises := event.operation then
      if premises.size == 2 then
        selected? := some (index, event, rule, envelope, premises)
  let some (eventIndex, event, rule, envelope, premises) := selected?
    | throwError "mutation fixture has no two-premise rewrite"

  expectReplayReject "configuration" {
    recording with certificate.config.memoize := !recording.certificate.config.memoize }
  expectReplayReject "event path" <| replaceEvent recording eventIndex {
    event with path.steps := event.path.steps.push .ground }
  expectReplayReject "event phase" <| replaceEvent recording eventIndex {
    event with phase := .dpost }
  expectReplayReject "rule variant" <| replaceEvent recording eventIndex {
    event with operation := .rewrite { rule with variant := rule.variant + 1 } envelope premises }
  expectReplayReject "operation" <| replaceEvent recording eventIndex {
    event with operation := .reduce .beta }
  expectReplayReject "match envelope" <| replaceEvent recording eventIndex {
    event with operation := .rewrite rule {
      envelope with proofPresent := !envelope.proofPresent } premises }
  let some firstPremise := premises[0]?
    | throwError "mutation fixture has no first premise"
  let some secondPremise := premises[1]?
    | throwError "mutation fixture has no second premise"
  expectReplayReject "premise order" <| replaceEvent recording eventIndex {
    event with operation := .rewrite rule envelope #[secondPremise, firstPremise] }
  expectReplayReject "terminal" <| replaceFirstSubject recording {
    subject with terminal := .targetTransport .explicit }
  expectReplayReject "final fingerprint" <| replaceFirstSubject recording {
    subject with program.finalFingerprint := "mutated" }

  logInfo "SIMP_ENGINE_MUTATIONS core=9"

elab "check_replay_structural_mutations" : tactic => withMainContext do
  let simpStx ← `(tactic| simp only [Nat.add_zero])
  let recording ← ExplicitLean.SimpEngine.Recording.recordCertificate simpStx.raw
  let some subject := recording.certificate.subjects[0]?
    | throwError "structural fixture has no subject"
  let mut phase? : Option (Nat × Simp.Engine.StructuralWitness) := none
  let mut congruence? : Option (Nat × Simp.Engine.StructuralWitness × Nat) := none
  let mut cache? : Option (Nat × Simp.Engine.StructuralWitness) := none
  for h : index in *...subject.program.structural.size do
    let structural := subject.program.structural[index]
    match structural.witness with
    | .phaseOutcome .. => if phase?.isNone then phase? := some (index, structural)
    | .congruence ordinal _ =>
        if congruence?.isNone then congruence? := some (index, structural, ordinal)
    | .cacheHit _ => if cache?.isNone then cache? := some (index, structural)
    | _ => pure ()
  let some (phaseIndex, phase) := phase?
    | throwError "structural fixture has no phase outcome"
  let some (congruenceIndex, congruence, ordinal) := congruence?
    | throwError "structural fixture has no congruence choice"
  let some (cacheIndex, cache) := cache?
    | throwError "structural fixture has no cache hit"
  expectReplayReject "structural path" <| replaceStructural recording phaseIndex {
    phase with path.steps := phase.path.steps.push .ground }
  let .phaseOutcome phaseName phaseOrdinal disposition output proof := phase.witness
    | throwError "unreachable phase witness"
  let mutatedDisposition := match disposition with
    | .done => Simp.Engine.StepDisposition.visit
    | _ => .done
  expectReplayReject "phase disposition" <| replaceStructural recording phaseIndex {
    phase with witness := .phaseOutcome phaseName phaseOrdinal mutatedDisposition output proof }
  expectReplayReject "congruence choice" <| replaceStructural recording congruenceIndex {
    congruence with witness := .congruence ordinal .generatedAttemptFailed }
  expectReplayReject "cache source" <| replaceStructural recording cacheIndex {
    cache with witness := .cacheHit { steps := #[.ground] } }
  let some event := subject.program.events[0]?
    | throwError "structural fixture has no event"
  expectReplayReject "event output" <| replaceFirstEvent recording {
    event with outputFingerprint := "mutated" }
  logInfo "SIMP_ENGINE_MUTATIONS structural=5"

elab "check_replay_arithmetic_mutation" : tactic => withMainContext do
  let simpStx ← `(tactic| simp (config := { arith := true }))
  let recording ← ExplicitLean.SimpEngine.Recording.recordCertificate simpStx.raw
  let some subject := recording.certificate.subjects[0]?
    | throwError "arithmetic fixture has no subject"
  let mut selected? : Option (Nat × Simp.Engine.Event × Simp.Engine.ArithHandler) := none
  for h : index in *...subject.program.events.size do
    let event := subject.program.events[index]
    if let .builtin (.arith handler) := event.operation then
      selected? := some (index, event, handler)
  let some (eventIndex, event, handler) := selected?
    | throwError "arithmetic fixture has no arithmetic event"
  let mutatedHandler := match handler with
    | .intEquality => Simp.Engine.ArithHandler.intRelation
    | _ => .intEquality
  expectReplayReject "arithmetic handler" <| replaceEvent recording eventIndex {
    event with operation := .builtin (.arith mutatedHandler) }
  logInfo "SIMP_ENGINE_MUTATIONS arithmetic=1"

example (a b : Nat) (ha : a = 0) (hb : b = 0) : replayPairAdd a b = 0 := by
  check_replay_mutations ha hb
  exact replayTwoPremises ha hb

example (x : Nat) : (x + 0, x + 0) = (x, x) := by
  check_replay_structural_mutations
  exact congrArg (fun y => (y, y)) (Nat.add_zero x)

example (x : Int) : x + x + 0 = 2 * x := by
  check_replay_arithmetic_mutation
  simp_engine_replay +arith
