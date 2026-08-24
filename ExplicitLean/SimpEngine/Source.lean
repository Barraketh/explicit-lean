module

public meta import ExplicitLean.SimpEngine.Replay
public meta import Lean.Data.Json.Parser
public meta import Lean.Data.Json.Printer

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

syntax (name := simpEngineSourceRecording)
  "simp_engine_source_recording" str str simpEngineReplayArgs : tactic

syntax (name := simpEngineApply)
  "simp_engine_apply" str group("(" &"certificates" " := " term ")")
    simpEngineReplayArgs : tactic

end Lean.Parser.Tactic

namespace ExplicitLean.SimpEngine.Source

/-- Schema 19's stable source payload. The engine identifier inside the
    certificate is part of the serialized data and is validated before replay. -/
def certificateSource (certificate : Simp.Engine.Certificate) : String :=
  (toJson certificate).compress

def parseCertificateSource (source : String) : Except String Simp.Engine.Certificate :=
  Json.parse source >>= fromJson?

private def certificateFileName (occurrenceId source : String) : String :=
  s!"{occurrenceId}-{hash source}.json"

private def deferredSubjectCount (certificate : Simp.Engine.Certificate) : Nat :=
  certificate.subjects.foldl (init := 0) fun count subject =>
    if subject.deferred.isSome then count + 1 else count

private def writeCertificate (directory occurrenceId : String)
    (certificate : Simp.Engine.Certificate) : TacticM System.FilePath := do
  let source := certificateSource certificate
  match parseCertificateSource source with
  | .ok decoded =>
      unless decoded == certificate do
        throwError "source_certificate_roundtrip_mismatch"
  | .error message => throwError "source_certificate_roundtrip_failure: {message}"
  let directory : System.FilePath := directory
  liftM <| IO.FS.createDirAll directory
  let path := directory / certificateFileName occurrenceId source
  liftM <| IO.FS.writeFile path source
  return path

private def recordSource (occurrenceId directory : String)
    (simpStx : Syntax) : TacticM Unit := do
  let referenceFailed ← IO.mkRef false
  let recording : Recording.TacticRecording ← try
    Recording.recordCertificate simpStx (commitReference := true) (onReferenceFailure := do
      referenceFailed.set true
      IO.println s!"SIMP_ENGINE_SOURCE_UNSUCCESSFUL occurrence={occurrenceId}")
  catch error =>
    let failed ← referenceFailed.get
    unless failed do
      IO.println s!"SIMP_ENGINE_SOURCE_RECORDER_FAILURE occurrence={occurrenceId}"
    throw error
  let path ← writeCertificate directory occurrenceId recording.certificate
  logInfo m!"SIMP_ENGINE_SOURCE_RECORD occurrence={occurrenceId} certificate={path} deferredSubjects={deferredSubjectCount recording.certificate} subjects={recording.certificate.subjects.size}"

private def certificateSourceArrayType : Expr :=
  mkApp (mkConst ``Array [Level.zero]) (mkConst ``String)

private unsafe def elaborateCertificates
    (source : Syntax) : TacticM (Array Simp.Engine.Certificate) := do
  -- Certificate source is closed data. Elaborating it must not solve
  -- postponed metavariables belonging to the declaration around this tactic.
  -- In particular, the global synthesis checkpoint below is required to
  -- evaluate the array but is not part of `simp`'s observable execution.
  let saved ← Tactic.saveState
  try
    let expression ← Term.elabTermEnsuringType source certificateSourceArrayType
    Term.synthesizeSyntheticMVarsNoPostponing
    let sources ← Meta.evalExpr (Array String) certificateSourceArrayType expression
    sources.mapM fun encoded =>
      match parseCertificateSource encoded with
      | .ok certificate => return certificate
      | .error message => throwError "source_certificate_parse_failure: {message}"
  finally
    saved.restore

private def selectCertificate (certificates : Array Simp.Engine.Certificate) : TacticM
    Simp.Engine.Certificate := do
  let initialState ← Simp.Engine.proofStateFingerprint (← getGoals)
  let candidates := certificates.filter (·.initialState == initialState)
  let some selected := candidates[0]?
    | throwError "source_certificate_missing_for_initial_state: actual={repr initialState}; available={repr (certificates.map (·.initialState))}"
  unless candidates.all (· == selected) do
    throwError "source_certificate_ambiguous_for_initial_state"
  unless selected.engine == Simp.Engine.engineId do
    throwError "source_certificate_engine_mismatch: expected {repr Simp.Engine.engineId}, got {repr selected.engine}"
  return selected

private def replaySource (occurrenceId : String) (certificatesSource : Syntax)
    (simpStx : Syntax) : TacticM Unit := do
  let certificates ← unsafe elaborateCertificates certificatesSource
  let certificate ← selectCertificate certificates
  let { ctx, .. } ← mkSimpContext simpStx (eraseLocal := false)
  let (fvarIds, simplifyTarget) ←
    Recording.locationSubjects (expandOptLocation simpStx[5])
  let recording : Recording.TacticRecording := {
    ctx
    certificate
    branches := #[]
    fvarIds
    simplifyTarget
  }
  Replay.replayCertificate recording
  logInfo m!"SIMP_ENGINE_SOURCE_REPLAY occurrence={occurrenceId}"

elab_rules : tactic
  | `(tactic| simp_engine_source_recording $occurrenceId:str $directory:str
      $args:simpEngineReplayArgs) => withMainContext do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      recordSource occurrenceId.getString directory.getString inner
  | `(tactic| simp_engine_apply $occurrenceId:str
      (certificates := $certificates:term) $args:simpEngineReplayArgs) => withMainContext do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      replaySource occurrenceId.getString certificates inner

end ExplicitLean.SimpEngine.Source
