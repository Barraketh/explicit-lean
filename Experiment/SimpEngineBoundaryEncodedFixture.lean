import ExplicitLean.SimpEngine.Boundary.Tactic

open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

private def quoted (value : String) : String := (Json.str value).compress

private def runEncodedOutcome (references : Array LMVarId) (outcome : String) : TacticM Unit := do
  let state ← boundaryProofStateFingerprintWithTerm (← getGoals) (← getThe Term.State)
  let options := boundaryOptionsFingerprint (← getOptions)
  let caller := boundaryCallerIdentity? (← Term.getDeclName?)
  let moduleName := (← getEnv).mainModule.toString
  let source := s!"simp_engine_boundary_select (artifact_kind := {quoted boundaryArtifactKind} " ++
    s!"artifact_schema := {boundaryArtifactSchema} selector_schema := {boundarySelectorSchema} " ++
    s!"semantic_contract := {quoted boundarySemanticContract} occurrence_id := \"fixture\" " ++
    s!"recorded_module := {quoted moduleName})\n" ++
    s!"  | \"fixture\" {quoted state.targetFingerprint} {quoted state.localContextFingerprint} " ++
    s!"{quoted state.metavariableContextFingerprint} {state.goalCount} " ++
    s!"{quoted options} {quoted caller} => {outcome}"
  let stx ← match Parser.runParserCategory (← getEnv) `tactic source with
    | .ok stx => pure stx
    | .error error => throwError "fixture syntax failed: {error}"
  evalTactic stx

private def rejects (references : Array LMVarId) (outcome expected : String) : TacticM Unit := do
  let saved ← Tactic.saveState
  let error? ← try
    runEncodedOutcome references outcome
    pure none
  catch error =>
    pure (some (← error.toMessageData.toString))
  saved.restore
  let some error := error? | throwError "encoded artifact unexpectedly accepted: {expected}"
  unless (error.splitOn expected).length > 1 do
    throwError "expected rejection {expected}, got {error}"

elab "test_encoded_boundary" : tactic => withMainContext do
  let references ← boundaryUniverseReferences (← getGoals) (← getThe Term.State)
  let trueType ← encodeBoundaryExprWithUniverses (mkConst ``True) references
  let wrongProof ← encodeBoundaryExprWithUniverses (mkConst ``True.intro) references
  rejects references s!"apply_encoded ({quoted trueType} ==> {quoted trueType} using {quoted wrongProof})"
    "boundary_expr_proof_type_mismatch"
  let malformed := "[\"expr_dag_v2\",0,[[\"a\",0,0]],0]"
  rejects references s!"apply_encoded ({quoted malformed} ==> {quoted trueType})"
    "boundary_expr_decode_error"
  rejects references s!"apply_encoded ({quoted "by simp"} ==> {quoted trueType})"
    "boundary_expr_decode_error"
  let badType ← encodeBoundaryExprWithUniverses (.lit (.natVal 3)) references
  rejects references s!"apply_encoded ({quoted badType} ==> {quoted trueType})"
    "boundary_expr_expected_types"
  let hole := "[\"expr_dag_v2\",0,[[\"c\",[[\"s\",\"sorryAx\"]],[]]],0]"
  rejects references s!"apply_encoded ({quoted trueType} ==> {quoted trueType} using {quoted hole})"
    "forbidden sorryAx"
  runEncodedOutcome references s!"apply_encoded ({quoted trueType} ==> {quoted trueType})"

example : True := by test_encoded_boundary
