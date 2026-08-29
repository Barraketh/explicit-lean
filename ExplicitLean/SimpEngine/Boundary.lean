module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.Tactic
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Meta.CollectMVars
public meta import Lean.Util.CollectLevelMVars

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

syntax boundarySimpArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?

syntax (name := simpEngineBoundaryProbe)
  "simp_engine_boundary_probe" boundarySimpArgs : tactic

syntax (name := simpEngineBoundaryRecord)
  "simp_engine_boundary_record" str boundarySimpArgs : tactic

end Lean.Parser.Tactic

namespace ExplicitLean.SimpEngine.Boundary

private structure ExprMVarBasis where
  id : MVarId
  decl : MetavarDecl

private structure LevelMVarBasis where
  id : LMVarId
  decl : LevelMetavarDecl

private structure PreBoundaryBasis where
  environment : Environment
  exprMVars : Array ExprMVarBasis
  levelMVars : Array LevelMVarBasis
  syntheticMVars : Array MVarId
  pendingMVars : Array MVarId

private structure BoundarySnapshot where
  goals : BoundaryStateFingerprint
  goalDescriptors : Array String
  exprAssignments : Array String
  levelAssignments : Array String
  pendingSynthetic : Array String
  postponed : Array String
  options : String
  deriving BEq, Repr

private structure SelectedLocation where
  fvarIds : Array FVarId
  simplifyTarget : Bool

private def mkPreBoundaryBasis : TacticM PreBoundaryBasis := do
  let mctx ← getMCtx
  let term ← getThe Term.State
  let exprMVars := mctx.decls.toList.toArray
    |>.qsort (fun lhs rhs => lhs.2.index < rhs.2.index)
    |>.map fun (id, decl) => { id, decl }
  let levelMVars := mctx.lDecls.toList.toArray
    |>.qsort (fun lhs rhs => lhs.2.index < rhs.2.index)
    |>.map fun (id, decl) => { id, decl }
  let syntheticMVars := term.syntheticMVars.toList.toArray
    |>.map (·.1)
    |>.qsort (fun lhs rhs => toString lhs.name < toString rhs.name)
  return {
    environment := ← getEnv
    exprMVars := exprMVars
    levelMVars := levelMVars
    syntheticMVars := syntheticMVars
    pendingMVars := term.pendingMVars.toArray
  }

private def localDeclDescriptor (decl : LocalDecl) : MetaM String := do
  let type ← boundaryExprFingerprintHash decl.type
  let value ← decl.value?.mapM boundaryExprFingerprintHash
  let kind := if decl.isLet then "let" else "decl"
  return s!"{decl.index}:{kind}:{repr decl.binderInfo}:{decl.userName}:{type}:{repr value}"

private def goalDescriptor (goal : MVarId) : MetaM String := do
  if ← goal.isAssigned then
    return "assigned"
  goal.withContext do
    let decl ← goal.getDecl
    let targetHash ← boundaryExprFingerprintHash decl.type
    let mut locals := #[]
    for localDecl in decl.lctx do
      locals := locals.push (← localDeclDescriptor localDecl)
    return s!"{decl.depth}:{repr decl.kind}:{decl.numScopeArgs}:{targetHash}:" ++
      String.intercalate "|" locals.toList

private def exprAssignmentDescriptor (basis : ExprMVarBasis) : MetaM String := do
  let mctx ← getMCtx
  withLCtx basis.decl.lctx basis.decl.localInstances do
    if let some value := mctx.eAssignment.find? basis.id then
      return s!"assigned:{← boundaryExprFingerprintHash (← instantiateMVars value)}"
    if let some delayed := mctx.dAssignment.find? basis.id then
      let fvars := delayed.fvars.map (fun fvar => reprStr fvar.fvarId!)
      return s!"delayed:{delayed.mvarIdPending.name}:" ++
        String.intercalate "," fvars.toList
    return "unassigned"

private def levelAssignmentDescriptor (basis : LevelMVarBasis) : MetaM String := do
  let mctx ← getMCtx
  return match mctx.lAssignment.find? basis.id with
    | none => "unassigned"
    | some value => s!"assigned:{repr value}"

private def pendingDescriptor (basis : PreBoundaryBasis) : TacticM (Array String) := do
  let term ← getThe Term.State
  let mctx ← getMCtx
  let mut result := #[]
  for id in basis.syntheticMVars do
    let present := term.syntheticMVars.contains id
    let pending := term.pendingMVars.contains id
    let assigned := mctx.eAssignment.contains id
    let delayed := mctx.dAssignment.contains id
    result := result.push s!"{id.name}:{present}:{pending}:{assigned}:{delayed}"
  let freshSynthetic := term.syntheticMVars.toList.countP fun (id, _) =>
    !basis.syntheticMVars.contains id
  result := result.push s!"freshSynthetic={freshSynthetic}"
  -- New pending entries are a continuation-visible effect. Canonical ordinals
  -- deliberately avoid requiring equal fresh metavariable names.
  let mut nextFresh := 0
  let mut pendingLabels : Array String := #[]
  for id in term.pendingMVars do
    match basis.pendingMVars.findIdx? (· == id) with
    | some index => pendingLabels := pendingLabels.push s!"pre:{index}"
    | none =>
        pendingLabels := pendingLabels.push s!"fresh:{nextFresh}"
        nextFresh := nextFresh + 1
  result := result.push <| "ordered=" ++ String.intercalate ","
    pendingLabels.toList
  return result

private def postponedDescriptor (entry : Meta.PostponedEntry) : MetaM String := do
  let context ← match entry.ctx? with
    | none => pure "none"
    | some ctx => withLCtx ctx.lctx ctx.localInstances do
        let lhs ← boundaryExprFingerprintHash ctx.lhs
        let rhs ← boundaryExprFingerprintHash ctx.rhs
        pure s!"{lhs}:{rhs}"
  return s!"{repr entry.lhs}:{repr entry.rhs}:{context}"

private def boundarySnapshot (basis : PreBoundaryBasis) : TacticM BoundarySnapshot := do
  let goals ← getGoals
  let mut goalDescriptors := #[]
  for goal in goals do
    goalDescriptors := goalDescriptors.push (← goalDescriptor goal)
  let mut exprAssignments := #[]
  for entry in basis.exprMVars do
    exprAssignments := exprAssignments.push (← exprAssignmentDescriptor entry)
  let mut levelAssignments := #[]
  for entry in basis.levelMVars do
    levelAssignments := levelAssignments.push (← levelAssignmentDescriptor entry)
  let metaState ← getThe Meta.State
  let mut postponed := #[]
  for entry in metaState.postponed.toArray do
    postponed := postponed.push (← postponedDescriptor entry)
  return {
    goals := ← boundaryProofStateFingerprint goals
    goalDescriptors
    exprAssignments
    levelAssignments
    pendingSynthetic := ← pendingDescriptor basis
    postponed
    options := boundaryOptionsFingerprint (← getOptions)
  }

private def resolveLocation (simpStx : Syntax) : TacticM SelectedLocation := do
  match expandOptLocation simpStx[5] with
  | .targets hypotheses simplifyTarget =>
      return { fvarIds := ← getFVarIds hypotheses, simplifyTarget }
  | .wildcard =>
      return {
        fvarIds := ← (← getMainGoal).getNondepPropHyps
        simplifyTarget := true
      }

private def executeStockLocation (simpStx : Syntax)
    (selection : SelectedLocation) : TacticM Bool := do
  let initialGoals ← getGoals
  let goal := initialGoals.head!
  let tail := initialGoals.tail
  let r@{ ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  if ctx.config.suggestions then
    throwError "+suggestions requires using simp? instead of simp"
  let result? ← dischargeWrapper.with fun discharge? =>
    withLoopChecking r do
      Prod.fst <$> Meta.simpGoal goal ctx (simprocs := simprocs)
        (discharge? := discharge?) (simplifyTarget := selection.simplifyTarget)
        (fvarIdsToSimp := selection.fvarIds)
  match result? with
  | none =>
      setGoals tail
      return true
  | some (_, next) =>
      setGoals (next :: tail)
      return false

private def validateArtifactExpr (basis : PreBoundaryBasis) (label : String)
    (expression : Expr) : MetaM Unit := do
  for id in ← getMVars expression do
    unless basis.exprMVars.any (fun entry => entry.id == id) do
      throwError "boundary_artifact_fresh_expression_mvar:{label}:{id.name}"
  for id in (collectLevelMVars {} expression).result do
    unless basis.levelMVars.any (fun entry => entry.id == id) do
      throwError "boundary_artifact_fresh_universe_mvar:{label}:{id.name}"

/-- Simp-argument elaboration may create private helper declarations. A closed
    boundary artifact cannot retain references to declarations introduced after
    the saved pre-state, so inline every such definition/theorem transitively. -/
private def closeFreshConstants (basis : PreBoundaryBasis) (expression : Expr) : MetaM Expr := do
  let current ← getEnv
  Core.transform expression (pre := fun subexpression => do
    match subexpression with
    | .const name levels =>
        if basis.environment.contains name then
          return .done subexpression
        let some info := current.find? name
          | throwError "boundary_artifact_fresh_constant_missing:{name}"
        let some value := info.value? (allowOpaque := true)
          | throwError "boundary_artifact_fresh_opaque_constant:{name}"
        return .visit (value.instantiateLevelParams info.levelParams levels)
    | _ => return .continue)

private def captureTransformation (basis : PreBoundaryBasis) (label : String)
    (input : Expr) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge) (stats : Simp.Stats) :
    MetaM (TargetArtifact × Simp.Stats) := do
  let input ← closeFreshConstants basis (← instantiateMVars input)
  let (result, stats) ← Meta.simp input ctx simprocs discharge? stats
  let output ← closeFreshConstants basis (← instantiateMVars result.expr)
  let proof? ← result.proof?.mapM fun proof => do
    closeFreshConstants basis (← instantiateMVars proof)
  validateArtifactExpr basis s!"{label}:input" input
  validateArtifactExpr basis s!"{label}:result" output
  if let some proof := proof? then
    validateArtifactExpr basis s!"{label}:proof" proof
  return ({ input, result := output, proof? }, stats)

private def captureGoalArtifact (basis : PreBoundaryBasis) (simpStx : Syntax)
    (selection : SelectedLocation) : TacticM GoalArtifact := do
  let goal ← getMainGoal
  let r@{ ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  if ctx.config.suggestions then
    throwError "+suggestions requires using simp? instead of simp"
  dischargeWrapper.with fun discharge? =>
    withLoopChecking r do
      let mut current := goal
      let mut locals : Array LocalArtifact := #[]
      let mut stats : Simp.Stats := {}
      for fvarId in selection.fvarIds do
        let (transformation, nextStats) ← current.withContext do
          let decl ← fvarId.getDecl
          let localCtx := ctx.setSimpTheorems <|
            ctx.simpTheorems.eraseTheorem (.fvar decl.fvarId)
          captureTransformation basis s!"local:{decl.userName}" decl.type localCtx
            simprocs discharge? stats
        stats := nextStats
        locals := locals.push { fvarId, transformation }
        if transformation.result.isFalse then
          return { locals }
        if transformation.proof?.isNone then
          current ← current.withContext do
            current.replaceLocalDeclDefEq fvarId transformation.result
      if selection.simplifyTarget then
        let (targetArtifact, _) ← current.withContext do
          captureTransformation basis "target" (← current.getType) ctx simprocs
            discharge? stats
        return { locals, target? := some targetArtifact }
      return { locals }

/-- Eliminate beta redexes whose explicit pretty-printed form would begin with
    the invalid source token `@fun`. This is deliberately narrower than term
    normalization: it visits the expression tree and contracts only applications
    whose head is a lambda, preserving the artifact up to definitional equality. -/
private def prepareArtifactExprForSource (expression : Expr) : MetaM Expr :=
  Core.transform expression (pre := fun subexpression => do
    let reduced := subexpression.headBeta
    if reduced == subexpression then
      return .continue
    return .visit reduced)

/-- Render artifact terms as source, not as display text. The settings are based
    on the earlier proof-source experiment: make elaboration-relevant arguments
    explicit, expose all proof/deep subterms, and disable notation that can lose
    information. Universe and metavariable arguments remain inferable holes;
    their internal identifiers are not stable source names. -/
private def renderArtifactExpr (expression : Expr) : MetaM String := do
  let expression ← prepareArtifactExprForSource expression
  let rendered ← withOptions (fun options => options
      |>.setBool `pp.explicit true
      |>.setBool `pp.instances false
      |>.setBool `pp.universes false
      |>.setBool `pp.fullNames true
      |>.setBool `pp.proofs true
      |>.setBool `pp.deepTerms true
      |>.setBool `pp.notation false
      |>.setBool `pp.match false
      |>.setBool `pp.fieldNotation false
      |>.setBool `pp.structureInstances false
      |>.setBool `pp.coercions false
      |>.setBool `pp.mvars false
      |>.set `pp.maxSteps (100000000 : Nat)
      |>.set `pp.width (1000000 : Nat)) do
    ppExpr expression
  return toString rendered

private def transformationJson (transformation : TargetArtifact) : TacticM Json := do
  let proofJson ← match transformation.proof? with
    | none => pure Json.null
    | some proof => pure (Json.str (← renderArtifactExpr proof))
  return Json.mkObj [
    ("input", Json.str (← renderArtifactExpr transformation.input)),
    ("result", Json.str (← renderArtifactExpr transformation.result)),
    ("proof", proofJson)
  ]

private def artifactReportJson (occurrence : String) (selector : Json)
    (artifact : GoalArtifact) : TacticM Json := withBoundaryEncodedSourceContext do
  let mut localReports := #[]
  for localArtifact in artifact.locals do
    let decl ← localArtifact.fvarId.getDecl
    localReports := localReports.push <| Json.mkObj [
      ("name", Json.str decl.userName.toString),
      ("index", toJson decl.index),
      ("transformation", ← transformationJson localArtifact.transformation)
    ]
  let targetJson ← artifact.target?.mapM transformationJson
  -- The flat target fields keep the first target-only materializer deliberately
  -- simple while the structured fields support full locations.
  let (inputJson, resultJson, proofJson) ← match artifact.target? with
    | none => pure (Json.null, Json.null, Json.null)
    | some targetArtifact => do
        let proofJson ← match targetArtifact.proof? with
          | none => pure Json.null
          | some proof => pure (Json.str (← renderArtifactExpr proof))
        pure (
          Json.str (← renderArtifactExpr targetArtifact.input),
          Json.str (← renderArtifactExpr targetArtifact.result),
          proofJson)
  return Json.mkObj [
    ("occurrence", Json.str occurrence),
    ("selector", selector),
    ("status", Json.str "success"),
    ("locals", Json.arr localReports),
    ("target", targetJson.getD Json.null),
    ("input", inputJson),
    ("result", resultJson),
    ("proof", proofJson)
  ]

private def failureReportJson (occurrence : String) (selector : Json) : Json :=
  Json.mkObj [
    ("occurrence", Json.str occurrence),
    ("selector", selector),
    ("status", Json.str "failure")
  ]

/-- Failed tactics roll back ordinary messages when an enclosing alternative
    catches the exception. Emit the closed failure observation directly so the
    translation harness can materialize the same transactional failure. -/
private def emitFailureReport (occurrence : String) (selector : Json) : TacticM Unit :=
  IO.println s!"SIMP_ENGINE_BOUNDARY_ARTIFACT {(failureReportJson occurrence selector).compress}"

private def runBoundaryProbe (simpStx : Syntax)
    (reportRequest? : Option (String × Json) := none) : TacticM GoalArtifact := do
  let pre ← Tactic.saveState
  let basis ← mkPreBoundaryBasis
  let selection ← try
    resolveLocation simpStx
  catch error =>
    pre.restore
    if let some (occurrence, selector) := reportRequest? then
      emitFailureReport occurrence selector
    throw error
  let stockClosed ← try
    executeStockLocation simpStx selection
  catch error =>
    pre.restore
    if let some (occurrence, selector) := reportRequest? then
      emitFailureReport occurrence selector
    throw error
  let stock ← boundarySnapshot basis
  pre.restore
  let artifact ← try
    captureGoalArtifact basis simpStx selection
  catch error =>
    pre.restore
    throw error
  -- Rendering must happen in the original local context. Proof-bearing local
  -- transformations clear their old declarations during apply, after which a
  -- pretty printer can no longer recover valid source names for the artifact.
  let report? ← reportRequest?.mapM fun (occurrence, selector) =>
    artifactReportJson occurrence selector artifact
  pre.restore
  let initialGoals ← getGoals
  let (applyGoals, applyTerminal) ←
    applyGoalArtifact initialGoals.head! initialGoals.tail artifact
  setGoals applyGoals
  let applied ← boundarySnapshot basis
  unless stock == applied do
    throwError "boundary_post_state_mismatch: stock={repr stock}; apply={repr applied}"
  let applyClosed := applyTerminal != .open
  unless stockClosed == applyClosed do
    throwError "boundary_terminal_mismatch: stockClosed={stockClosed}; apply={repr applyTerminal}"
  let outcome := match applyTerminal with
    | .open => "transported"
    | .closedFromLocalFalse => "closed_false"
    | .closedFromTargetTrue => "closed_true"
  let transformations := artifact.locals.map (·.transformation) ++ artifact.target?.toArray
  let evidence := if transformations.any (·.proof?.isSome) then
      "equality"
    else if transformations.all fun item => item.input == item.result then
      "unchanged"
    else
      "defeq"
  logInfo m!"SIMP_ENGINE_BOUNDARY_PROBE outcome={outcome} evidence={evidence} equivalent=true"
  if let some report := report? then
    logInfo m!"SIMP_ENGINE_BOUNDARY_ARTIFACT {report.compress}"
  return artifact

elab_rules : tactic
  | `(tactic| simp_engine_boundary_probe $args:boundarySimpArgs) => withMainContext do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      discard <| runBoundaryProbe inner
  | `(tactic| simp_engine_boundary_record $occurrence:str $args:boundarySimpArgs) =>
      withMainContext do
        let goals ← getGoals
        let preState ← boundaryProofStateFingerprint goals
        let caller? ← Term.getDeclName?
        let selector := Json.mkObj [
          ("occurrence", Json.str occurrence.getString),
          ("preState", toJson preState),
          ("options", Json.str (boundaryOptionsFingerprint (← getOptions))),
          ("module", Json.str (← getEnv).mainModule.toString),
          ("caller", caller?.map (fun name =>
            Json.str (boundaryCallerIdentity name)) |>.getD Json.null)
        ]
        let inner := mkNode ``Lean.Parser.Tactic.simp #[
          mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
        discard <| runBoundaryProbe inner (some (occurrence.getString, selector))

end ExplicitLean.SimpEngine.Boundary
