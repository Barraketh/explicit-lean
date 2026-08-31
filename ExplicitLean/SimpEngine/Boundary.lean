module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.Tactic
public meta import ExplicitLean.SimpEngine.Boundary.MatchState
public meta import ExplicitLean.SimpEngine.Boundary.LetRecState
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Meta.CollectMVars
public meta import Lean.Util.CollectLevelMVars
public meta import Lean.Meta.Constructions.SparseCasesOn
meta import all Lean.Meta.Constructions.SparseCasesOn

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

syntax boundarySimpArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?

syntax (name := simpEngineBoundaryProbe)
  "simp_engine_boundary_probe" boundarySimpArgs : tactic

syntax (name := simpEngineBoundaryRecord)
  "simp_engine_boundary_record" str boundarySimpArgs : tactic

syntax (name := simpEngineBoundaryComparatorSelfTest)
  "simp_engine_boundary_comparator_self_test" : tactic

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
  checkedDeclarationNames : NameSet
  exprMVars : Array ExprMVarBasis
  levelMVars : Array LevelMVarBasis
  universeReferences : Array LMVarId
  fvarIds : Array FVarId
  syntheticMVars : Array (MVarId × Term.SyntheticMVarDecl)
  letRecsToLift : List Term.LetRecToLift

private structure BoundaryLocalInstance where
  className : Name
  localOrdinal : Nat
  deriving Inhabited, BEq, Repr

private structure BoundaryGoalSnapshot where
  id : MVarId
  decl : MetavarDecl
  deriving Inhabited

private abbrev BoundaryExprMVarStatusTag := Nat

private def boundaryExprUnassigned : BoundaryExprMVarStatusTag := 0
private def boundaryExprAssigned : BoundaryExprMVarStatusTag := 1
private def boundaryExprDelayed : BoundaryExprMVarStatusTag := 2

private structure BoundaryExprMVarStatus where
  tag : BoundaryExprMVarStatusTag
  isProof : Bool
  valueOpt : Option Expr
  pendingOpt : Option MVarId
  fvars : Array Expr

private abbrev BoundaryLevelMVarStatusTag := Nat

private def boundaryLevelUnassigned : BoundaryLevelMVarStatusTag := 0
private def boundaryLevelAssigned : BoundaryLevelMVarStatusTag := 1

private structure BoundaryExprMVarSnapshot where
  id : MVarId
  decl : MetavarDecl
  status : BoundaryExprMVarStatus

private structure BoundaryLevelMVarStatus where
  tag : BoundaryLevelMVarStatusTag
  valueOpt : Option Level

private structure BoundaryLevelMVarSnapshot where
  id : LMVarId
  decl : LevelMetavarDecl
  status : BoundaryLevelMVarStatus

private structure BoundarySyntheticEntry where
  id : MVarId
  decl : Term.SyntheticMVarDecl
  pending : Bool
  assigned : Bool
  delayed : Bool

private structure BoundaryPendingSnapshot where
  synthetic : Array BoundarySyntheticEntry
  pending : Array MVarId

private structure BoundaryDefEqContextSnapshot where
  lhs : Expr
  rhs : Expr
  lctx : LocalContext
  localInstances : LocalInstances
  localInstanceShape : Array BoundaryLocalInstance
  deriving Inhabited

private structure BoundaryPostponedSnapshot where
  lhs : Level
  rhs : Level
  context? : Option BoundaryDefEqContextSnapshot
  deriving Inhabited

private structure BoundarySnapshot where
  goals : Array BoundaryGoalSnapshot
  exprMVars : Array BoundaryExprMVarSnapshot
  levelMVars : Array BoundaryLevelMVarSnapshot
  pendingSynthetic : BoundaryPendingSnapshot
  postponed : Array BoundaryPostponedSnapshot
  options : Options
  auxDeclNGen : DeclNameGenerator
  mctxDepth : Nat
  levelAssignDepth : Nat
  zetaDeltaFVarIds : Array FVarId
  levelNames : List Name
  letRecsToLift : List Term.LetRecToLift
  mctxUserNames : Array (Name × MVarId)
  mvarErrorInfoRoots : Array MVarId
  levelMVarErrorInfoDeps : Array (Array LMVarId)

private structure BoundaryIdMap where
  fvars : Array (FVarId × FVarId)
  mvars : Array (MVarId × MVarId)
  lmvars : Array (LMVarId × LMVarId)

private structure BoundaryMVarPair where
  applied : MVarId
  stock : MVarId
  deriving Inhabited, BEq

private structure SelectedLocation where
  fvarIds : Array FVarId
  simplifyTarget : Bool

private structure BoundaryFullMetaState where
  core : Core.State
  metaState : Meta.State

private def saveBoundaryFullMetaState : MetaM BoundaryFullMetaState := do
  return { core := ← getThe Core.State, metaState := ← getThe Meta.State }

private def BoundaryFullMetaState.restore (state : BoundaryFullMetaState) : MetaM Unit := do
  modifyThe Core.State fun _ => state.core
  modifyThe Meta.State fun _ => state.metaState

private def withRestoredBoundaryFullMetaState (action : MetaM α) : MetaM α := do
  let saved ← saveBoundaryFullMetaState
  try action finally saved.restore

private def boundaryLocalDecls (lctx : LocalContext) : Array LocalDecl :=
  lctx.foldl (fun decls decl => decls.push decl) #[]

private def mkPreBoundaryBasis : TacticM PreBoundaryBasis := do
  let environment ← getEnv
  -- Environment.constants is the checked view, including declarations from
  -- prior async branches. Snapshot that same domain before stock execution;
  -- Environment.contains defaults to skipping other branches' realizations.
  let checkedDeclarationNames := environment.constants.foldStage2
    (fun names name _ => names.insert name) ({} : NameSet)
  let mctx ← getMCtx
  let term ← getThe Term.State
  let goals ← getGoals
  let universeReferences ← boundaryUniverseReferences goals term
  let exprMVars := mctx.decls.toList.toArray
    |>.qsort (fun lhs rhs => lhs.2.index < rhs.2.index)
    |>.map fun (id, decl) => { id, decl }
  let levelMVars := mctx.lDecls.toList.toArray
    |>.qsort (fun lhs rhs => lhs.2.index < rhs.2.index)
    |>.map fun (id, decl) => { id, decl }
  let mut fvarIds : Array FVarId := #[]
  for goal in goals do
    let decl ← goal.getDecl
    fvarIds := fvarIds ++ decl.lctx.getFVarIds
  for (_, decl) in mctx.decls.toList do
    fvarIds := fvarIds ++ decl.lctx.getFVarIds
  -- Assignments retained by Lean can refer to locals no longer present in any
  -- metavariable declaration's context (for example, after `use`). These IDs
  -- already existed at the boundary and must be compared by exact identity;
  -- treating them as fresh would reject even an unchanged assignment.
  for (_, expression) in mctx.eAssignment.toList do
    fvarIds := fvarIds ++ (collectFVars {} expression).fvarIds
  -- Pending recursion may retain locals outside the current goal contexts.
  -- These IDs already existed at entry and retain their exact identities.
  for entry in term.letRecsToLift do
    fvarIds := fvarIds.push entry.fvarId ++ entry.lctx.getFVarIds
    fvarIds := fvarIds ++ (collectFVars {} entry.type).fvarIds
    fvarIds := fvarIds ++ (collectFVars {} entry.val).fvarIds
    for localInstance in entry.localInstances do
      fvarIds := fvarIds ++ (collectFVars {} localInstance.fvar).fvarIds
  let metaState ← getThe Meta.State
  for entry in metaState.postponed do
    if let some context := entry.ctx? then
      fvarIds := fvarIds ++ context.lctx.getFVarIds
  let mut uniqueFVarIds : Array FVarId := #[]
  for id in fvarIds do
    unless uniqueFVarIds.contains id do
      uniqueFVarIds := uniqueFVarIds.push id
  let allFVarIds := uniqueFVarIds
  let syntheticMVars := term.syntheticMVars.toList.toArray
    |>.qsort (fun lhs rhs => toString lhs.1.name < toString rhs.1.name)
  return {
    environment
    checkedDeclarationNames
    exprMVars
    levelMVars
    universeReferences
    fvarIds := allFVarIds
    syntheticMVars
    letRecsToLift := term.letRecsToLift
  }

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

private def instantiateBoundaryLevels (expression : Expr) : MetaM Expr :=
  Core.transform expression (pre := fun subexpression => do
    match subexpression with
    | .sort level =>
        return .done (.sort (← instantiateLevelMVars level))
    | .const name levels =>
        let levels ← levels.mapM instantiateLevelMVars
        return .done (.const name levels)
    | _ => return .continue)

private def captureBoundaryExpr (basis : PreBoundaryBasis) (expression : Expr) : MetaM Expr :=
  withRestoredBoundaryFullMetaState do
    let expression ← instantiateMVars expression
    let expression ← closeFreshConstants basis expression
    let expression ← instantiateMVars expression
    instantiateBoundaryLevels expression

private def validateBoundaryRawExprConstants
    (basis : PreBoundaryBasis) (expression : Expr) : MetaM Unit := do
  let _ ← Core.transform expression (pre := fun subexpression => do
    match subexpression with
    | .const name _ =>
        unless basis.environment.contains name do
          throwError "boundary_comparison_unpaired_fresh_constant"
        return .done subexpression
    | _ => return .continue)
  pure ()

private def validateBoundaryRawLocalContext
    (basis : PreBoundaryBasis) (lctx : LocalContext) : MetaM Unit := do
  for localDecl in boundaryLocalDecls lctx do
    match localDecl with
    | .cdecl _ _ _ type _ _ =>
        validateBoundaryRawExprConstants basis type
    | .ldecl _ _ _ type value _ _ =>
        validateBoundaryRawExprConstants basis type
        validateBoundaryRawExprConstants basis value

private def validateBoundaryRawMVarDecl
    (basis : PreBoundaryBasis) (decl : MetavarDecl) : MetaM Unit := do
  validateBoundaryRawLocalContext basis decl.lctx
  validateBoundaryRawExprConstants basis decl.type

private def captureGoalSnapshot
    (basis : PreBoundaryBasis) (goal : MVarId) : TacticM BoundaryGoalSnapshot := do
  unless !(← goal.isAssigned) do
    throwError "boundary_comparison_unpaired_assigned_goal"
  let decl ← goal.getDecl
  validateBoundaryRawMVarDecl basis decl
  return { id := goal, decl }

private def captureExprMVarSnapshot (basis : PreBoundaryBasis)
    (id : MVarId) (decl : MetavarDecl) : TacticM BoundaryExprMVarSnapshot := do
  let mctx ← getMCtx
  validateBoundaryRawMVarDecl basis decl
  withLCtx decl.lctx decl.localInstances do
    let assignmentIsProof ← withRestoredBoundaryFullMetaState <| isProp decl.type
    let status ← match mctx.eAssignment.find? id, mctx.dAssignment.find? id with
    | some value, none =>
        let value ← captureBoundaryExpr basis value
        pure ({ tag := boundaryExprAssigned, isProof := assignmentIsProof, valueOpt := some value, pendingOpt := none, fvars := #[] } : BoundaryExprMVarStatus)
    | none, some delayed =>
        pure ({ tag := boundaryExprDelayed, isProof := false, valueOpt := none, pendingOpt := some delayed.mvarIdPending, fvars := delayed.fvars } : BoundaryExprMVarStatus)
    | none, none =>
        pure ({ tag := boundaryExprUnassigned, isProof := false, valueOpt := none, pendingOpt := none, fvars := #[] } : BoundaryExprMVarStatus)
    | some _, some _ =>
        throwError s!"boundary_comparison_invalid_mvar_assignment:{decl.index}"
    return { id, decl, status }

private def captureLevelMVarSnapshot
    (id : LMVarId) (decl : LevelMetavarDecl) : TacticM BoundaryLevelMVarSnapshot := do
  let mctx ← getMCtx
  let status ← match mctx.lAssignment.find? id with
  | none => pure { tag := boundaryLevelUnassigned, valueOpt := none }
  | some level =>
      let level ← withRestoredBoundaryFullMetaState <| instantiateLevelMVars level
      pure { tag := boundaryLevelAssigned, valueOpt := some level }
  return { id, decl, status }

private def capturePendingSnapshot : TacticM BoundaryPendingSnapshot := do
  let term ← getThe Term.State
  let mctx ← getMCtx
  let synthetic := term.syntheticMVars.toList.toArray
    |>.qsort (fun lhs rhs => toString lhs.1.name < toString rhs.1.name)
    |>.map fun (id, decl) => {
      id
      decl
      pending := term.pendingMVars.contains id
      assigned := mctx.eAssignment.contains id
      delayed := mctx.dAssignment.contains id
    }
  return { synthetic, pending := term.pendingMVars.toArray }

private def capturePostponedSnapshot (basis : PreBoundaryBasis)
    (entry : Meta.PostponedEntry) : TacticM BoundaryPostponedSnapshot := do
  let lhs ← withRestoredBoundaryFullMetaState <| instantiateLevelMVars entry.lhs
  let rhs ← withRestoredBoundaryFullMetaState <| instantiateLevelMVars entry.rhs
  let context? ← match entry.ctx? with
  | none => pure none
  | some context => do
      validateBoundaryRawLocalContext basis context.lctx
      let lhs ← withLCtx context.lctx context.localInstances <|
        captureBoundaryExpr basis context.lhs
      let rhs ← withLCtx context.lctx context.localInstances <|
        captureBoundaryExpr basis context.rhs
      let decls := boundaryLocalDecls context.lctx
      let mut localInstances := #[]
      for localInstance in context.localInstances do
        unless localInstance.fvar.isFVar do
          throwError "boundary_comparison_unpaired_local_instance"
        let some ordinal := decls.findIdx? (fun decl =>
            decl.fvarId == localInstance.fvar.fvarId!)
          | throwError "boundary_comparison_unpaired_local_instance"
        localInstances := localInstances.push {
          className := localInstance.className
          localOrdinal := ordinal
        }
      pure <| some {
        lhs
        rhs
        lctx := context.lctx
        localInstances := context.localInstances
        localInstanceShape := localInstances
      }
  return { lhs, rhs, context? }

private def captureBoundaryLevelErrorDeps
    (entry : Term.LevelMVarErrorInfo) : TacticM (Array LMVarId) := do
  withRestoredBoundaryFullMetaState do
    withLCtx entry.lctx #[] do
      let expression ← instantiateMVars entry.expr
      return (collectLevelMVars {} expression).result

private def boundarySnapshot (basis : PreBoundaryBasis) : TacticM BoundarySnapshot := do
  let auxDeclNGen ← getDeclNGen
  let goals ← (← getGoals).toArray.mapM (captureGoalSnapshot basis)
  let mctx ← getMCtx
  let exprMVars := mctx.decls.toList.toArray
    |>.qsort (fun lhs rhs => lhs.2.index < rhs.2.index)
  let exprMVars ← exprMVars.mapM fun (id, decl) =>
    captureExprMVarSnapshot basis id decl
  let levelMVars := mctx.lDecls.toList.toArray
    |>.qsort (fun lhs rhs => lhs.2.index < rhs.2.index)
  let levelMVars ← levelMVars.mapM fun (id, decl) =>
    captureLevelMVarSnapshot id decl
  let metaState ← getThe Meta.State
  let postponed ← metaState.postponed.toArray.mapM (capturePostponedSnapshot basis)
  let term ← getThe Term.State
  let mctxUserNames := mctx.userNames.toList.toArray
    |>.qsort (fun lhs rhs => toString lhs.1 < toString rhs.1)
  let mvarErrorInfoRoots := term.mvarErrorInfos.toArray.map (·.mvarId)
  let levelMVarErrorInfoDeps ← term.levelMVarErrorInfos.toArray.mapM
    captureBoundaryLevelErrorDeps
  return {
    goals
    exprMVars
    levelMVars
    pendingSynthetic := ← capturePendingSnapshot
    postponed
    options := ← getOptions
    auxDeclNGen
    mctxDepth := mctx.depth
    levelAssignDepth := mctx.levelAssignDepth
    zetaDeltaFVarIds := metaState.zetaDeltaFVarIds.toList.toArray
    levelNames := term.levelNames
    letRecsToLift := term.letRecsToLift
    mctxUserNames
    mvarErrorInfoRoots
    levelMVarErrorInfoDeps
  }

private def boundaryComparisonMismatch {α : Type} (label : String) : TacticM α :=
  throwError s!"boundary_comparison_mismatch:{label}"

private def boundaryEnvironmentActionName : EnvironmentAction → Name
  | EnvironmentAction.declareCongruence name _ => name
  | EnvironmentAction.declareEquation name _ => name
  | EnvironmentAction.declareMatcher anchor _ => anchor
  | EnvironmentAction.declareLocalTheorems anchor _ => anchor
  | EnvironmentAction.realizeGroups anchor _ => anchor

private def boundaryEnvironmentActionJson (action : EnvironmentAction) : Json :=
  match action with
  | EnvironmentAction.declareCongruence name payload => Json.mkObj [
      ("kind", Json.str "declare_congruence"),
      ("name", Json.str name.toString),
      ("nameParts", encodeBoundaryName name),
      ("declaration", Json.str payload)
    ]
  | EnvironmentAction.declareEquation name payload => Json.mkObj [
      ("kind", Json.str "declare_equation"),
      ("name", Json.str name.toString),
      ("nameParts", encodeBoundaryName name),
      ("declaration", Json.str payload)
    ]
  | EnvironmentAction.declareMatcher anchor payload => Json.mkObj [
      ("kind", Json.str "declare_matcher"),
      ("name", Json.str anchor.toString),
      ("nameParts", encodeBoundaryName anchor),
      ("declaration", Json.str payload)
    ]
  | EnvironmentAction.declareLocalTheorems anchor payload => Json.mkObj [
      ("kind", Json.str "declare_local_theorems"),
      ("name", Json.str anchor.toString),
      ("nameParts", encodeBoundaryName anchor),
      ("declaration", Json.str payload)
    ]
  | EnvironmentAction.realizeGroups anchor payload => Json.mkObj [
      ("kind", Json.str "realize_groups"),
      ("name", Json.str anchor.toString),
      ("nameParts", encodeBoundaryName anchor),
      ("declaration", Json.str payload)
    ]

private def boundaryMetavarKindEq : MetavarKind → MetavarKind → Bool
  | .natural, .natural => true
  | .synthetic, .synthetic => true
  | .syntheticOpaque, .syntheticOpaque => true
  | _, _ => false

private def findExprMVarSnapshot? (snapshot : BoundarySnapshot)
    (id : MVarId) : Option BoundaryExprMVarSnapshot :=
  snapshot.exprMVars.find? (fun entry => entry.id == id)

private def findLevelMVarSnapshot? (snapshot : BoundarySnapshot)
    (id : LMVarId) : Option BoundaryLevelMVarSnapshot :=
  snapshot.levelMVars.find? (fun entry => entry.id == id)

private def findSyntheticSnapshot? (snapshot : BoundarySnapshot)
    (id : MVarId) : Option BoundarySyntheticEntry :=
  snapshot.pendingSynthetic.synthetic.find? (fun entry => entry.id == id)

private def findPairByApplied? {α : Type} [BEq α]
    (pairs : Array (α × α)) (id : α) : Option α :=
  pairs.find? (fun pair => pair.1 == id) |>.map (·.2)

private def findPairByStock? {α : Type} [BEq α]
    (pairs : Array (α × α)) (id : α) : Option α :=
  pairs.find? (fun pair => pair.2 == id) |>.map (·.1)

private def pairFVarIds (basis : PreBoundaryBasis) (mapping : BoundaryIdMap)
    (applied stock : FVarId) (label : String) : TacticM BoundaryIdMap := do
  match findPairByApplied? mapping.fvars applied, findPairByStock? mapping.fvars stock with
  | some mapped, _ =>
      unless mapped == stock do boundaryComparisonMismatch s!"{label}.fvar"
      return mapping
  | none, some _ =>
      boundaryComparisonMismatch s!"{label}.fvar.injective"
  | none, none =>
      let appliedPre := basis.fvarIds.contains applied
      let stockPre := basis.fvarIds.contains stock
      unless (!appliedPre && !stockPre) || (appliedPre && stockPre && applied == stock) do
        boundaryComparisonMismatch s!"{label}.fvar.pre"
      return { mapping with fvars := mapping.fvars.push (applied, stock) }

private def pairMVarIds (basis : PreBoundaryBasis) (mapping : BoundaryIdMap)
    (applied stock : MVarId) (label : String) : TacticM BoundaryIdMap := do
  match findPairByApplied? mapping.mvars applied, findPairByStock? mapping.mvars stock with
  | some mapped, _ =>
      unless mapped == stock do boundaryComparisonMismatch s!"{label}.mvar"
      return mapping
  | none, some _ =>
      boundaryComparisonMismatch s!"{label}.mvar.injective"
  | none, none =>
      let appliedPre := basis.exprMVars.any (fun entry => entry.id == applied)
      let stockPre := basis.exprMVars.any (fun entry => entry.id == stock)
      unless (!appliedPre && !stockPre) || (appliedPre && stockPre && applied == stock) do
        boundaryComparisonMismatch s!"{label}.mvar.pre"
      return { mapping with mvars := mapping.mvars.push (applied, stock) }

private def pairLMVarIds (basis : PreBoundaryBasis) (mapping : BoundaryIdMap)
    (applied stock : LMVarId) (label : String) : TacticM BoundaryIdMap := do
  let mappedApplied := findPairByApplied? mapping.lmvars applied
  let mappedStock := findPairByStock? mapping.lmvars stock
  match mappedApplied, mappedStock with
  | some mapped, _ =>
      unless mapped == stock do boundaryComparisonMismatch s!"{label}.universe"
      return mapping
  | none, some _ =>
      boundaryComparisonMismatch s!"{label}.universe.injective"
  | none, none =>
      let appliedPre := basis.levelMVars.any (fun entry => entry.id == applied)
      let stockPre := basis.levelMVars.any (fun entry => entry.id == stock)
      unless (!appliedPre && !stockPre) || (appliedPre && stockPre && applied == stock) do
        boundaryComparisonMismatch s!"{label}.universe.pre"
      return { mapping with lmvars := mapping.lmvars.push (applied, stock) }

private def pairBoundaryLevelAssignments (basis : PreBoundaryBasis)
    (mapping : BoundaryIdMap) (stock applied : BoundarySnapshot) : TacticM BoundaryIdMap := do
  let mut mapping := mapping
  let mut ordinal := 0
  while h : ordinal < mapping.lmvars.size do
    let pair := mapping.lmvars[ordinal]
    ordinal := ordinal + 1
    let some stockEntry := findLevelMVarSnapshot? stock pair.2
      | throwError "boundary_comparison_unpaired_mapped_universe_mvar"
    let some appliedEntry := findLevelMVarSnapshot? applied pair.1
      | throwError "boundary_comparison_unpaired_mapped_universe_mvar"
    match stockEntry.status.valueOpt, appliedEntry.status.valueOpt with
    | some stockLevel, some appliedLevel =>
        let stockLevels := (collectLevelMVars {} (.sort stockLevel)).result
        let appliedLevels := (collectLevelMVars {} (.sort appliedLevel)).result
        unless stockLevels.size == appliedLevels.size do
          throwError s!"boundary_comparison_unpaired_fresh_universe_mvar:assignment[{ordinal - 1}]"
        for h : levelOrdinal in *...stockLevels.size do
          let some appliedLevelMVar := appliedLevels[levelOrdinal]?
            | throwError "boundary_comparison_unpaired_fresh_universe_mvar"
          mapping ← pairLMVarIds basis mapping appliedLevelMVar stockLevels[levelOrdinal]
            s!"levelMVars.assignment[{ordinal - 1}][{levelOrdinal}]"
    | none, none => pure ()
    | _, _ => pure ()
  return mapping

private def initialBoundaryIdMap (basis : PreBoundaryBasis) : BoundaryIdMap :=
  {
    fvars := basis.fvarIds.map fun id => (id, id)
    mvars := basis.exprMVars.map fun entry => (entry.id, entry.id)
    lmvars := basis.levelMVars.map fun entry => (entry.id, entry.id)
  }

private def pairBoundaryLevels (basis : PreBoundaryBasis) (mapping : BoundaryIdMap)
    (stock applied : Expr) (label : String) : TacticM BoundaryIdMap := do
  let stockLevels := (collectLevelMVars {} stock).result
  let appliedLevels := (collectLevelMVars {} applied).result
  unless stockLevels.size == appliedLevels.size do
    throwError s!"boundary_comparison_unpaired_fresh_universe_mvar:{label}"
  let mut mapping := mapping
  for h : ordinal in *...stockLevels.size do
    let some appliedLevel := appliedLevels[ordinal]?
      | throwError s!"boundary_comparison_unpaired_fresh_universe_mvar:{label}"
    mapping ← pairLMVarIds basis mapping appliedLevel
      stockLevels[ordinal] s!"{label}[{ordinal}]"
  return mapping

private def pairBoundaryExprMVars (basis : PreBoundaryBasis) (mapping : BoundaryIdMap)
    (queue : Array BoundaryMVarPair) (stock applied : Expr) (label : String) :
    TacticM (BoundaryIdMap × Array BoundaryMVarPair) := do
  let stockMVars := (stock.collectMVars {}).result
  let appliedMVars := (applied.collectMVars {}).result
  unless stockMVars.size == appliedMVars.size do
    throwError s!"boundary_comparison_unpaired_fresh_expression_mvar:{label}"
  let mut mapping := mapping
  let mut queue := queue
  for h : ordinal in *...stockMVars.size do
    let some appliedMVar := appliedMVars[ordinal]?
      | throwError s!"boundary_comparison_unpaired_fresh_expression_mvar:{label}"
    mapping ← pairMVarIds basis mapping appliedMVar
      stockMVars[ordinal] s!"{label}[{ordinal}]"
    queue := queue.push { applied := appliedMVar, stock := stockMVars[ordinal] }
  mapping ← pairBoundaryLevels basis mapping stock applied label
  return (mapping, queue)

private def pairBoundaryProofRoots (basis : PreBoundaryBasis)
    (mapping : BoundaryIdMap) (queue : Array BoundaryMVarPair)
    (stock applied : Expr) (label : String) :
    TacticM (BoundaryIdMap × Array BoundaryMVarPair) := do
  let stockMVars := (stock.collectMVars {}).result
  let appliedMVars := (applied.collectMVars {}).result
  let mut mapping := mapping
  let mut queue := queue
  if stockMVars.size == appliedMVars.size then
    for h : ordinal in *...stockMVars.size do
      let some appliedMVar := appliedMVars[ordinal]?
        | return (mapping, queue)
      mapping ← pairMVarIds basis mapping appliedMVar stockMVars[ordinal]
        s!"{label}.mvar[{ordinal}]"
      queue := queue.push { applied := appliedMVar, stock := stockMVars[ordinal] }
    let stockLevels := (collectLevelMVars {} stock).result
    let appliedLevels := (collectLevelMVars {} applied).result
    if stockLevels.size == appliedLevels.size then
      for h : ordinal in *...stockLevels.size do
        let some appliedLevel := appliedLevels[ordinal]?
          | return (mapping, queue)
        mapping ← pairLMVarIds basis mapping appliedLevel stockLevels[ordinal]
          s!"{label}.universe[{ordinal}]"
  return (mapping, queue)

private def compareBoundaryLocalDeclShape (label : String)
    (stock applied : LocalDecl) : TacticM Unit := do
  unless stock.userName == applied.userName do
    boundaryComparisonMismatch s!"{label}.userName"
  match stock, applied with
  | .cdecl _ _ _ _ stockBinder stockKind, .cdecl _ _ _ _ appliedBinder appliedKind =>
      unless stockBinder == appliedBinder do
        boundaryComparisonMismatch s!"{label}.binderInfo"
      unless stockKind == appliedKind do
        boundaryComparisonMismatch s!"{label}.kind"
  | .ldecl _ _ _ _ _ stockNondep stockKind, .ldecl _ _ _ _ _ appliedNondep appliedKind =>
      unless stockNondep == appliedNondep do
        boundaryComparisonMismatch s!"{label}.nondep"
      unless stockKind == appliedKind do
        boundaryComparisonMismatch s!"{label}.kind"
  | _, _ => boundaryComparisonMismatch s!"{label}.shape"

private def pairBoundaryLocalInstances (basis : PreBoundaryBasis)
    (mapping : BoundaryIdMap) (stock applied : LocalInstances) (label : String) :
    TacticM BoundaryIdMap := do
  unless stock.size == applied.size do boundaryComparisonMismatch s!"{label}.count"
  let mut mapping := mapping
  for h : ordinal in *...stock.size do
    let stockInstance := stock[ordinal]
    let appliedInstance := applied[ordinal]!
    unless stockInstance.className == appliedInstance.className do
      boundaryComparisonMismatch s!"{label}[{ordinal}].class"
    unless stockInstance.fvar.isFVar && appliedInstance.fvar.isFVar do
      throwError "boundary_comparison_unpaired_local_instance"
    mapping ← pairFVarIds basis mapping appliedInstance.fvar.fvarId!
      stockInstance.fvar.fvarId! s!"{label}[{ordinal}]"
  return mapping

private def pairBoundaryLocalContext (basis : PreBoundaryBasis)
    (mapping : BoundaryIdMap) (queue : Array BoundaryMVarPair)
    (stock applied : LocalContext) (label : String) :
    TacticM (BoundaryIdMap × Array BoundaryMVarPair) := do
  let stockDecls := boundaryLocalDecls stock
  let appliedDecls := boundaryLocalDecls applied
  unless stockDecls.size == appliedDecls.size do
    boundaryComparisonMismatch s!"{label}.count"
  let mut mapping := mapping
  for h : ordinal in *...stockDecls.size do
    let stockDecl := stockDecls[ordinal]
    let appliedDecl := appliedDecls[ordinal]!
    mapping ← pairFVarIds basis mapping appliedDecl.fvarId stockDecl.fvarId
      s!"{label}[{ordinal}]"
  let mut queue := queue
  for h : ordinal in *...stockDecls.size do
    let stockDecl := stockDecls[ordinal]
    let appliedDecl := appliedDecls[ordinal]!
    compareBoundaryLocalDeclShape s!"{label}[{ordinal}]" stockDecl appliedDecl
    let (mapping', queue') ← pairBoundaryExprMVars basis mapping queue
      stockDecl.type appliedDecl.type s!"{label}[{ordinal}].type"
    mapping := mapping'
    queue := queue'
    match stockDecl, appliedDecl with
    | .cdecl .., .cdecl .. => pure ()
    | .ldecl _ _ _ _ stockValue _ _, .ldecl _ _ _ _ appliedValue _ _ =>
        let (mapping', queue') ← pairBoundaryExprMVars basis mapping queue
          stockValue appliedValue s!"{label}[{ordinal}].value"
        mapping := mapping'
        queue := queue'
    | _, _ => pure ()
  return (mapping, queue)

private def pairBoundaryMVarDeclLocalInstances (basis : PreBoundaryBasis)
    (mapping : BoundaryIdMap) (stock applied : MetavarDecl) (label : String) :
    TacticM BoundaryIdMap :=
  pairBoundaryLocalInstances basis mapping stock.localInstances applied.localInstances label

private def buildBoundaryIdMap (basis : PreBoundaryBasis)
    (stock applied : BoundarySnapshot) : TacticM BoundaryIdMap := do
  unless stock.goals.size == applied.goals.size do
    boundaryComparisonMismatch "goals.count"
  let mut mapping := initialBoundaryIdMap basis
  let mut queue : Array BoundaryMVarPair := #[]
  for h : ordinal in *...stock.goals.size do
    let stockGoal := stock.goals[ordinal]
    let appliedGoal := applied.goals[ordinal]!
    mapping ← pairMVarIds basis mapping appliedGoal.id stockGoal.id s!"goals[{ordinal}]"
    queue := queue.push { applied := appliedGoal.id, stock := stockGoal.id }
    let (mapping', queue') ← pairBoundaryLocalContext basis mapping queue
      stockGoal.decl.lctx appliedGoal.decl.lctx s!"goals[{ordinal}].locals"
    mapping := mapping'
    queue := queue'
    mapping ← pairBoundaryLocalInstances basis mapping
      stockGoal.decl.localInstances appliedGoal.decl.localInstances
      s!"goals[{ordinal}].localInstances"
    let (mapping', queue') ← pairBoundaryExprMVars basis mapping queue
      stockGoal.decl.type appliedGoal.decl.type s!"goals[{ordinal}].target"
    mapping := mapping'
    queue := queue'
  unless stock.mctxUserNames.size == applied.mctxUserNames.size do
    boundaryComparisonMismatch "mctx.userNames.count"
  for h : ordinal in *...stock.mctxUserNames.size do
    let stockEntry := stock.mctxUserNames[ordinal]
    let appliedEntry := applied.mctxUserNames[ordinal]!
    unless stockEntry.1 == appliedEntry.1 do
      boundaryComparisonMismatch s!"mctx.userNames[{ordinal}].name"
    mapping ← pairMVarIds basis mapping appliedEntry.2 stockEntry.2
      s!"mctx.userNames[{ordinal}].mvar"
    queue := queue.push { applied := appliedEntry.2, stock := stockEntry.2 }
  unless stock.mvarErrorInfoRoots.size == applied.mvarErrorInfoRoots.size do
    boundaryComparisonMismatch "mvarErrorInfos.count"
  for h : ordinal in *...stock.mvarErrorInfoRoots.size do
    mapping ← pairMVarIds basis mapping applied.mvarErrorInfoRoots[ordinal]!
      stock.mvarErrorInfoRoots[ordinal] s!"mvarErrorInfos[{ordinal}]"
    queue := queue.push {
      applied := applied.mvarErrorInfoRoots[ordinal]!
      stock := stock.mvarErrorInfoRoots[ordinal]
    }
  unless stock.levelMVarErrorInfoDeps.size == applied.levelMVarErrorInfoDeps.size do
    boundaryComparisonMismatch "levelMVarErrorInfos.count"
  for h : entryOrdinal in *...stock.levelMVarErrorInfoDeps.size do
    let stockDeps := stock.levelMVarErrorInfoDeps[entryOrdinal]
    let appliedDeps := applied.levelMVarErrorInfoDeps[entryOrdinal]!
    unless stockDeps.size == appliedDeps.size do
      boundaryComparisonMismatch s!"levelMVarErrorInfos[{entryOrdinal}].count"
    for h : ordinal in *...stockDeps.size do
      let some appliedLevel := appliedDeps[ordinal]?
        | throwError "boundary_comparison_unpaired_fresh_universe_mvar"
      mapping ← pairLMVarIds basis mapping appliedLevel stockDeps[ordinal]
        s!"levelMVarErrorInfos[{entryOrdinal}][{ordinal}]"
  unless stock.pendingSynthetic.pending.size == applied.pendingSynthetic.pending.size do
    boundaryComparisonMismatch "pendingSynthetic.pending.count"
  for h : ordinal in *...stock.pendingSynthetic.pending.size do
    mapping ← pairMVarIds basis mapping applied.pendingSynthetic.pending[ordinal]!
      stock.pendingSynthetic.pending[ordinal] s!"pendingSynthetic.pending[{ordinal}]"
    queue := queue.push {
      applied := applied.pendingSynthetic.pending[ordinal]!
      stock := stock.pendingSynthetic.pending[ordinal]
    }
  unless stock.postponed.size == applied.postponed.size do
    boundaryComparisonMismatch "postponed.count"
  for h : ordinal in *...stock.postponed.size do
    let stockEntry := stock.postponed[ordinal]
    let appliedEntry := applied.postponed[ordinal]!
    let (mapping', queue') ← pairBoundaryExprMVars basis mapping queue
      (.sort stockEntry.lhs) (.sort appliedEntry.lhs)
      s!"postponed[{ordinal}].lhs"
    mapping := mapping'
    queue := queue'
    let (mapping', queue') ← pairBoundaryExprMVars basis mapping queue
      (.sort stockEntry.rhs) (.sort appliedEntry.rhs)
      s!"postponed[{ordinal}].rhs"
    mapping := mapping'
    queue := queue'
    match stockEntry.context?, appliedEntry.context? with
    | none, none => pure ()
    | some stockContext, some appliedContext =>
        let (mapping', queue') ← pairBoundaryLocalContext basis mapping queue
          stockContext.lctx appliedContext.lctx s!"postponed[{ordinal}].context.locals"
        mapping := mapping'
        queue := queue'
        mapping ← pairBoundaryLocalInstances basis mapping stockContext.localInstances
          appliedContext.localInstances s!"postponed[{ordinal}].context.localInstances"
        let (mapping', queue') ← pairBoundaryExprMVars basis mapping queue
          stockContext.lhs appliedContext.lhs s!"postponed[{ordinal}].context.lhs"
        mapping := mapping'
        queue := queue'
        let (mapping', queue') ← pairBoundaryExprMVars basis mapping queue
          stockContext.rhs appliedContext.rhs s!"postponed[{ordinal}].context.rhs"
        mapping := mapping'
        queue := queue'
    | _, _ => boundaryComparisonMismatch s!"postponed[{ordinal}].context.presence"
  for entry in basis.exprMVars do
    let some stockEntry := findExprMVarSnapshot? stock entry.id
      | boundaryComparisonMismatch s!"exprMVars[{entry.decl.index}].missingStock"
    let some appliedEntry := findExprMVarSnapshot? applied entry.id
      | boundaryComparisonMismatch s!"exprMVars[{entry.decl.index}].missingApplied"
    queue := queue.push { applied := appliedEntry.id, stock := stockEntry.id }
  let mut processed : Array BoundaryMVarPair := #[]
  while h : queue.size > 0 do
    let pair := queue.back!
    queue := queue.pop
    unless processed.contains pair do
      processed := processed.push pair
      let some stockEntry := findExprMVarSnapshot? stock pair.stock
        | boundaryComparisonMismatch "exprMVars.missingStock"
      let some appliedEntry := findExprMVarSnapshot? applied pair.applied
        | boundaryComparisonMismatch "exprMVars.missingApplied"
      unless boundaryMetavarKindEq stockEntry.decl.kind appliedEntry.decl.kind do
        boundaryComparisonMismatch "exprMVars.kind"
      unless stockEntry.decl.depth == appliedEntry.decl.depth do
        boundaryComparisonMismatch "exprMVars.depth"
      unless stockEntry.decl.numScopeArgs == appliedEntry.decl.numScopeArgs do
        boundaryComparisonMismatch "exprMVars.numScopeArgs"
      let (mapping', queue') ← pairBoundaryLocalContext basis mapping queue
        stockEntry.decl.lctx appliedEntry.decl.lctx "exprMVars.lctx"
      mapping := mapping'
      queue := queue'
      mapping ← pairBoundaryMVarDeclLocalInstances basis mapping
        stockEntry.decl appliedEntry.decl "exprMVars.localInstances"
      let (mapping', queue') ← pairBoundaryExprMVars basis mapping queue
        stockEntry.decl.type appliedEntry.decl.type "exprMVars.type"
      mapping := mapping'
      queue := queue'
      unless stockEntry.status.tag == appliedEntry.status.tag do
        boundaryComparisonMismatch "exprMVars.assignment.status"
      if stockEntry.status.tag == boundaryExprAssigned then
        unless stockEntry.status.isProof == appliedEntry.status.isProof do
          boundaryComparisonMismatch "exprMVars.assignment.proofStatus"
        let some stockValue := stockEntry.status.valueOpt
          | boundaryComparisonMismatch "exprMVars.assignment.stockValue"
        let some appliedValue := appliedEntry.status.valueOpt
          | boundaryComparisonMismatch "exprMVars.assignment.appliedValue"
        let (mapping', queue') ← if stockEntry.status.isProof then
          pairBoundaryProofRoots basis mapping queue stockValue appliedValue
            "exprMVars.assignment"
        else
          pairBoundaryExprMVars basis mapping queue stockValue appliedValue
            "exprMVars.assignment"
        mapping := mapping'
        queue := queue'
      else if stockEntry.status.tag == boundaryExprDelayed then
        let some stockPending := stockEntry.status.pendingOpt
          | boundaryComparisonMismatch "exprMVars.delayed.stockPending"
        let some appliedPending := appliedEntry.status.pendingOpt
          | boundaryComparisonMismatch "exprMVars.delayed.appliedPending"
        mapping ← pairMVarIds basis mapping appliedPending stockPending
          "exprMVars.delayed.pending"
        queue := queue.push { applied := appliedPending, stock := stockPending }
        unless stockEntry.status.fvars.size == appliedEntry.status.fvars.size do
          throwError "boundary_comparison_unpaired_fresh_delayed_fvar"
        for h : ordinal in *...stockEntry.status.fvars.size do
          let stockFVar := stockEntry.status.fvars[ordinal]
          let appliedFVar := appliedEntry.status.fvars[ordinal]!
          unless stockFVar.isFVar && appliedFVar.isFVar do
            throwError "boundary_comparison_unpaired_fresh_delayed_fvar"
          mapping ← pairFVarIds basis mapping appliedFVar.fvarId!
            stockFVar.fvarId! s!"exprMVars.delayed.fvar[{ordinal}]"
  pairBoundaryLevelAssignments basis mapping stock applied

private def mapBoundaryLevel (mapping : BoundaryIdMap) : Level → MetaM Level
  | .zero => pure .zero
  | .param name => pure (.param name)
  | .succ level => return .succ (← mapBoundaryLevel mapping level)
  | .max lhs rhs => return .max (← mapBoundaryLevel mapping lhs) (← mapBoundaryLevel mapping rhs)
  | .imax lhs rhs => return .imax (← mapBoundaryLevel mapping lhs) (← mapBoundaryLevel mapping rhs)
  | .mvar id =>
      match findPairByApplied? mapping.lmvars id with
      | some mapped => pure (.mvar mapped)
      | none => throwError "boundary_comparison_unpaired_fresh_universe_mvar"

private def mapBoundaryExpr (mapping : BoundaryIdMap) (label : String)
    (expression : Expr) : MetaM Expr :=
  Core.transform expression (pre := fun subexpression => do
    match subexpression with
    | .fvar id =>
        let some mapped := findPairByApplied? mapping.fvars id
          | throwError s!"boundary_comparison_unpaired_fresh_fvar:{label}:id={id.name}"
        return .done (.fvar mapped)
    | .mvar id =>
        let some mapped := findPairByApplied? mapping.mvars id
          | throwError "boundary_comparison_unpaired_fresh_expression_mvar"
        return .done (.mvar mapped)
    | .sort level =>
        return .done (.sort (← mapBoundaryLevel mapping level))
    | .const name levels =>
        return .done (.const name (← levels.mapM (mapBoundaryLevel mapping)))
    | _ => return .continue)

private def compareBoundaryExpr (mapping : BoundaryIdMap) (label : String)
    (lctx : LocalContext) (localInstances : LocalInstances)
    (stock applied : Expr) : TacticM Unit := do
  let applied ← mapBoundaryExpr mapping label applied
  let equal ← withRestoredBoundaryFullMetaState do
    withLCtx lctx localInstances do
      withNewMCtxDepth <| isDefEqGuarded stock applied
  unless equal do
    throwError s!"boundary_comparison_mismatch:{label}:stockHash={stock.hash}:appliedHash={applied.hash}"

private def compareBoundaryLevel (mapping : BoundaryIdMap) (label : String)
    (stock applied : Level) : TacticM Unit := do
  let applied ← mapBoundaryLevel mapping applied
  let stock := Expr.sort stock
  let applied := Expr.sort applied
  let equal ← withRestoredBoundaryFullMetaState do
    withNewMCtxDepth <| isDefEqGuarded stock applied
  unless equal do
    throwError s!"boundary_comparison_mismatch:{label}:stockHash={stock.hash}:appliedHash={applied.hash}"

private def compareBoundaryLocalContext (mapping : BoundaryIdMap)
    (stock applied : LocalContext) (localInstances : LocalInstances)
    (label : String) : TacticM Unit := do
  let stockDecls := boundaryLocalDecls stock
  let appliedDecls := boundaryLocalDecls applied
  unless stockDecls.size == appliedDecls.size do
    boundaryComparisonMismatch s!"{label}.count"
  for h : ordinal in *...stockDecls.size do
    let stockDecl := stockDecls[ordinal]
    let appliedDecl := appliedDecls[ordinal]!
    let some mappedFVar := findPairByApplied? mapping.fvars appliedDecl.fvarId
      | throwError s!"boundary_comparison_unpaired_fresh_fvar:{label}[{ordinal}]:id={appliedDecl.fvarId.name}"
    unless mappedFVar == stockDecl.fvarId do
      boundaryComparisonMismatch s!"{label}[{ordinal}].fvar"
    compareBoundaryLocalDeclShape s!"{label}[{ordinal}]" stockDecl appliedDecl
    compareBoundaryExpr mapping s!"{label}[{ordinal}].type" stock localInstances
      stockDecl.type appliedDecl.type
    match stockDecl, appliedDecl with
    | .cdecl .., .cdecl .. => pure ()
    | .ldecl _ _ _ _ stockValue _ _, .ldecl _ _ _ _ appliedValue _ _ =>
        compareBoundaryExpr mapping s!"{label}[{ordinal}].value" stock localInstances
          stockValue appliedValue
    | _, _ => pure ()

private def compareBoundaryLocalInstances (mapping : BoundaryIdMap)
    (stock applied : LocalInstances) (label : String) : TacticM Unit := do
  unless stock.size == applied.size do boundaryComparisonMismatch s!"{label}.count"
  for h : ordinal in *...stock.size do
    let stockInstance := stock[ordinal]
    let appliedInstance := applied[ordinal]!
    unless stockInstance.className == appliedInstance.className do
      boundaryComparisonMismatch s!"{label}[{ordinal}].class"
    unless stockInstance.fvar.isFVar && appliedInstance.fvar.isFVar do
      throwError "boundary_comparison_unpaired_local_instance"
    let some mappedFVar := findPairByApplied? mapping.fvars appliedInstance.fvar.fvarId!
      | throwError "boundary_comparison_unpaired_fvar"
    unless mappedFVar == stockInstance.fvar.fvarId! do
      boundaryComparisonMismatch s!"{label}[{ordinal}].fvar"

private def boundaryMacroStackEq : MacroStack → MacroStack → Bool
  | [], [] => true
  | stock :: stocks, applied :: applieds =>
      stock.before == applied.before && stock.after == applied.after &&
        boundaryMacroStackEq stocks applieds
  | _, _ => false

private def boundarySavedContextEq
    (stock applied : Term.SavedContext) : Bool :=
  stock.declName? == applied.declName? &&
    stock.options == applied.options &&
    stock.openDecls == applied.openDecls &&
    boundaryMacroStackEq stock.macroStack applied.macroStack &&
    stock.errToSorry == applied.errToSorry &&
    stock.levelNames == applied.levelNames &&
    stock.fixedTermElabs.isEmpty && applied.fixedTermElabs.isEmpty

private def rejectBoundaryUnsupportedSavedContext
    (context : Term.SavedContext) : TacticM Unit := do
  unless context.fixedTermElabs.isEmpty do
    throwError "boundary_comparison_unsupported_fixed_term_elabs"

private def rejectBoundaryUnsupportedSyntheticDecl
    (decl : Term.SyntheticMVarDecl) : TacticM Unit := do
  match decl.kind with
  | .typeClass _ => pure ()
  | .tactic _ context _ _ => rejectBoundaryUnsupportedSavedContext context
  | .postponed context => rejectBoundaryUnsupportedSavedContext context
  -- The coercion continuation carries expressions and an optional function.
  -- Until those are paired through BoundaryIdMap, reject it explicitly.
  | .coe .. => throwError "boundary_comparison_unsupported_synthetic_coe"

private def boundaryTacticMVarKindEq
    (stock applied : Term.TacticMVarKind) : Bool :=
  match stock, applied with
  | .term, .term => true
  | .autoParam stockName, .autoParam appliedName => stockName == appliedName
  | .fieldAutoParam stockField stockStruct, .fieldAutoParam appliedField appliedStruct =>
      stockField == appliedField && stockStruct == appliedStruct
  | _, _ => false

private def boundarySyntheticDeclEq
    (stock applied : Term.SyntheticMVarDecl) : Bool :=
  match stock.kind, applied.kind with
  | .typeClass _, .typeClass _ => stock.stx == applied.stx
  | .tactic stockStx stockContext stockKind stockDelay,
      .tactic appliedStx appliedContext appliedKind appliedDelay =>
      stock.stx == applied.stx && stockStx == appliedStx &&
        boundaryTacticMVarKindEq stockKind appliedKind &&
        stockDelay == appliedDelay &&
        boundarySavedContextEq stockContext appliedContext
  | .postponed stockContext, .postponed appliedContext =>
      stock.stx == applied.stx && boundarySavedContextEq stockContext appliedContext
  | .coe .., .coe .. => false
  | _, _ => false

private structure BoundaryProofDependencies where
  mvars : Array MVarId := #[]
  lmvars : Array LMVarId := #[]

private def canonicalBoundaryProofMVar (mapping : BoundaryIdMap)
    (appliedSide : Bool) (id : MVarId) : TacticM MVarId := do
  if appliedSide then
    let some mapped := findPairByApplied? mapping.mvars id
      | throwError "boundary_comparison_unpaired_proof_dependency"
    return mapped
  unless findPairByStock? mapping.mvars id |>.isSome do
    throwError "boundary_comparison_unpaired_proof_dependency"
  return id

private def canonicalBoundaryProofLMVar (mapping : BoundaryIdMap)
    (appliedSide : Bool) (id : LMVarId) : TacticM LMVarId := do
  if appliedSide then
    let some mapped := findPairByApplied? mapping.lmvars id
      | throwError "boundary_comparison_unpaired_proof_universe_dependency"
    return mapped
  unless findPairByStock? mapping.lmvars id |>.isSome do
    throwError "boundary_comparison_unpaired_proof_universe_dependency"
  return id

private def boundaryProofFVarMapped (mapping : BoundaryIdMap)
    (appliedSide : Bool) (id : FVarId) : Bool :=
  if appliedSide then
    findPairByApplied? mapping.fvars id |>.isSome
  else
    findPairByStock? mapping.fvars id |>.isSome

mutual

private partial def collectBoundaryProofExprDependencies
    (mapping : BoundaryIdMap) (snapshot : BoundarySnapshot)
    (appliedSide : Bool) (expression : Expr)
    (dependencies : BoundaryProofDependencies)
    (visited active : Array MVarId) :
    TacticM (BoundaryProofDependencies × Array MVarId) := do
  let mut dependencies := dependencies
  for id in (collectLevelMVars {} expression).result do
    let id ← canonicalBoundaryProofLMVar mapping appliedSide id
    unless dependencies.lmvars.contains id do
      dependencies := { dependencies with lmvars := dependencies.lmvars.push id }
  let mut visited := visited
  for id in (expression.collectMVars {}).result do
    let (dependencies', visited') ← collectBoundaryProofMVarDependencies
      mapping snapshot appliedSide id dependencies visited active
    dependencies := dependencies'
    visited := visited'
  return (dependencies, visited)

private partial def collectBoundaryProofMVarDependencies
    (mapping : BoundaryIdMap) (snapshot : BoundarySnapshot)
    (appliedSide : Bool) (id : MVarId)
    (dependencies : BoundaryProofDependencies)
    (visited active : Array MVarId) :
    TacticM (BoundaryProofDependencies × Array MVarId) := do
  if active.contains id then
    throwError "boundary_comparison_proof_dependency_cycle"
  if visited.contains id then
    return (dependencies, visited)
  let some entry := findExprMVarSnapshot? snapshot id
    | throwError "boundary_comparison_unpaired_proof_dependency"
  let visited := visited.push id
  let active := active.push id
  if entry.status.tag == boundaryExprAssigned then
    let some value := entry.status.valueOpt
      | throwError "boundary_comparison_unpaired_proof_dependency"
    collectBoundaryProofExprDependencies mapping snapshot appliedSide value
      dependencies visited active
  else if entry.status.tag == boundaryExprDelayed then
    let some pending := entry.status.pendingOpt
      | throwError "boundary_comparison_unpaired_proof_dependency"
    for fvar in entry.status.fvars do
      unless fvar.isFVar &&
          boundaryProofFVarMapped mapping appliedSide fvar.fvarId! do
        throwError "boundary_comparison_unpaired_proof_fvar_dependency"
    collectBoundaryProofMVarDependencies mapping snapshot appliedSide pending
      dependencies visited active
  else
    let canonical ← canonicalBoundaryProofMVar mapping appliedSide id
    let dependencies := if dependencies.mvars.contains canonical then dependencies else
      { dependencies with mvars := dependencies.mvars.push canonical }
    return (dependencies, visited)

end

private def compareBoundaryProofDependencies (mapping : BoundaryIdMap)
    (stockSnapshot appliedSnapshot : BoundarySnapshot)
    (label : String) (stock applied : Expr) : TacticM Unit := do
  let (stockDependencies, _) ← collectBoundaryProofExprDependencies
    mapping stockSnapshot false stock {} #[] #[]
  let (appliedDependencies, _) ← collectBoundaryProofExprDependencies
    mapping appliedSnapshot true applied {} #[] #[]
  unless stockDependencies.mvars.size == appliedDependencies.mvars.size &&
      stockDependencies.mvars.all (fun id => appliedDependencies.mvars.contains id) do
    boundaryComparisonMismatch s!"{label}.proofMVars"
  unless stockDependencies.lmvars.size == appliedDependencies.lmvars.size &&
      stockDependencies.lmvars.all (fun id => appliedDependencies.lmvars.contains id) do
    boundaryComparisonMismatch s!"{label}.proofLMVars"

private def compareBoundaryMVarStatus (mapping : BoundaryIdMap)
    (stockSnapshot appliedSnapshot : BoundarySnapshot)
    (label : String) (stock applied : BoundaryExprMVarStatus)
    (lctx : LocalContext) (localInstances : LocalInstances) : TacticM Unit := do
  unless stock.tag == applied.tag do boundaryComparisonMismatch s!"{label}.status"
  unless stock.isProof == applied.isProof do
    boundaryComparisonMismatch s!"{label}.proofStatus"
  if stock.tag == boundaryExprAssigned then
    let some stockValue := stock.valueOpt
      | boundaryComparisonMismatch s!"{label}.stockValue"
    let some appliedValue := applied.valueOpt
      | boundaryComparisonMismatch s!"{label}.appliedValue"
    if stock.isProof then
      compareBoundaryProofDependencies mapping stockSnapshot appliedSnapshot
        label stockValue appliedValue
    else
      compareBoundaryExpr mapping label lctx localInstances stockValue appliedValue
  else if stock.tag == boundaryExprDelayed then
    let some stockPending := stock.pendingOpt
      | boundaryComparisonMismatch s!"{label}.stockPending"
    let some appliedPending := applied.pendingOpt
      | boundaryComparisonMismatch s!"{label}.appliedPending"
    let some mappedPending := findPairByApplied? mapping.mvars appliedPending
      | throwError "boundary_comparison_unpaired_fresh_delayed_mvar"
    unless mappedPending == stockPending do
      boundaryComparisonMismatch s!"{label}.pending"
    unless stock.fvars.size == applied.fvars.size do
      throwError "boundary_comparison_unpaired_fresh_delayed_fvar"
    for h : ordinal in *...stock.fvars.size do
      let stockFVar := stock.fvars[ordinal]
      let appliedFVar := applied.fvars[ordinal]!
      unless stockFVar.isFVar && appliedFVar.isFVar do
        throwError "boundary_comparison_unpaired_fresh_delayed_fvar"
      let some mappedFVar := findPairByApplied? mapping.fvars appliedFVar.fvarId!
        | throwError "boundary_comparison_unpaired_fresh_delayed_fvar"
      unless mappedFVar == stockFVar.fvarId! do
        boundaryComparisonMismatch s!"{label}.fvars"

private def compareBoundaryMVarNode (mapping : BoundaryIdMap)
    (stockSnapshot appliedSnapshot : BoundarySnapshot)
    (stock applied : BoundaryExprMVarSnapshot) (label : String) : TacticM Unit := do
  unless stock.decl.userName == applied.decl.userName do
    boundaryComparisonMismatch s!"{label}.userName"
  unless boundaryMetavarKindEq stock.decl.kind applied.decl.kind do
    boundaryComparisonMismatch s!"{label}.kind"
  unless stock.decl.depth == applied.decl.depth do
    boundaryComparisonMismatch s!"{label}.depth"
  unless stock.decl.numScopeArgs == applied.decl.numScopeArgs do
    boundaryComparisonMismatch s!"{label}.numScopeArgs"
  compareBoundaryLocalContext mapping stock.decl.lctx applied.decl.lctx
    stock.decl.localInstances
    s!"{label}.lctx"
  compareBoundaryLocalInstances mapping stock.decl.localInstances applied.decl.localInstances
    s!"{label}.localInstances"
  compareBoundaryExpr mapping s!"{label}.type" stock.decl.lctx stock.decl.localInstances
    stock.decl.type applied.decl.type
  compareBoundaryMVarStatus mapping stockSnapshot appliedSnapshot
    s!"{label}.assignment" stock.status applied.status stock.decl.lctx
    stock.decl.localInstances

private def compareBoundarySyntheticEntries (stock applied : BoundarySyntheticEntry)
    (label : String) : TacticM Unit := do
  rejectBoundaryUnsupportedSyntheticDecl stock.decl
  rejectBoundaryUnsupportedSyntheticDecl applied.decl
  unless stock.pending == applied.pending do boundaryComparisonMismatch s!"{label}.pending"
  unless stock.assigned == applied.assigned do boundaryComparisonMismatch s!"{label}.assigned"
  unless stock.delayed == applied.delayed do boundaryComparisonMismatch s!"{label}.delayed"
  unless boundarySyntheticDeclEq stock.decl applied.decl do
    boundaryComparisonMismatch s!"{label}.decl"

private def compareBoundarySyntheticState (basis : PreBoundaryBasis)
    (mapping : BoundaryIdMap) (stock applied : BoundarySnapshot) : TacticM Unit := do
  for (preId, preDecl) in basis.syntheticMVars do
    rejectBoundaryUnsupportedSyntheticDecl preDecl
    let stockEntry? := findSyntheticSnapshot? stock preId
    let appliedEntry? := findSyntheticSnapshot? applied preId
    match stockEntry?, appliedEntry? with
    | none, none => boundaryComparisonMismatch "pendingSynthetic.synthetic.presence"
    | some stockEntry, some appliedEntry =>
        compareBoundarySyntheticEntries stockEntry appliedEntry
          s!"pendingSynthetic.synthetic[{preId.name}]"
        unless boundarySyntheticDeclEq preDecl stockEntry.decl do
          boundaryComparisonMismatch "pendingSynthetic.synthetic.decl"
        unless boundarySyntheticDeclEq preDecl appliedEntry.decl do
          boundaryComparisonMismatch "pendingSynthetic.synthetic.decl"
    | _, _ => boundaryComparisonMismatch "pendingSynthetic.synthetic.presence"
  for stockEntry in stock.pendingSynthetic.synthetic do
    unless basis.syntheticMVars.any (fun pre => pre.1 == stockEntry.id) do
      let some appliedId := findPairByStock? mapping.mvars stockEntry.id
        | throwError "boundary_comparison_unpaired_fresh_synthetic"
      let some appliedEntry := findSyntheticSnapshot? applied appliedId
        | boundaryComparisonMismatch "pendingSynthetic.synthetic.fresh.presence"
      compareBoundarySyntheticEntries stockEntry appliedEntry
        "pendingSynthetic.synthetic.fresh"
      unless stock.pendingSynthetic.pending.contains stockEntry.id ||
          stock.goals.any (fun goal => goal.id == stockEntry.id) do
        throwError "boundary_comparison_unpaired_fresh_synthetic"
  for appliedEntry in applied.pendingSynthetic.synthetic do
    unless basis.syntheticMVars.any (fun pre => pre.1 == appliedEntry.id) do
      let some stockId := findPairByApplied? mapping.mvars appliedEntry.id
        | throwError "boundary_comparison_unpaired_fresh_synthetic"
      let some stockEntry := findSyntheticSnapshot? stock stockId
        | boundaryComparisonMismatch "pendingSynthetic.synthetic.fresh.presence"
      compareBoundarySyntheticEntries stockEntry appliedEntry
        "pendingSynthetic.synthetic.fresh"
      unless applied.pendingSynthetic.pending.contains appliedEntry.id ||
          applied.goals.any (fun goal => goal.id == appliedEntry.id) do
        throwError "boundary_comparison_unpaired_fresh_synthetic"
  unless stock.pendingSynthetic.pending.size == applied.pendingSynthetic.pending.size do
    boundaryComparisonMismatch "pendingSynthetic.pending.count"
  for h : ordinal in *...stock.pendingSynthetic.pending.size do
    let stockId := stock.pendingSynthetic.pending[ordinal]
    let appliedId := applied.pendingSynthetic.pending[ordinal]!
    let some mapped := findPairByApplied? mapping.mvars appliedId
      | throwError "boundary_comparison_unpaired_fresh_pending"
    unless mapped == stockId do
      boundaryComparisonMismatch s!"pendingSynthetic.pending[{ordinal}]"

private def compareBoundaryZeta (mapping : BoundaryIdMap)
    (stock applied : Array FVarId) : TacticM Unit := do
  let mut appliedMapped : Array FVarId := #[]
  for id in applied do
    let some mapped := findPairByApplied? mapping.fvars id
      | throwError s!"boundary_comparison_unpaired_fresh_fvar:zetaDeltaFVarIds:id={id.name}"
    unless appliedMapped.contains mapped do
      appliedMapped := appliedMapped.push mapped
  for id in stock do
    unless appliedMapped.contains id do
      boundaryComparisonMismatch "zetaDeltaFVarIds"
  let mut stockUnique : Array FVarId := #[]
  for id in stock do
    unless stockUnique.contains id do
      stockUnique := stockUnique.push id
  unless appliedMapped.size == stockUnique.size do
    boundaryComparisonMismatch "zetaDeltaFVarIds.count"

private def compareBoundaryLetRecs
    (basis : PreBoundaryBasis) (stock applied : List Term.LetRecToLift) : TacticM Unit := do
  -- Entries can already exist while tactics in a `where` body are pending.
  -- Supporting these requires no new effect: both trials must retain every
  -- field exactly from the common pre-state, including list order. Any fresh
  -- or changed pending recursion still needs an explicit future capability.
  unless boundaryExistingLetRecsEq basis.letRecsToLift stock &&
      boundaryExistingLetRecsEq basis.letRecsToLift applied do
    throwError "boundary_comparison_unsupported_letrec_state"

private def compareBoundaryLevelMVarStates (mapping : BoundaryIdMap)
    (stock applied : BoundarySnapshot) : TacticM Unit := do
  for (appliedId, stockId) in mapping.lmvars do
    let some stockEntry := findLevelMVarSnapshot? stock stockId
      | throwError "boundary_comparison_unpaired_mapped_universe_mvar"
    let some appliedEntry := findLevelMVarSnapshot? applied appliedId
      | throwError "boundary_comparison_unpaired_mapped_universe_mvar"
    unless stockEntry.decl.depth == appliedEntry.decl.depth do
      boundaryComparisonMismatch s!"levelMVars[{stockId.name}].depth"
    unless stockEntry.status.tag == appliedEntry.status.tag do
      boundaryComparisonMismatch s!"levelMVars[{stockId.name}].status"
    if stockEntry.status.tag == boundaryLevelAssigned then
      let some stockLevel := stockEntry.status.valueOpt
        | boundaryComparisonMismatch s!"levelMVars[{stockId.name}].stockValue"
      let some appliedLevel := appliedEntry.status.valueOpt
        | boundaryComparisonMismatch s!"levelMVars[{stockId.name}].appliedValue"
      compareBoundaryLevel mapping s!"levelMVars[{stockId.name}].value"
        stockLevel appliedLevel

private def compareBoundarySnapshot (basis : PreBoundaryBasis)
    (mapping : BoundaryIdMap) (stock applied : BoundarySnapshot) : TacticM Unit := do
  unless stock.auxDeclNGen.namePrefix == applied.auxDeclNGen.namePrefix &&
      stock.auxDeclNGen.idx == applied.auxDeclNGen.idx &&
      stock.auxDeclNGen.parentIdxs == applied.auxDeclNGen.parentIdxs do
    boundaryComparisonMismatch s!"core.auxDeclNGen: stock={stock.auxDeclNGen.namePrefix}/{stock.auxDeclNGen.idx}/{stock.auxDeclNGen.parentIdxs}; applied={applied.auxDeclNGen.namePrefix}/{applied.auxDeclNGen.idx}/{applied.auxDeclNGen.parentIdxs}"
  unless stock.options == applied.options do boundaryComparisonMismatch "options"
  unless stock.mctxDepth == applied.mctxDepth do boundaryComparisonMismatch "mctx.depth"
  unless stock.levelAssignDepth == applied.levelAssignDepth do
    boundaryComparisonMismatch "mctx.levelAssignDepth"
  unless stock.levelNames == applied.levelNames do boundaryComparisonMismatch "term.levelNames"
  compareBoundaryLetRecs basis stock.letRecsToLift applied.letRecsToLift
  compareBoundaryZeta mapping stock.zetaDeltaFVarIds applied.zetaDeltaFVarIds
  unless stock.mctxUserNames.size == applied.mctxUserNames.size do
    boundaryComparisonMismatch "mctx.userNames.count"
  for h : ordinal in *...stock.mctxUserNames.size do
    let stockEntry := stock.mctxUserNames[ordinal]
    let appliedEntry := applied.mctxUserNames[ordinal]!
    unless stockEntry.1 == appliedEntry.1 do
      boundaryComparisonMismatch s!"mctx.userNames[{ordinal}].name"
    let some mapped := findPairByApplied? mapping.mvars appliedEntry.2
      | throwError "boundary_comparison_unpaired_fresh_user_name_mvar"
    unless mapped == stockEntry.2 do
      boundaryComparisonMismatch s!"mctx.userNames[{ordinal}].mvar"
  unless stock.mvarErrorInfoRoots.size == applied.mvarErrorInfoRoots.size do
    boundaryComparisonMismatch "mvarErrorInfos.count"
  for h : ordinal in *...stock.mvarErrorInfoRoots.size do
    let stockRoot := stock.mvarErrorInfoRoots[ordinal]
    let appliedRoot := applied.mvarErrorInfoRoots[ordinal]!
    let some mapped := findPairByApplied? mapping.mvars appliedRoot
      | throwError "boundary_comparison_unpaired_fresh_mvar_error_info"
    unless mapped == stockRoot do
      boundaryComparisonMismatch s!"mvarErrorInfos[{ordinal}]"
  unless stock.levelMVarErrorInfoDeps.size == applied.levelMVarErrorInfoDeps.size do
    boundaryComparisonMismatch "levelMVarErrorInfos.count"
  for h : entryOrdinal in *...stock.levelMVarErrorInfoDeps.size do
    let stockDeps := stock.levelMVarErrorInfoDeps[entryOrdinal]
    let appliedDeps := applied.levelMVarErrorInfoDeps[entryOrdinal]!
    unless stockDeps.size == appliedDeps.size do
      boundaryComparisonMismatch s!"levelMVarErrorInfos[{entryOrdinal}].count"
    for h : ordinal in *...stockDeps.size do
      let appliedLevel := appliedDeps[ordinal]!
      let some mapped := findPairByApplied? mapping.lmvars appliedLevel
          | throwError "boundary_comparison_unpaired_fresh_universe_mvar"
      unless mapped == stockDeps[ordinal] do
        boundaryComparisonMismatch s!"levelMVarErrorInfos[{entryOrdinal}][{ordinal}]"
  unless stock.goals.size == applied.goals.size do boundaryComparisonMismatch "goals.count"
  for h : ordinal in *...stock.goals.size do
    let stockGoal := stock.goals[ordinal]
    let appliedGoal := applied.goals[ordinal]!
    unless stockGoal.decl.userName == appliedGoal.decl.userName do
      boundaryComparisonMismatch s!"goals[{ordinal}].userName"
    unless boundaryMetavarKindEq stockGoal.decl.kind appliedGoal.decl.kind do
      boundaryComparisonMismatch s!"goals[{ordinal}].kind"
    unless stockGoal.decl.depth == appliedGoal.decl.depth do
      boundaryComparisonMismatch s!"goals[{ordinal}].depth"
    unless stockGoal.decl.numScopeArgs == appliedGoal.decl.numScopeArgs do
      boundaryComparisonMismatch s!"goals[{ordinal}].numScopeArgs"
    compareBoundaryLocalContext mapping stockGoal.decl.lctx appliedGoal.decl.lctx
      stockGoal.decl.localInstances
      s!"goals[{ordinal}].locals"
    compareBoundaryLocalInstances mapping stockGoal.decl.localInstances
      appliedGoal.decl.localInstances s!"goals[{ordinal}].localInstances"
    compareBoundaryExpr mapping s!"goals[{ordinal}].target" stockGoal.decl.lctx
      stockGoal.decl.localInstances stockGoal.decl.type appliedGoal.decl.type
  for h : ordinal in *...mapping.mvars.size do
    let pair := mapping.mvars[ordinal]
    let some stockEntry := findExprMVarSnapshot? stock pair.2
      | throwError "boundary_comparison_unpaired_mapped_mvar"
    let some appliedEntry := findExprMVarSnapshot? applied pair.1
      | throwError "boundary_comparison_unpaired_mapped_mvar"
    compareBoundaryMVarNode mapping stock applied stockEntry appliedEntry
      s!"exprMVars.mapped[{ordinal}]"
  compareBoundaryLevelMVarStates mapping stock applied
  compareBoundarySyntheticState basis mapping stock applied
  unless stock.postponed.size == applied.postponed.size do
    boundaryComparisonMismatch "postponed.count"
  for h : ordinal in *...stock.postponed.size do
    let stockEntry := stock.postponed[ordinal]
    let appliedEntry := applied.postponed[ordinal]!
    compareBoundaryLevel mapping s!"postponed[{ordinal}].lhs"
      stockEntry.lhs appliedEntry.lhs
    compareBoundaryLevel mapping s!"postponed[{ordinal}].rhs"
      stockEntry.rhs appliedEntry.rhs
    match stockEntry.context?, appliedEntry.context? with
    | none, none => pure ()
    | some stockContext, some appliedContext =>
        unless stockContext.localInstanceShape == appliedContext.localInstanceShape do
          boundaryComparisonMismatch s!"postponed[{ordinal}].context.localInstances"
        compareBoundaryLocalInstances mapping stockContext.localInstances
          appliedContext.localInstances s!"postponed[{ordinal}].context.localInstances"
        compareBoundaryLocalContext mapping stockContext.lctx appliedContext.lctx
          stockContext.localInstances
          s!"postponed[{ordinal}].context.locals"
        compareBoundaryExpr mapping s!"postponed[{ordinal}].context.lhs"
          stockContext.lctx stockContext.localInstances stockContext.lhs appliedContext.lhs
        compareBoundaryExpr mapping s!"postponed[{ordinal}].context.rhs"
          stockContext.lctx stockContext.localInstances stockContext.rhs appliedContext.rhs
    | _, _ => boundaryComparisonMismatch s!"postponed[{ordinal}].context.presence"

private def compareBoundaryStates (basis : PreBoundaryBasis)
    (stockState appliedState : Tactic.SavedState)
    (stock applied : BoundarySnapshot) : TacticM Unit := do
  try
    let mapping ← buildBoundaryIdMap basis stock applied
    stockState.restore
    compareBoundarySnapshot basis mapping stock applied
  finally
    appliedState.restore

private def runBoundaryComparatorSelfTest : TacticM Unit := do
  let outerState ← Tactic.saveState
  try
    let parentGoal ← getMainGoal
    let mkTestGoal (target : Expr) : TacticM MVarId :=
      parentGoal.withContext do
        return (← mkFreshExprSyntheticOpaqueMVar target).mvarId!
    let proofDependency ← mkTestGoal (mkConst ``True)
    let testBaseState ← Tactic.saveState
    -- Model a cached assignment to a local whose context has already ended.
    -- Such assignments occur before the simp boundary in Mathlib's Action.End.
    -- The unchanged cache must compare equal, but a new escaped ID must fail.
    let cachedMVar ← mkTestGoal (mkConst ``Nat)
    let cachedFVar ← mkFreshFVarId
    modifyMCtx fun mctx =>
      { mctx with eAssignment := mctx.eAssignment.insert cachedMVar (.fvar cachedFVar) }
    let cachedBasis ← mkPreBoundaryBasis
    unless cachedBasis.fvarIds.contains cachedFVar do
      throwError "boundary_comparator_self_test_cached_fvar_missing"
    let cachedStock ← boundarySnapshot cachedBasis
    let cachedStockState ← Tactic.saveState
    compareBoundaryStates cachedBasis cachedStockState cachedStockState cachedStock cachedStock
    let changedCachedFVar ← mkFreshFVarId
    modifyMCtx fun mctx =>
      { mctx with eAssignment := mctx.eAssignment.insert cachedMVar (.fvar changedCachedFVar) }
    let cachedApplied ← boundarySnapshot cachedBasis
    let cachedAppliedState ← Tactic.saveState
    let cachedRejected ← try
      compareBoundaryStates cachedBasis cachedStockState cachedAppliedState cachedStock cachedApplied
      pure false
    catch error =>
      unless (← error.toMessageData.toString).contains "boundary_comparison_unpaired_fresh_fvar:" do
        throw error
      pure true
    unless cachedRejected do
      throwError "boundary_comparator_self_test_changed_cached_fvar_accepted"
    testBaseState.restore
    let basis ← mkPreBoundaryBasis
    let stockGoal ← mkTestGoal (mkConst ``True)
    setGoals [stockGoal]
    let stock ← boundarySnapshot basis
    let stockState ← Tactic.saveState
    if let some entry := basis.letRecsToLift.head? then
      let changes := #[
        ("deleted", []),
        ("body", [{entry with val := .lam `n (mkConst ``Nat) (mkNatLit 123) .default}]),
        ("fresh", {entry with declName := entry.declName.str "fresh"} :: basis.letRecsToLift)]
      for (label, entries) in changes do
        -- Equal mutations on both sides must still fail against the original
        -- pre-state. This tests the actual complete comparator, not only the
        -- exported field equality helper.
        let changed := {stock with letRecsToLift := entries}
        let rejected ← try
          compareBoundaryStates basis stockState stockState changed changed
          pure false
        catch error =>
          unless (← error.toMessageData.toString).contains
              "boundary_comparison_unsupported_letrec_state" do throw error
          pure true
        unless rejected do
          throwError "boundary_comparator_self_test_letrec_{label}_accepted"
      IO.println "LETREC_COMPARATOR_CONTROLS deleted=true body=true fresh=true commonPreRequired=true"
      -- The remaining synthetic proof-mvar scenarios assume no unrelated
      -- pending recursive bodies. This branch tests the real retained list;
      -- the outer finally restores the caller before returning.
      return
    testBaseState.restore
    let positiveTarget : Expr :=
      .letE `P (mkSort .zero) (mkConst ``True) (.bvar 0) false
    let positiveGoal ← mkTestGoal positiveTarget
    setGoals [positiveGoal]
    let positive ← boundarySnapshot basis
    let positiveState ← Tactic.saveState
    compareBoundaryStates basis stockState positiveState stock positive
    unless (← getGoals) == [positiveGoal] do
      throwError "boundary_comparator_self_test_positive_restore_failed"
    testBaseState.restore
    let stockFreshLevel ← mkFreshLevelMVar
    let stockFreshGoal ← mkTestGoal (.sort stockFreshLevel)
    setGoals [stockFreshGoal]
    let freshStock ← boundarySnapshot basis
    let freshStockState ← Tactic.saveState
    testBaseState.restore
    let _unusedFreshLevel ← mkFreshLevelMVar
    let appliedFreshLevel ← mkFreshLevelMVar
    let appliedFreshGoal ← mkTestGoal (.sort appliedFreshLevel)
    setGoals [appliedFreshGoal]
    let freshApplied ← boundarySnapshot basis
    let freshAppliedState ← Tactic.saveState
    unless stockFreshLevel != appliedFreshLevel do
      throwError "boundary_comparator_self_test_fresh_universe_not_alpha_renamed"
    compareBoundaryStates basis freshStockState freshAppliedState freshStock freshApplied
    unless (← getGoals) == [appliedFreshGoal] do
      throwError "boundary_comparator_self_test_fresh_universe_restore_failed"
    testBaseState.restore
    let statusStockLevel ← mkFreshLevelMVar
    let statusStockGoal ← mkTestGoal (.sort statusStockLevel)
    setGoals [statusStockGoal]
    let statusStock ← boundarySnapshot basis
    let statusStockState ← Tactic.saveState
    testBaseState.restore
    let _unusedStatusLevel ← mkFreshLevelMVar
    let statusAppliedLevel ← mkFreshLevelMVar
    assignLevelMVar statusAppliedLevel.mvarId! .zero
    let statusAppliedGoal ← mkTestGoal (.sort statusAppliedLevel)
    setGoals [statusAppliedGoal]
    let statusApplied ← boundarySnapshot basis
    let statusAppliedState ← Tactic.saveState
    let statusRejected ← try
      compareBoundaryStates basis statusStockState statusAppliedState statusStock statusApplied
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      unless message.contains "boundary_comparison_mismatch:levelMVars" &&
          message.contains ".status" do
        throw error
      unless (← getGoals) == [statusAppliedGoal] do
        throwError "boundary_comparator_self_test_fresh_status_restore_failed"
      pure true
    unless statusRejected do
      throwError "boundary_comparator_self_test_fresh_status_accepted"
    testBaseState.restore
    let depthStockLevel ← mkFreshLevelMVar
    let depthStockGoal ← mkTestGoal (.sort depthStockLevel)
    setGoals [depthStockGoal]
    let depthStock ← boundarySnapshot basis
    let depthStockState ← Tactic.saveState
    testBaseState.restore
    let _unusedDepthLevel ← mkFreshLevelMVar
    let depthAppliedLevel ← mkFreshLevelMVar
    let depthAppliedId := depthAppliedLevel.mvarId!
    let depthDecl := (← getMCtx).getLevelDecl depthAppliedId
    let depthChangedDecl := { depthDecl with depth := depthDecl.depth + 1 }
    modifyMCtx fun mctx =>
      { mctx with lDecls := mctx.lDecls.insert depthAppliedId depthChangedDecl }
    let depthAppliedGoal ← mkTestGoal (.sort depthAppliedLevel)
    setGoals [depthAppliedGoal]
    let depthApplied ← boundarySnapshot basis
    let depthAppliedState ← Tactic.saveState
    let depthRejected ← try
      compareBoundaryStates basis depthStockState depthAppliedState depthStock depthApplied
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      unless message.contains "boundary_comparison_mismatch:levelMVars" &&
          message.contains ".depth" do
        throw error
      unless (← getGoals) == [depthAppliedGoal] do
        throwError "boundary_comparator_self_test_fresh_depth_restore_failed"
      pure true
    unless depthRejected do
      throwError "boundary_comparator_self_test_fresh_depth_accepted"
    testBaseState.restore
    let shareStockLevel1 ← mkFreshLevelMVar
    let shareStockLevel2 ← mkFreshLevelMVar
    let shareStockGoal1 ← mkTestGoal (.sort shareStockLevel1)
    let shareStockGoal2 ← mkTestGoal (.sort shareStockLevel2)
    setGoals [shareStockGoal1, shareStockGoal2]
    let shareStock ← boundarySnapshot basis
    let shareStockState ← Tactic.saveState
    testBaseState.restore
    let _unusedShareLevel ← mkFreshLevelMVar
    let shareAppliedLevel ← mkFreshLevelMVar
    let shareAppliedGoal1 ← mkTestGoal (.sort shareAppliedLevel)
    let shareAppliedGoal2 ← mkTestGoal (.sort shareAppliedLevel)
    setGoals [shareAppliedGoal1, shareAppliedGoal2]
    let shareApplied ← boundarySnapshot basis
    let shareAppliedState ← Tactic.saveState
    let shareRejected ← try
      compareBoundaryStates basis shareStockState shareAppliedState shareStock shareApplied
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      unless message.contains "boundary_comparison_mismatch:" &&
          message.contains ".universe" do
        throw error
      unless (← getGoals) == [shareAppliedGoal1, shareAppliedGoal2] do
        throwError "boundary_comparator_self_test_fresh_sharing_restore_failed"
      pure true
    unless shareRejected do
      throwError "boundary_comparator_self_test_fresh_sharing_accepted"
    testBaseState.restore
    let chainStockChild ← mkFreshLevelMVar
    let chainStockRoot ← mkFreshLevelMVar
    assignLevelMVar chainStockRoot.mvarId! (.succ chainStockChild)
    let chainStockGoal ← mkTestGoal (.sort chainStockRoot)
    setGoals [chainStockGoal]
    let chainStock ← boundarySnapshot basis
    let chainStockState ← Tactic.saveState
    testBaseState.restore
    let _unusedChainChild ← mkFreshLevelMVar
    let chainAppliedChild ← mkFreshLevelMVar
    let chainAppliedRoot ← mkFreshLevelMVar
    assignLevelMVar chainAppliedRoot.mvarId! (.succ chainAppliedChild)
    let chainAppliedGoal ← mkTestGoal (.sort chainAppliedRoot)
    setGoals [chainAppliedGoal]
    let chainApplied ← boundarySnapshot basis
    let chainAppliedState ← Tactic.saveState
    compareBoundaryStates basis chainStockState chainAppliedState chainStock chainApplied
    unless (← getGoals) == [chainAppliedGoal] do
      throwError "boundary_comparator_self_test_fresh_assignment_chain_restore_failed"
    testBaseState.restore
    let valueStockChild ← mkFreshLevelMVar
    let valueStockRoot ← mkFreshLevelMVar
    assignLevelMVar valueStockRoot.mvarId! (.succ valueStockChild)
    let valueStockGoal ← mkTestGoal (.sort valueStockRoot)
    setGoals [valueStockGoal]
    let valueStock ← boundarySnapshot basis
    let valueStockState ← Tactic.saveState
    testBaseState.restore
    let _unusedValueChild ← mkFreshLevelMVar
    let valueAppliedChild ← mkFreshLevelMVar
    let valueAppliedRoot ← mkFreshLevelMVar
    assignLevelMVar valueAppliedRoot.mvarId! (.succ (.succ valueAppliedChild))
    let valueAppliedGoal ← mkTestGoal (.sort valueAppliedRoot)
    setGoals [valueAppliedGoal]
    let valueApplied ← boundarySnapshot basis
    let valueAppliedState ← Tactic.saveState
    let valueRejected ← try
      compareBoundaryStates basis valueStockState valueAppliedState valueStock valueApplied
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      unless message.contains "boundary_comparison_mismatch:levelMVars" &&
          message.contains ".value" do
        throw error
      unless (← getGoals) == [valueAppliedGoal] do
        throwError "boundary_comparator_self_test_fresh_assignment_value_restore_failed"
      pure true
    unless valueRejected do
      throwError "boundary_comparator_self_test_fresh_assignment_value_accepted"
    testBaseState.restore
    let negativeGoal ← mkTestGoal (mkConst ``False)
    setGoals [negativeGoal]
    let negative ← boundarySnapshot basis
    let negativeState ← Tactic.saveState
    let negativeGoals ← getGoals
    let rejected ← try
      compareBoundaryStates basis stockState negativeState stock negative
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      unless message.contains "boundary_comparison_mismatch:goals[0].target:" do
        throw error
      unless (← getGoals) == negativeGoals do
        throwError "boundary_comparator_self_test_negative_restore_failed"
      unless !(← negativeGoal.isAssigned) do
        throwError "boundary_comparator_self_test_negative_assignment_restore_failed"
      let restoredNegativeType ← negativeGoal.getType
      let restoredNegativeTypeIsFalse ← withRestoredBoundaryFullMetaState do
        negativeGoal.withContext do
          isDefEqGuarded restoredNegativeType (mkConst ``False)
      unless restoredNegativeTypeIsFalse do
        throwError "boundary_comparator_self_test_negative_decl_restore_failed"
      pure true
    unless rejected do
      throwError "boundary_comparator_self_test_negative_accepted"
    testBaseState.restore
    parentGoal.assign (.mvar proofDependency)
    setGoals []
    let openProofStock ← boundarySnapshot basis
    let openProofStockState ← Tactic.saveState
    testBaseState.restore
    parentGoal.assign (mkConst ``True.intro)
    setGoals []
    let closedProofApplied ← boundarySnapshot basis
    let closedProofAppliedState ← Tactic.saveState
    let closedProofGoals ← getGoals
    let openProofRejected ← try
      compareBoundaryStates basis openProofStockState closedProofAppliedState
        openProofStock closedProofApplied
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      unless message.contains "boundary_comparison_mismatch:" &&
          message.contains ".assignment.proofMVars" do
        throw error
      unless (← getGoals) == closedProofGoals do
        throwError "boundary_comparator_self_test_proof_restore_failed"
      unless ← parentGoal.isAssigned do
        throwError "boundary_comparator_self_test_proof_assignment_restore_failed"
      let restoredProof ← instantiateMVars (.mvar parentGoal)
      let restoredProofIsClosed ← withRestoredBoundaryFullMetaState do
        parentGoal.withContext do
          isDefEqGuarded restoredProof (mkConst ``True.intro)
      unless restoredProofIsClosed do
        throwError "boundary_comparator_self_test_proof_value_restore_failed"
      pure true
    unless openProofRejected do
      throwError "boundary_comparator_self_test_open_proof_accepted"
    testBaseState.restore
    let reservedName := `Nat.add.congr_simp
    let environment ← getEnv
    unless !environment.contains reservedName do
      throwError "boundary_environment_action_self_test_name_already_present"
    unless isReservedName environment reservedName do
      throwError "boundary_environment_action_self_test_name_not_reserved"
    -- This is a recorder-side positive control, never artifact application.
    executeReservedNameAction reservedName
    unless (← getEnv).containsOnBranch reservedName do
      throwError "boundary_environment_action_self_test_replay_failed"
    IO.println "SIMP_ENGINE_BOUNDARY_COMPARATOR_SELF_TEST ok"
  finally
    outerState.restore

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

private def boundaryEnvironmentDeclarations (environment : Environment) :
    Array ConstantInfo :=
  environment.constants.foldStage2 (fun declarations _ info => declarations.push info) #[]

private def boundaryEnvironmentDelta (basis : PreBoundaryBasis)
    (environment : Environment) : Array ConstantInfo :=
  (boundaryEnvironmentDeclarations environment).filter fun info =>
    !basis.checkedDeclarationNames.contains info.name

private def boundaryEnvironmentPrivateName (_basis : PreBoundaryBasis) (name : Name) : Bool :=
  -- Authored public names such as `sample.proof_1` may look generated.
  -- Only Lean's private-name encoding justifies the private-proof exception.
  isPrivateName name

/-
  `ModuleData.entries` is the serialized view of persistent environment
  extensions.  Private-proof bookkeeping and the typed dependency/tag rules
  below are narrow closed-world exceptions.  Every other persistent extension
  must be byte-for-byte identical at the simp boundary.

  Keep these exceptions exact.  In particular, do not suffix-match private
  extension names: a project extension with a lookalike name is observable and
  must be compared.
-/
private def boundaryIsPermittedPersistentExtension (name : Name) : Bool :=
  name == `Lean.declRangeExt ||
    name == "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt".toName ||
    name == "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt".toName

private def boundaryExtraModUsesExtensionName : Name :=
  "_private.Lean.ExtraModUses.0.Lean.extraModUses".toName

private def boundaryIsTypedTagExtension (name : Name) : Bool :=
  name == `Lean.backwardDefeqAttr || name == `Lean.defeqAttr

private unsafe def boundaryCurrentExtraModUsesImpl (data : ModuleData) : Array ExtraModUse :=
  match data.entries.find? (fun entry => entry.1 == boundaryExtraModUsesExtensionName) with
  | some (_, entries) => unsafeCast entries
  | none => #[]

@[implemented_by boundaryCurrentExtraModUsesImpl]
private opaque boundaryCurrentExtraModUses (data : ModuleData) : Array ExtraModUse

private def normalizedBoundaryExtraModUses (uses : Array ExtraModUse) : Array ExtraModUse :=
  uses.foldl (init := #[]) (fun result use =>
      if result.contains use then result else result.push use)
    |>.qsort fun lhs rhs =>
      s!"{lhs.module}|{lhs.isExported}|{lhs.isMeta}" <
        s!"{rhs.module}|{rhs.isExported}|{rhs.isMeta}"

/- Stock simplification may record imports of theorem-provider modules that the
   closed artifact no longer consults. Omitting those dependency hints is safe;
   adding a dependency absent from stock is not. This is the same typed subset
   rule enforced by the completed-module declaration oracle. -/
private def compareBoundaryExtraModUses (stockData appliedData : ModuleData) : TacticM Unit := do
  let stock := normalizedBoundaryExtraModUses (boundaryCurrentExtraModUses stockData)
  let applied := normalizedBoundaryExtraModUses (boundaryCurrentExtraModUses appliedData)
  unless applied.all stock.contains do
    throwError "boundary_comparison_extra_module_uses_not_stock_subset"

private def normalizeBoundaryModuleData (data : ModuleData)
    (name : Name) (entries : Array EnvExtensionEntry) : ModuleData :=
  { data with
    imports := #[]
    constNames := #[]
    constants := #[]
    extraConstNames := #[]
    entries := #[(name, entries)] }

/- CompactedRegion is intentionally an unsafe runtime primitive.  The opaque
   declaration keeps that implementation detail out of the kernel-visible
   boundary checker while retaining the deterministic bytes produced by the
   same serializer used by the declaration oracle. -/
private unsafe def serializeBoundaryModuleDataImpl (data : ModuleData) : IO ByteArray := do
  IO.FS.withTempFile fun _ path => do
    let compactor ← CompactedRegion.save path `_simp_engine_boundary_extension data #[] none
    Runtime.forget compactor
    IO.FS.readBinFile path

@[implemented_by serializeBoundaryModuleDataImpl]
private opaque serializeBoundaryModuleData (data : ModuleData) : IO ByteArray

private def boundaryPersistentExtensionEntries (data : ModuleData) :
    Array (Name × Array EnvExtensionEntry) :=
  data.entries.qsort (fun lhs rhs => lhs.1.toString < rhs.1.toString)

private def compareBoundaryPersistentExtensions
    (stockData appliedData : ModuleData) : TacticM Unit := do
  compareBoundaryExtraModUses stockData appliedData
  let stockEntries := boundaryPersistentExtensionEntries stockData
  let appliedEntries := boundaryPersistentExtensionEntries appliedData
  let stockNames := stockEntries.map (·.1)
  let appliedNames := appliedEntries.map (·.1)
  let names := (stockNames ++ appliedNames).qsort (fun lhs rhs => lhs.toString < rhs.toString)
    |>.foldl (init := #[]) fun result name =>
      if result.contains name then result else result.push name
  for name in names do
    if boundaryIsPermittedPersistentExtension name ||
        name == boundaryExtraModUsesExtensionName ||
        boundaryIsTypedTagExtension name then
      continue
    let some (_, stockValues) := stockEntries.find? (fun entry => entry.1 == name)
      | throwError s!"boundary_comparison_missing_stock_extension:{name}"
    let some (_, appliedValues) := appliedEntries.find? (fun entry => entry.1 == name)
      | throwError s!"boundary_comparison_missing_applied_extension:{name}"
    let stockNormalized := normalizeBoundaryModuleData stockData name stockValues
    let appliedNormalized := normalizeBoundaryModuleData appliedData name appliedValues
    let stockBytes ← serializeBoundaryModuleData stockNormalized
    let stockBytesAgain ← serializeBoundaryModuleData stockNormalized
    unless stockBytes == stockBytesAgain do
      throwError s!"boundary_comparison_nondeterministic_extension_serialization:{name}"
    let appliedBytes ← serializeBoundaryModuleData appliedNormalized
    let appliedBytesAgain ← serializeBoundaryModuleData appliedNormalized
    unless appliedBytes == appliedBytesAgain do
      throwError s!"boundary_comparison_nondeterministic_extension_serialization:{name}"
    unless stockBytes == appliedBytes do
      throwError s!"boundary_comparison_extension_state:{name}"

private def boundaryPrivateProofDeclaration (basis : PreBoundaryBasis)
    (environment : Environment) (info : ConstantInfo) : TacticM Bool := do
  if !boundaryEnvironmentPrivateName basis info.name then
    return false
  match info with
  | .thmInfo _ => pure true
  | .defnInfo _ | .opaqueInfo _ =>
      withEnv environment <| withLCtx {} #[] <|
        withRestoredBoundaryFullMetaState <| isProp info.type
  | _ => pure false

/- Auxiliary lemma caches are local environment state, not serialized module
   entries. Preserve every pre-existing entry and every public helper entry.
   The existing private-proof omission policy applies only to a newly inserted
   private cache key whose value is a genuinely private, newly checked proof, with
   matching type, universes and requested definitional-equality tag. -/
private def normalizeBoundaryAuxLemmas (basis : PreBoundaryBasis)
    (before : AuxLemmas) (environment : Environment) (state : AuxLemmas) :
    TacticM AuxLemmas := do
  let mut result : AuxLemmas := {}
  for (key, value) in state.lemmas.toArray do
    let mut canOmit := false
    if key.isPrivate && (before.lemmas.find? key).isNone &&
        !basis.checkedDeclarationNames.contains value.1 then
      if let some info := environment.constants.find? value.1 then
        if key.type == info.type && value.2 == info.levelParams &&
            (!key.defeq || Lean.defeqAttr.hasTag environment value.1) then
          canOmit ← boundaryPrivateProofDeclaration basis environment info
    unless canOmit do
      result := { result with lemmas := result.lemmas.insert key value }
  return result

private def compareBoundaryAuxLemmas (basis : PreBoundaryBasis) (label : String)
    (before : AuxLemmas) (stockEnvironment appliedEnvironment : Environment)
    (stock applied : AuxLemmas) : TacticM Unit := do
  let stock ← normalizeBoundaryAuxLemmas basis before stockEnvironment stock
  let applied ← normalizeBoundaryAuxLemmas basis before appliedEnvironment applied
  let entries := stock.lemmas.toArray
  unless entries.size == applied.lemmas.toArray.size &&
      entries.all (fun (key, value) => applied.lemmas.find? key == some value) do
    throwError s!"boundary_comparison_local_aux_lemmas_state:{label}"

private unsafe def boundaryCurrentTagEntriesImpl (data : ModuleData)
    (extensionName : Name) : Array Name :=
  match data.entries.find? (fun entry => entry.1 == extensionName) with
  | some (_, entries) => unsafeCast entries
  | none => #[]

@[implemented_by boundaryCurrentTagEntriesImpl]
private opaque boundaryCurrentTagEntries (data : ModuleData)
    (extensionName : Name) : Array Name

private def compareBoundaryTagAttribute (basis : PreBoundaryBasis) (label : String)
    (tagAttr : TagAttribute) (stockEnvironment appliedEnvironment : Environment)
    (stockData appliedData : ModuleData) : TacticM Unit := do
  let stockDeclarations := boundaryEnvironmentDeclarations stockEnvironment
  let appliedDeclarations := boundaryEnvironmentDeclarations appliedEnvironment
  let stockTagged := boundaryCurrentTagEntries stockData tagAttr.ext.name
  let appliedTagged := boundaryCurrentTagEntries appliedData tagAttr.ext.name
  let names := (stockTagged ++ appliedTagged)
    |>.qsort (fun lhs rhs => lhs.toString < rhs.toString)
    |>.foldl (init := #[]) fun result name =>
      if result.contains name then result else result.push name
  for name in names do
    let stockInfo? := stockDeclarations.find? (fun info => info.name == name)
    let appliedInfo? := appliedDeclarations.find? (fun info => info.name == name)
    let stockPrivateProof ← match stockInfo? with
      | some info => boundaryPrivateProofDeclaration basis stockEnvironment info
      | none => pure false
    let appliedPrivateProof ← match appliedInfo? with
      | some info => boundaryPrivateProofDeclaration basis appliedEnvironment info
      | none => pure false
    let everyPresentDeclarationIsPrivateProof :=
      (stockInfo?.isNone || stockPrivateProof) &&
        (appliedInfo?.isNone || appliedPrivateProof)
    if everyPresentDeclarationIsPrivateProof then
      continue
    unless stockTagged.contains name == appliedTagged.contains name do
      throwError s!"boundary_comparison_extension_state:{label}:{name}"

private def captureBoundaryEnvironmentActions (basis : PreBoundaryBasis)
    (stockEnvironment : Environment) : TacticM (Array EnvironmentAction) := do
  let declarations := (boundaryEnvironmentDelta basis stockEnvironment).qsort
    (fun lhs rhs => lhs.name.toString < rhs.name.toString)
  -- A generated splitter's typed async snapshot authenticates bundle ownership.
  -- Bundles have disjoint members and independently closed bodies. Capture
  -- retains the existing deterministic action order and exact caller/async
  -- state checks; cross-bundle body dependencies remain unsupported.
  let mut matchers : Array (Name × Match.MatchEqns) := #[]
  let mut members : Array Name := #[]
  for info in declarations do
    if let .defnInfo _ := info then
      let state := Match.matchEqnsExt.getState stockEnvironment
        (asyncMode := .async .asyncEnv) (asyncDecl := info.name)
      let candidates := state.map.toArray.filter (fun (_, eqns) => eqns.splitterName == info.name)
      unless candidates.isEmpty do
        unless candidates.size == 1 do
          throwError "boundary_matcher_ambiguous_capture_provenance"
        let candidate := candidates[0]!
        let names := candidate.2.eqnNames.push candidate.2.splitterName
        if matchers.any (·.1 == candidate.1) || names.any members.contains then
          throwError "boundary_matcher_overlapping_capture_provenance"
        matchers := matchers.push candidate
        members := members ++ names
  matchers := matchers.qsort (fun lhs rhs => lhs.1.toString < rhs.1.toString)
  -- Sparse helpers need both typed cache provenance and the owning splitter's
  -- namespace. A prefix alone never exempts an unknown computational declaration.
  let mut sparseByAnchor : Std.HashMap Name (Array Name) := {}
  for info in declarations do
    if !members.contains info.name && isSparseCasesOn stockEnvironment info.name then
      let candidates := matchers.filter fun (_, eqns) =>
        eqns.splitterName.isPrefixOf info.name &&
          (sparseCasesOnCacheExt.getState stockEnvironment
            (asyncMode := .async .asyncEnv) (asyncDecl := eqns.splitterName)).toArray.any
              (fun (_, name) => name == info.name)
      unless candidates.size == 1 do
        throwError "boundary_sparse_ambiguous_matcher_owner:{info.name}"
      let anchor := candidates[0]!.1
      sparseByAnchor := sparseByAnchor.insert anchor
        ((sparseByAnchor.getD anchor #[]).push info.name)
      members := members.push info.name
  let mut actions : Array EnvironmentAction := #[]
  let mut helpers : Array TheoremVal := #[]
  for info in declarations do
    if members.contains info.name then
      continue
    if boundaryEnvironmentPrivateName basis info.name ||
        !isReservedName basis.environment info.name then
      -- Ordinary helpers are exact closed singleton theorems. Proof-valued
      -- definitions/opaque declarations remain unsupported instead of omitted.
      let .thmInfo thm := info
        | throwError s!"boundary_comparison_unsupported_environment_delta:{info.name}"
      helpers := helpers.push thm
    else
      let .thmInfo thm := info
        | throwError s!"boundary_comparison_unsupported_environment_delta:{info.name}"
      -- Inline all post-boundary constants, so each captured declaration
      -- depends only on the saved environment and sorted replay is sufficient.
      let thm := { thm with
        type := ← closeFreshConstants basis thm.type
        value := ← closeFreshConstants basis thm.value }
      let anchor := info.name.getPrefix
      unless (basis.environment.find? anchor (skipRealize := true)).isSome do
        throwError s!"boundary_comparison_unsupported_declaration_anchor:{anchor}"
      if let some kinds := congrKindsExt.find? stockEnvironment info.name then
        actions := actions.push (.declareCongruence info.name
          (← encodeBoundaryCongruence anchor thm kinds))
      else if let .str _ suffix := info.name then
        unless isEqnLikeSuffix suffix do
          throwError s!"boundary_comparison_unsupported_declaration_metadata:{info.name}"
        let mappedAnchor? := (eqnsExt.getState stockEnvironment).mapInv.find? info.name
        if let some mappedAnchor := mappedAnchor? then
          unless mappedAnchor == anchor do
            throwError s!"boundary_comparison_unsupported_equation_mapping:{info.name}"
        actions := actions.push (.declareEquation info.name
          (← encodeBoundaryEquation anchor thm
            (Lean.defeqAttr.hasTag stockEnvironment info.name)
            (Lean.backwardDefeqAttr.hasTag stockEnvironment info.name)
            mappedAnchor?.isSome))
      else
        throwError s!"boundary_comparison_unsupported_declaration_metadata:{info.name}"
  let ordinaryDeclarations := actions.map boundaryEnvironmentActionName ++ helpers.map (·.name)
  let mut priorMatcherEquations : Array Name := #[]
  for (anchor, eqns) in matchers do
    let sparseDeclarations := sparseByAnchor.getD anchor #[]
    let currentMembers := sparseDeclarations ++ eqns.eqnNames.push eqns.splitterName
    let otherDeclarations := ordinaryDeclarations ++ members.filter (!currentMembers.contains ·)
    let priorEquationDeclarations := actions.filterMap fun action => match action with
      | .declareEquation name _ => if name.toString < anchor.toString then some name else none
      | _ => none
    let payload ← withEnv stockEnvironment <| encodeBoundaryMatcher
      basis.environment basis.checkedDeclarationNames anchor eqns
      otherDeclarations (priorEquationDeclarations ++ priorMatcherEquations) sparseDeclarations
    actions := actions.push (.declareMatcher anchor payload)
    priorMatcherEquations := priorMatcherEquations ++ eqns.eqnNames
  let equations := actions.filterMap fun action => match action with
    | .declareEquation name source => some (name, source)
    | _ => none
  let matcherActions := actions.filterMap fun action => match action with
    | .declareMatcher name source => some (name, source)
    | _ => none
  if equations.size + matcherActions.size == actions.size then
    if let some (anchor, payload) ← encodeBoundaryRealizationSequence?
        basis.environment stockEnvironment basis.checkedDeclarationNames
        (declarations.map (·.name)) equations matcherActions helpers then
      return #[.realizeGroups anchor payload]
  unless helpers.isEmpty do
    let (anchor, payload) ← withEnv stockEnvironment <|
      encodeBoundaryLocalTheorems basis.environment helpers
    actions := actions.push (.declareLocalTheorems anchor payload)
  if helpers.isEmpty && (declarations.isEmpty || matchers.size > 0) then
    let equations := actions.filterMap fun action => match action with
      | .declareEquation name source => some (name, source)
      | _ => none
    let matcherActions := actions.filterMap fun action => match action with
      | .declareMatcher name source => some (name, source)
      | _ => none
    if equations.size + matcherActions.size == actions.size then
      if let some (anchor, payload) ← encodeBoundaryRealizationBatch?
          basis.environment stockEnvironment basis.checkedDeclarationNames equations matcherActions then
        return #[.realizeGroups anchor payload]
  return actions.qsort fun lhs rhs =>
    (boundaryEnvironmentActionName lhs).toString < (boundaryEnvironmentActionName rhs).toString

private def boundaryConstantMetadataEq
    (stock applied : ConstantInfo) : Bool :=
  match stock, applied with
  | .axiomInfo stock, .axiomInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.isUnsafe == applied.isUnsafe
  | .defnInfo stock, .defnInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.hints == applied.hints && stock.safety == applied.safety &&
        stock.all == applied.all
  | .thmInfo stock, .thmInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.all == applied.all
  | .opaqueInfo stock, .opaqueInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.isUnsafe == applied.isUnsafe && stock.all == applied.all
  | .quotInfo stock, .quotInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        match stock.kind, applied.kind with
        | .type, .type => true
        | .ctor, .ctor => true
        | .lift, .lift => true
        | .ind, .ind => true
        | _, _ => false
  | .inductInfo stock, .inductInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.numParams == applied.numParams && stock.numIndices == applied.numIndices &&
        stock.all == applied.all && stock.ctors == applied.ctors &&
        stock.numNested == applied.numNested && stock.isRec == applied.isRec &&
        stock.isUnsafe == applied.isUnsafe && stock.isReflexive == applied.isReflexive
  | .ctorInfo stock, .ctorInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.induct == applied.induct && stock.cidx == applied.cidx &&
        stock.numParams == applied.numParams && stock.numFields == applied.numFields &&
        stock.isUnsafe == applied.isUnsafe
  | .recInfo stock, .recInfo applied =>
      stock.name == applied.name && stock.levelParams == applied.levelParams &&
        stock.all == applied.all && stock.numParams == applied.numParams &&
        stock.numIndices == applied.numIndices && stock.numMotives == applied.numMotives &&
        stock.numMinors == applied.numMinors && stock.k == applied.k &&
        stock.isUnsafe == applied.isUnsafe && stock.rules.length == applied.rules.length &&
        (List.zipWith (fun stockRule appliedRule =>
          stockRule.ctor == appliedRule.ctor && stockRule.nfields == appliedRule.nfields)
          stock.rules applied.rules).all (fun value => value)
  | _, _ => false

private def boundaryDeclarationIsProp (environment : Environment)
    (info : ConstantInfo) : TacticM Bool :=
  withEnv environment <| withLCtx {} #[] <|
    withRestoredBoundaryFullMetaState <| isProp info.type

private def compareBoundaryRecursorRules (stockEnvironment : Environment)
    (stock applied : ConstantInfo) : TacticM Unit := do
  match stock, applied with
  | .recInfo stock, .recInfo applied =>
      for (stockRule, appliedRule) in List.zip stock.rules applied.rules do
        let equal ← withEnv stockEnvironment do
          withLCtx {} #[] do
            withRestoredBoundaryFullMetaState <|
              withNewMCtxDepth <| isDefEqGuarded stockRule.rhs appliedRule.rhs
        unless equal do
          boundaryComparisonMismatch s!"environment.declaration.recursorRule:{stock.name}"
  | _, _ => pure ()

private def compareBoundaryDeclaration (stockEnvironment : Environment)
    (stock applied : ConstantInfo) : TacticM Unit := do
  unless boundaryConstantMetadataEq stock applied do
    boundaryComparisonMismatch s!"environment.declaration.metadata:{stock.name}"
  let typeEqual ← withEnv stockEnvironment do
    withLCtx {} #[] do
      withRestoredBoundaryFullMetaState <| withNewMCtxDepth <| isDefEqGuarded stock.type applied.type
  unless typeEqual do
    boundaryComparisonMismatch s!"environment.declaration.type:{stock.name}"
  compareBoundaryRecursorRules stockEnvironment stock applied
  unless ← boundaryDeclarationIsProp stockEnvironment stock do
    match stock.value? (allowOpaque := true), applied.value? (allowOpaque := true) with
    | some stockValue, some appliedValue =>
        let valueEqual ← withEnv stockEnvironment do
          withLCtx {} #[] do
            withRestoredBoundaryFullMetaState <|
              withNewMCtxDepth <| isDefEqGuarded stockValue appliedValue
        unless valueEqual do
          boundaryComparisonMismatch s!"environment.declaration.value:{stock.name}"
    | none, none => pure ()
    | _, _ => boundaryComparisonMismatch s!"environment.declaration.value:{stock.name}"

private def compareBoundarySparseCasesCache (label : String)
    (stock applied : PHashMap SparseCasesOnKey Name) : TacticM Unit := do
  let entries := stock.toArray
  unless entries.size == applied.toArray.size &&
      entries.all (fun (key, value) => applied.find? key == some value) do
    throwError s!"boundary_comparison_local_sparse_cases_cache:{label}"

private def compareBoundaryHelperCache (members : Array Name) (label : String)
    (stock applied : AuxLemmas) : TacticM Unit := do
  let selected := fun (state : AuxLemmas) => state.lemmas.toArray.filter
    (fun (_, value) => members.contains value.1)
  let expected := selected stock
  let actual := selected applied
  unless expected.size == actual.size && expected.all (fun (key, value) =>
      actual.any (fun (otherKey, otherValue) => key == otherKey && value == otherValue)) do
    throwError "boundary_local_theorems_cache_conflict:{label}"

private def compareBoundaryEnvironment (basis : PreBoundaryBasis)
    (stockEnvironment appliedEnvironment : Environment)
    (actions : Array EnvironmentAction) : TacticM Unit := do
  compareBoundarySparseCasesCache "local" (sparseCasesOnCacheExt.getState stockEnvironment)
    (sparseCasesOnCacheExt.getState appliedEnvironment)
  let mut helperNames := #[]
  for action in actions do
    if let .declareLocalTheorems anchor payload := action then
      helperNames := helperNames ++ (← boundaryLocalTheoremNames anchor payload)
    if let .realizeGroups anchor payload := action then
      if isBoundaryRealizationSequence payload then
        let (_, _, helpers) ← boundaryRealizationSequenceMembers anchor payload
        helperNames := helperNames ++ helpers.map (·.1)
  compareBoundaryHelperCache helperNames "local"
    (auxLemmasExt.getState stockEnvironment) (auxLemmasExt.getState appliedEnvironment)
  let beforeAux := auxLemmasExt.getState basis.environment
  compareBoundaryAuxLemmas basis "local" beforeAux stockEnvironment appliedEnvironment
    (auxLemmasExt.getState stockEnvironment) (auxLemmasExt.getState appliedEnvironment)
  -- Match-equation metadata is local and absent from ModuleData. Realizations
  -- also retain local state in their completed declaration snapshots. Check
  -- every current-stage name, including private proofs and existing names.
  unless boundaryMatchEqnsStateEq (Match.matchEqnsExt.getState stockEnvironment)
      (Match.matchEqnsExt.getState appliedEnvironment) do
    throwError "boundary_comparison_local_match_eqns_state:local"
  let names := (boundaryEnvironmentDeclarations stockEnvironment ++
      boundaryEnvironmentDeclarations appliedEnvironment).foldl
    (fun names info => names.insert info.name) ({} : NameSet)
  for name in names do
    compareBoundaryHelperCache helperNames name.toString
      (auxLemmasExt.getState (asyncMode := .async .asyncEnv) (asyncDecl := name) stockEnvironment)
      (auxLemmasExt.getState (asyncMode := .async .asyncEnv) (asyncDecl := name) appliedEnvironment)
    compareBoundarySparseCasesCache name.toString
      (sparseCasesOnCacheExt.getState (asyncMode := .async .asyncEnv)
        (asyncDecl := name) stockEnvironment)
      (sparseCasesOnCacheExt.getState (asyncMode := .async .asyncEnv)
        (asyncDecl := name) appliedEnvironment)
    let before := if basis.checkedDeclarationNames.contains name then
        auxLemmasExt.getState (asyncMode := .async .asyncEnv)
          (asyncDecl := name) basis.environment
      else beforeAux
    compareBoundaryAuxLemmas basis name.toString before stockEnvironment appliedEnvironment
      (auxLemmasExt.getState (asyncMode := .async .asyncEnv)
        (asyncDecl := name) stockEnvironment)
      (auxLemmasExt.getState (asyncMode := .async .asyncEnv)
        (asyncDecl := name) appliedEnvironment)
    unless boundaryMatchEqnsStateEq
        (Match.matchEqnsExt.getState (asyncMode := .async .asyncEnv)
          (asyncDecl := name) stockEnvironment)
        (Match.matchEqnsExt.getState (asyncMode := .async .asyncEnv)
          (asyncDecl := name) appliedEnvironment) do
      throwError s!"boundary_comparison_local_match_eqns_state:{name}"
  let stockModuleData ← observePrivateModuleData stockEnvironment
  let appliedModuleData ← observePrivateModuleData appliedEnvironment
  compareBoundaryPersistentExtensions stockModuleData appliedModuleData
  compareBoundaryTagAttribute basis "backwardDefeqAttr" Lean.backwardDefeqAttr
    stockEnvironment appliedEnvironment stockModuleData appliedModuleData
  compareBoundaryTagAttribute basis "defeqAttr" Lean.defeqAttr
    stockEnvironment appliedEnvironment stockModuleData appliedModuleData
  let stockDelta := boundaryEnvironmentDelta basis stockEnvironment
  let appliedDelta := boundaryEnvironmentDelta basis appliedEnvironment
  let stockPublic :=
    (stockDelta.filter (!boundaryEnvironmentPrivateName basis ·.name)).qsort
      (fun lhs rhs => lhs.name.toString < rhs.name.toString)
  let appliedPublic :=
    (appliedDelta.filter (!boundaryEnvironmentPrivateName basis ·.name)).qsort
      (fun lhs rhs => lhs.name.toString < rhs.name.toString)
  let stockPublicNames := stockPublic.map (·.name)
  let appliedPublicNames := appliedPublic.map (·.name)
  unless stockPublicNames == appliedPublicNames do
    throwError "boundary_comparison_unsupported_environment_delta"
  let actionNames := actions.filterMap fun action => match action with
    | .declareMatcher _ _ | .declareLocalTheorems _ _ | .realizeGroups _ _ => none
    | _ => some (boundaryEnvironmentActionName action)
  let mut groupPublicNames := #[]
  for action in actions do
    if let .realizeGroups anchor payload := action then
      let (members, newPublic) ← if isBoundaryRealizationSequence payload then do
          let (members, newPublic, _) ← boundaryRealizationSequenceMembers anchor payload
          pure (members, newPublic)
        else do
          let (cached, members, publicMembers) ← boundaryRealizationBatchMembers payload
          pure (members, if cached then #[] else publicMembers)
      groupPublicNames := groupPublicNames ++ newPublic
      for name in members do
        let some stockInfo := stockEnvironment.checked.get.find? name
          | throwError "boundary_realization_missing_stock_member:{name}"
        let some appliedInfo := appliedEnvironment.checked.get.find? name
          | throwError "boundary_realization_missing_applied_member:{name}"
        compareBoundaryDeclaration stockEnvironment stockInfo appliedInfo
  let actionNames := (actionNames ++ groupPublicNames ++ helperNames.filter (!boundaryEnvironmentPrivateName basis ·)).qsort
    (fun a b => a.toString < b.toString)
  unless actionNames == stockPublicNames do
    throwError "boundary_comparison_unsupported_environment_delta"
  -- A matcher action names an existing anchor, while its added members are
  -- private. Require every captured member on both sides, including proof
  -- members that the general private-proof omission policy would permit.
  for action in actions do
    if let .declareMatcher anchor payload := action then
      let members ← withEnv stockEnvironment <| boundaryMatcherDeclarationNames anchor payload
      for name in members do
        let some stockInfo := stockDelta.find? (·.name == name)
          | throwError s!"boundary_matcher_missing_stock_member:{name}"
        let some appliedInfo := appliedDelta.find? (·.name == name)
          | throwError s!"boundary_matcher_missing_applied_member:{name}"
        compareBoundaryDeclaration stockEnvironment stockInfo appliedInfo
  for name in helperNames do
    let some (.thmInfo stockInfo) := stockDelta.find? (·.name == name)
      | throwError "boundary_local_theorems_missing_stock_member:{name}"
    let some (.thmInfo appliedInfo) := appliedDelta.find? (·.name == name)
      | throwError "boundary_local_theorems_missing_applied_member:{name}"
    let stockPayload ← withEnv stockEnvironment <| encodeBoundaryTheorem stockInfo
    let appliedPayload ← withEnv appliedEnvironment <| encodeBoundaryTheorem appliedInfo
    unless (← boundaryLocalTheoremExportKind stockEnvironment name) ==
        (← boundaryLocalTheoremExportKind appliedEnvironment name) do
      throwError "boundary_local_theorems_exported_kind_conflict:{name}"
    unless stockPayload == appliedPayload do
      throwError "boundary_local_theorems_canonical_body_conflict:{name}"
    unless defeqAttr.hasTag stockEnvironment name == defeqAttr.hasTag appliedEnvironment name &&
        backwardDefeqAttr.hasTag stockEnvironment name == backwardDefeqAttr.hasTag appliedEnvironment name do
      throwError "boundary_local_theorems_tag_conflict:{name}"
  for stockInfo in stockPublic do
    let some appliedInfo := appliedDelta.find? (fun info => info.name == stockInfo.name)
      | throwError "boundary_comparison_unsupported_environment_delta"
    compareBoundaryDeclaration stockEnvironment stockInfo appliedInfo
  for stockInfo in stockDelta do
    if boundaryEnvironmentPrivateName basis stockInfo.name then
      match appliedDelta.find? (fun info => info.name == stockInfo.name) with
      | some appliedInfo =>
          compareBoundaryDeclaration stockEnvironment stockInfo appliedInfo
      | none =>
          unless ← boundaryPrivateProofDeclaration basis stockEnvironment stockInfo do
            throwError s!"boundary_comparison_unsupported_environment_delta:{stockInfo.name}"
  for appliedInfo in appliedDelta do
    if boundaryEnvironmentPrivateName basis appliedInfo.name &&
        (stockDelta.find? (fun info => info.name == appliedInfo.name)).isNone then
      unless ← boundaryPrivateProofDeclaration basis appliedEnvironment appliedInfo do
        throwError s!"boundary_comparison_unsupported_environment_delta:{appliedInfo.name}"
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

/-- Encode the captured kernel expression directly. No source parser, term
    elaborator, instance search, or universe inference runs during decoding. -/
private def renderArtifactExpr (references : Array LMVarId) (expression : Expr) : MetaM String :=
  encodeBoundaryExprWithUniverses expression references

private def transformationJson (references : Array LMVarId) (transformation : TargetArtifact) : TacticM Json := do
  let proofJson ← match transformation.proof? with
    | none => pure Json.null
    | some proof => pure (Json.str (← renderArtifactExpr references proof))
  return Json.mkObj [
    ("input", Json.str (← renderArtifactExpr references transformation.input)),
    ("result", Json.str (← renderArtifactExpr references transformation.result)),
    ("proof", proofJson)
  ]

private def artifactTerminal (artifact : GoalArtifact) : String :=
  if artifact.locals.any (·.transformation.result.isFalse) then
    "closed_from_local_false"
  else if artifact.target?.any (·.result.isTrue) then
    "closed_from_target_true"
  else
    "open"

private def appliedTerminal (terminal : GoalTerminal) : String :=
  match terminal with
  | .open => "open"
  | .closedFromLocalFalse => "closed_from_local_false"
  | .closedFromTargetTrue => "closed_from_target_true"

private def artifactEncodingJson : Json := Json.mkObj [
  ("terms", Json.str boundaryArtifactTermEncoding),
  ("locals", Json.str boundaryArtifactLocalReferenceEncoding),
  ("universes", Json.str boundaryArtifactUniverseEncoding),
  ("instances", Json.str boundaryArtifactInstanceEncoding)
]

private def boundaryRecordingNonce : TacticM String := do
  match ← IO.getEnv boundaryRunNonceEnv with
  | some nonce =>
    if nonce.isEmpty then
      pure boundaryUnauthenticatedRunNonce
    else
      pure nonce
  | none =>
    pure boundaryUnauthenticatedRunNonce

private def emitBoundaryJsonMarker (marker : String) (payload : Json) : TacticM Unit := do
  let nonce ← boundaryRecordingNonce
  -- Stock tactics may have printed a partial line before recording failed.
  IO.println s!"\n{marker}{nonce} {payload.compress}"

private def artifactReportJson (basis : PreBoundaryBasis) (occId : String) (selector : Json)
    (artifact : GoalArtifact) (terminal : String)
    (stockGenerator : DeclNameGenerator) : TacticM Json :=
  withBoundaryEncodedSourceContext do
  let mut localReports := #[]
  for localArtifact in artifact.locals do
    let decl ← localArtifact.fvarId.getDecl
    localReports := localReports.push <| Json.mkObj [
      ("userName", Json.str decl.userName.toString),
      ("reference", Json.mkObj [
        ("kind", Json.str "local_decl_index"),
        ("index", toJson decl.index)
      ]),
      ("transformation", ← transformationJson basis.universeReferences localArtifact.transformation)
    ]
  let targetJson ← artifact.target?.mapM (transformationJson basis.universeReferences)
  return Json.mkObj [
    ("kind", Json.str boundaryArtifactKind),
    ("schema", toJson boundaryArtifactSchema),
    ("semanticContract", Json.str boundarySemanticContract),
    ("occurrence", Json.str occId),
    ("selector", selector),
    ("status", Json.str "success"),
    ("stockGenerator", encodeBoundaryDeclNameGenerator stockGenerator),
    ("terminal", Json.str terminal),
    ("encoding", artifactEncodingJson),
    ("stateDeltas", Json.arr #[]),
    ("environmentActions", Json.arr (artifact.environmentActions.map
      boundaryEnvironmentActionJson)),
    ("locals", Json.arr localReports),
    ("target", targetJson.getD Json.null)
  ]

private def failureReportJson (occId : String) (selector : Json) : Json :=
  Json.mkObj [
    ("kind", Json.str boundaryArtifactKind),
    ("schema", toJson boundaryArtifactSchema),
    ("semanticContract", Json.str boundarySemanticContract),
    ("occurrence", Json.str occId),
    ("selector", selector),
    ("status", Json.str "failure")
  ]

/-- Failed tactics roll back ordinary messages when an enclosing alternative
    catches the exception. Emit the closed failure observation directly so the
    translation harness can materialize the same transactional failure. -/
private def emitFailureReport (occId : String) (selector : Json) : TacticM Unit :=
  emitBoundaryJsonMarker "SIMP_ENGINE_BOUNDARY_ARTIFACT "
    (failureReportJson occId selector)

private def recordingAbortJson (occId moduleName stage detail : String) : Json :=
  Json.mkObj [
    ("kind", Json.str "simp_engine_boundary_recording_abort"),
    ("schema", toJson (1 : Nat)),
    ("occurrence", Json.str occId),
    ("module", Json.str moduleName),
    ("stage", Json.str stage),
    ("detail", Json.str detail)
  ]

/-- This marker uses direct IO so an enclosing `first` or `try` cannot roll it
    back with ordinary tactic messages. A fingerprinting or post-stock recorder
    failure is an infrastructure abort, never evidence that the call was
    unobserved. -/
private def emitRecordingAbort (occId stage : String) (error : Exception) : TacticM Unit := do
  let detail ← try
    error.toMessageData.toString
  catch _ =>
    pure "boundary recorder raised an unrenderable exception"
  let moduleName := (← getEnv).mainModule.toString
  emitBoundaryJsonMarker "SIMP_ENGINE_BOUNDARY_RECORDING_ABORT "
    (recordingAbortJson occId moduleName stage detail)

private def runBoundaryProbe (simpStx : Syntax)
    (reportRequest? : Option (String × Json) := none) : TacticM GoalArtifact := do
  let pre ← Tactic.saveState
  let preGenerator ← getDeclNGen
  let basis ← mkPreBoundaryBasis
  let selection ← try
    resolveLocation simpStx
  catch error =>
    pre.restore
    if let some (occId, selector) := reportRequest? then
      emitFailureReport occId selector
    throw error
  let stockClosed ← try
    executeStockLocation simpStx selection
  catch error =>
    let failureGenerator ← getDeclNGen
    pre.restore
    if failureGenerator.namePrefix != preGenerator.namePrefix ||
        failureGenerator.idx != preGenerator.idx ||
        failureGenerator.parentIdxs != preGenerator.parentIdxs then
      if let some (occId, _) := reportRequest? then
        emitBoundaryJsonMarker "SIMP_ENGINE_BOUNDARY_RECORDING_ABORT " <|
          recordingAbortJson occId (← getEnv).mainModule.toString "stock_failure_state"
            "boundary_stock_failure_aux_decl_name_effect_unsupported"
      throwError "boundary_stock_failure_aux_decl_name_effect_unsupported"
    if let some (occId, selector) := reportRequest? then
      emitFailureReport occId selector
    throw error
  -- Core.SavedState.restore deliberately retains name-generator advancement.
  -- Snapshot the original result before diagnostics/trials; reset generators
  -- only for isolated trial input and return the original stock continuation.
  let stockState ← Tactic.saveState
  let stockGenerator ← getDeclNGen
  let stockEnvironment ← getEnv
  let restoreTrialInput : TacticM Unit := do
    pre.restore
    setDeclNGen preGenerator
  let postStockAction : TacticM (GoalArtifact × String) := do
    let stock ← boundarySnapshot basis
    let environmentActions ← captureBoundaryEnvironmentActions basis stockEnvironment
    restoreTrialInput
    let artifact ← captureGoalArtifact basis simpStx selection
    let artifact := { artifact with environmentActions }
    let terminal := artifactTerminal artifact
    -- Rendering must happen in the original local context. Proof-bearing local
    -- transformations clear their old declarations during apply, after which a
    -- pretty printer can no longer recover valid source names for the artifact.
    let report? ← reportRequest?.mapM fun (occId, selector) =>
      artifactReportJson basis occId selector artifact terminal stockGenerator
    restoreTrialInput
    let initialGoals ← getGoals
    let (applyGoals, applyTerminal) ←
      applyGoalArtifact initialGoals.head! initialGoals.tail artifact
    unless terminal == appliedTerminal applyTerminal do
      throwError s!"boundary_terminal_mismatch: artifact={terminal}; \
        apply={appliedTerminal applyTerminal}"
    setGoals applyGoals
    let applied ← boundarySnapshot basis
    let appliedState ← Tactic.saveState
    compareBoundaryStates basis stockState appliedState stock applied
    compareBoundaryEnvironment basis stockEnvironment (← getEnv) environmentActions
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
    let message := s!"SIMP_ENGINE_BOUNDARY_PROBE outcome={outcome} evidence={evidence} equivalent=true"
    if let some report := report? then
      emitBoundaryJsonMarker "SIMP_ENGINE_BOUNDARY_ARTIFACT " report
    return (artifact, message)
  let (artifact, message) ← try
    postStockAction
  catch error =>
    if let some (occId, _) := reportRequest? then
      emitRecordingAbort occId "post_stock" error
    throw error
  finally
    stockState.restore
    setDeclNGen stockGenerator
  -- Preserve the diagnostic without preserving any trial elaboration state.
  logInfo m!"{message}"
  return artifact

elab_rules : tactic
  | `(tactic| simp_engine_boundary_comparator_self_test) => withMainContext do
      runBoundaryComparatorSelfTest
  | `(tactic| simp_engine_boundary_probe $args:boundarySimpArgs) => withMainContext do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      discard <| runBoundaryProbe inner
  | `(tactic| simp_engine_boundary_record $occurrenceId:str $args:boundarySimpArgs) =>
      withMainContext do
        let occId := occurrenceId.getString
        unless !occId.isEmpty do
          throwError "invalid_boundary_occurrence"
        let goals ← getGoals
        let preState ← try
          boundaryProofStateFingerprintWithTerm goals (← getThe Term.State)
        catch error =>
          emitRecordingAbort occId "prestate_fingerprint" error
          throw error
        let caller? ← Term.getDeclName?
        let selector := Json.mkObj [
          ("selectorSchema", toJson boundarySelectorSchema),
          ("occurrence", Json.str occId),
          ("preState", toJson preState),
          ("options", Json.str (boundaryOptionsFingerprint (← getOptions))),
          ("module", Json.str (← getEnv).mainModule.toString),
          ("caller", caller?.map (fun name =>
            Json.str (boundaryCallerIdentity name)) |>.getD Json.null)
        ]
        let inner := mkNode ``Lean.Parser.Tactic.simp #[
          mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
        discard <| runBoundaryProbe inner (some (occId, selector))

end ExplicitLean.SimpEngine.Boundary
