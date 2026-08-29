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
  exprMVars : Array ExprMVarBasis
  levelMVars : Array LevelMVarBasis
  fvarIds : Array FVarId
  syntheticMVars : Array (MVarId × Term.SyntheticMVarDecl)

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
  let mctx ← getMCtx
  let term ← getThe Term.State
  let goals ← getGoals
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
    environment := ← getEnv
    exprMVars
    levelMVars
    fvarIds := allFVarIds
    syntheticMVars
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
      unless appliedPre && stockPre && applied == stock do
        throwError s!"boundary_comparison_unpaired_fresh_universe_mvar:{label}"
      return { mapping with lmvars := mapping.lmvars.push (applied, stock) }

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
        unless stockEntry.status.isProof do
          let some stockValue := stockEntry.status.valueOpt
            | boundaryComparisonMismatch "exprMVars.assignment.stockValue"
          let some appliedValue := appliedEntry.status.valueOpt
            | boundaryComparisonMismatch "exprMVars.assignment.appliedValue"
          let (mapping', queue') ← pairBoundaryExprMVars basis mapping queue
            stockValue appliedValue "exprMVars.assignment"
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
  for entry in stock.levelMVars do
    unless basis.levelMVars.any (fun pre => pre.id == entry.id) do
      throwError "boundary_comparison_unpaired_fresh_universe_mvar"
  for entry in applied.levelMVars do
    unless basis.levelMVars.any (fun pre => pre.id == entry.id) do
      throwError "boundary_comparison_unpaired_fresh_universe_mvar"
  return mapping

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

private def mapBoundaryExpr (mapping : BoundaryIdMap) (expression : Expr) : MetaM Expr :=
  Core.transform expression (pre := fun subexpression => do
    match subexpression with
    | .fvar id =>
        let some mapped := findPairByApplied? mapping.fvars id
          | throwError "boundary_comparison_unpaired_fresh_fvar"
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
  let applied ← mapBoundaryExpr mapping applied
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
      | throwError "boundary_comparison_unpaired_fresh_fvar"
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
      | throwError "boundary_comparison_unpaired_fresh_fvar"
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
    (stock applied : List Term.LetRecToLift) : TacticM Unit := do
  unless stock.isEmpty && applied.isEmpty do
    throwError "boundary_comparison_unpaired_fresh_letrec"

private def compareBoundarySnapshot (basis : PreBoundaryBasis)
    (mapping : BoundaryIdMap) (stock applied : BoundarySnapshot) : TacticM Unit := do
  unless stock.options == applied.options do boundaryComparisonMismatch "options"
  unless stock.mctxDepth == applied.mctxDepth do boundaryComparisonMismatch "mctx.depth"
  unless stock.levelAssignDepth == applied.levelAssignDepth do
    boundaryComparisonMismatch "mctx.levelAssignDepth"
  unless stock.levelNames == applied.levelNames do boundaryComparisonMismatch "term.levelNames"
  compareBoundaryLetRecs stock.letRecsToLift applied.letRecsToLift
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
  for pre in basis.levelMVars do
    let some stockEntry := findLevelMVarSnapshot? stock pre.id
      | boundaryComparisonMismatch s!"levelMVars[{pre.decl.index}].missingStock"
    let some appliedEntry := findLevelMVarSnapshot? applied pre.id
      | boundaryComparisonMismatch s!"levelMVars[{pre.decl.index}].missingApplied"
    unless stockEntry.decl.depth == appliedEntry.decl.depth do
      boundaryComparisonMismatch s!"levelMVars[{pre.decl.index}].depth"
    unless stockEntry.status.tag == appliedEntry.status.tag do
      boundaryComparisonMismatch s!"levelMVars[{pre.decl.index}].status"
    if stockEntry.status.tag == boundaryLevelAssigned then
      let some stockLevel := stockEntry.status.valueOpt
        | boundaryComparisonMismatch s!"levelMVars[{pre.decl.index}].stockValue"
      let some appliedLevel := appliedEntry.status.valueOpt
        | boundaryComparisonMismatch s!"levelMVars[{pre.decl.index}].appliedValue"
      compareBoundaryLevel mapping s!"levelMVars[{pre.decl.index}].value"
        stockLevel appliedLevel
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
    let basis ← mkPreBoundaryBasis
    let stockGoal ← mkTestGoal (mkConst ``True)
    setGoals [stockGoal]
    let stock ← boundarySnapshot basis
    let stockState ← Tactic.saveState
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
  let stockState ← Tactic.saveState
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
  let appliedState ← Tactic.saveState
  compareBoundaryStates basis stockState appliedState stock applied
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
  | `(tactic| simp_engine_boundary_comparator_self_test) => withMainContext do
      runBoundaryComparatorSelfTest
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
