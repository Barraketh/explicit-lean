module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.Selector
public meta import ExplicitLean.SimpEngine.Boundary.NoSynthesis

public meta section
open Lean Meta
namespace ExplicitLean.SimpEngine.Boundary

/-- Process-local identities from the already authenticated selector. No raw
    identity is reconstructed from wire data. Closed codecs do not use this. -/
structure BoundaryExpressionReferences where
  universes : Array LMVarId
  mvars : Array MVarId
  visible : List MVarId
  before : MetavarContext

def boundaryExpressionReferenceContext (goals : List MVarId)
    (termState : Lean.Elab.Term.State) : MetaM BoundaryExpressionReferences := do
  let before ← getMCtx
  let (mvars, universes) ← boundaryCanonicalReferenceTables goals termState
  unless mvars.all before.decls.contains && universes.all before.lDecls.contains do
    throwError "boundary_reference_observation_created_identity"
  return {mvars, universes, visible := goals, before}

private def sameExprOption : Option Expr → Option Expr → Bool
  | none, none => true
  | some a, some b => a.equal b
  | _, _ => false

private def sameLocalDecl (a b : LocalDecl) : Bool :=
  a.index == b.index && a.fvarId == b.fvarId && a.userName == b.userName &&
    a.type.equal b.type && a.binderInfo == b.binderInfo && a.kind == b.kind &&
    sameExprOption (a.value? (allowNondep := true)) (b.value? (allowNondep := true)) &&
    a.isLet (allowNondep := true) == b.isLet (allowNondep := true) &&
    (match a, b with
      | .ldecl (nondep := x) .., .ldecl (nondep := y) .. => x == y
      | .cdecl .., .cdecl .. => true
      | _, _ => false)

private def sameLocalContext (a b : LocalContext) : Bool :=
  let xs := a.decls.toArray
  let ys := b.decls.toArray
  xs.size == ys.size && (xs.zip ys).all (fun (x, y) => match x, y with
    | none, none => true
    | some x, some y => sameLocalDecl x y
    | _, _ => false) &&
  a.fvarIdToDecl.toList.length == b.fvarIdToDecl.toList.length &&
  a.fvarIdToDecl.toList.all (fun (id, d) => (b.find? id).any (sameLocalDecl d)) &&
  a.auxDeclToFullName.toList.length == b.auxDeclToFullName.toList.length &&
  a.auxDeclToFullName.toList.all (fun (id, n) => b.auxDeclToFullName.get? id == some n)

private def kindTag : MetavarKind → Nat
  | .natural => 0
  | .synthetic => 1
  | .syntheticOpaque => 2

private def sameMetavarDecl (a b : MetavarDecl) : Bool :=
  a.userName == b.userName && a.index == b.index && kindTag a.kind == kindTag b.kind &&
  a.depth == b.depth && a.numScopeArgs == b.numScopeArgs && a.type.equal b.type &&
  sameLocalContext a.lctx b.lctx && a.localInstances.size == b.localInstances.size &&
  (a.localInstances.zip b.localInstances).all (fun (x, y) =>
    x.className == y.className && x.fvar.equal y.fvar)

private def sameDelayed : Option DelayedMetavarAssignment → Option DelayedMetavarAssignment → Bool
  | none, none => true
  | some a, some b => a.mvarIdPending == b.mvarIdPending && a.fvars.size == b.fvars.size &&
      (a.fvars.zip b.fvars).all (fun (x, y) => x.equal y)
  | _, _ => false

private def unchangedMVar (before after : MetavarContext) (id : MVarId) : Bool :=
  match before.decls.find? id, after.decls.find? id with
  | some a, some b => sameMetavarDecl a b &&
      sameExprOption (before.eAssignment.find? id) (after.eAssignment.find? id) &&
      sameDelayed (before.dAssignment.find? id) (after.dAssignment.find? id)
  | _, _ => false

/-- Only the narrow non-visible opaque/unassigned domain has a full existing
    selector record and is supported initially. -/
def BoundaryExpressionReferences.resolve (refs : BoundaryExpressionReferences)
    (index : Nat) : MetaM MVarId := do
  let some id := refs.mvars[index]? | throwError "boundary_reference_index"
  let mctx ← getMCtx
  let some decl := refs.before.decls.find? id | throwError "boundary_reference_missing"
  unless kindTag decl.kind == 2 && !refs.visible.contains id &&
      !refs.before.eAssignment.contains id && !refs.before.dAssignment.contains id do
    throwError "boundary_reference_ineligible"
  unless unchangedMVar refs.before mctx id do
    throwError "boundary_reference_state_changed"
  return id

private structure GraphState where
  mvars : Std.HashMap MVarId Bool := {}
  fvars : Std.HashMap (Option MVarId × FVarId) Bool := {}
  exprs : Std.HashMap (Option MVarId) (ExprStructMap Unit) := {}
  order : Array MVarId := #[]
  levels : Std.HashMap LMVarId Bool := {}
  levelOrder : Array LMVarId := #[]
  steps : Nat := 0
private abbrev GraphM := StateT GraphState (Except String)

private def tick : GraphM Unit := do
  modify fun s => {s with steps := s.steps + 1}
  if (← get).steps > 1000000 then throw "boundary_reference_dependency_limit"

private partial def visitLevel (mctx : MetavarContext) (level : Level) : GraphM Unit := do
  tick
  match level with
  | .mvar id =>
      if let some done := (← get).levels[id]? then
        unless done do throw "boundary_reference_level_cycle"
        return
      unless mctx.lDecls.contains id do throw "boundary_reference_unknown_level"
      modify fun s => {s with levels := s.levels.insert id false, levelOrder := s.levelOrder.push id}
      if let some value := mctx.lAssignment.find? id then visitLevel mctx value
      modify fun s => {s with levels := s.levels.insert id true}
  | .succ l => visitLevel mctx l
  | .max a b | .imax a b => visitLevel mctx a; visitLevel mctx b
  | _ => pure ()

mutual
private partial def visitExpr (mctx : MetavarContext) (destination : Option MVarId)
    (context : Option MVarId) (lctx : LocalContext) (e : Expr) : GraphM Unit := do
  tick
  if ((← get).exprs[context]?.getD {}).contains ⟨e⟩ then return
  -- Mark after descent: a cyclic expression dependency must not be hidden by memoization.
  match e with
  | .sort level => visitLevel mctx level
  | .const _ levels => levels.forM (visitLevel mctx)
  | .mvar id => visitMVar mctx destination id
  | .fvar id => visitFVar mctx destination context lctx id
  | .app f a => visitExpr mctx destination context lctx f; visitExpr mctx destination context lctx a
  | .lam _ t b _ | .forallE _ t b _ =>
      visitExpr mctx destination context lctx t; visitExpr mctx destination context lctx b
  | .letE _ t v b _ =>
      visitExpr mctx destination context lctx t; visitExpr mctx destination context lctx v
      visitExpr mctx destination context lctx b
  | .mdata _ b | .proj _ _ b => visitExpr mctx destination context lctx b
  | _ => pure ()
  modify fun s => {s with exprs := s.exprs.insert context ((s.exprs[context]?.getD {}).insert ⟨e⟩ ())}

private partial def visitFVar (mctx : MetavarContext) (destination : Option MVarId)
    (context : Option MVarId) (lctx : LocalContext) (id : FVarId) : GraphM Unit := do
  tick
  let some decl := lctx.find? id | throw "boundary_reference_unknown_local"
  let key := (context, id)
  if let some done := (← get).fvars[key]? then
    unless done do throw "boundary_reference_dependency_cycle"
    return
  modify fun s => {s with fvars := s.fvars.insert key false}
  visitExpr mctx destination context lctx decl.type
  if let some value := decl.value? (allowNondep := true) then visitExpr mctx destination context lctx value
  modify fun s => {s with fvars := s.fvars.insert key true}

private partial def visitMVar (mctx : MetavarContext) (destination : Option MVarId)
    (id : MVarId) : GraphM Unit := do
  tick
  if destination == some id then throw "boundary_reference_occurs"
  if let some done := (← get).mvars[id]? then
    unless done do throw "boundary_reference_dependency_cycle"
    return
  let some decl := mctx.decls.find? id | throw "boundary_reference_unknown_dependency"
  modify fun s => {s with mvars := s.mvars.insert id false, order := s.order.push id}
  visitExpr mctx destination (some id) decl.lctx decl.type
  for localDecl in decl.lctx do visitFVar mctx destination (some id) decl.lctx localDecl.fvarId
  for inst in decl.localInstances do visitExpr mctx destination (some id) decl.lctx inst.fvar
  if let some value := mctx.eAssignment.find? id then visitExpr mctx destination (some id) decl.lctx value
  if let some value := mctx.dAssignment.find? id then
    visitMVar mctx destination value.mvarIdPending
    -- Delayed arguments belong to the pending metavariable's context, not
    -- the outer assigned metavariable's context (pinned MetavarContext.lean).
    let some pending := mctx.decls.find? value.mvarIdPending
      | throw "boundary_reference_unknown_dependency"
    for fvar in value.fvars do
      visitExpr mctx destination (some value.mvarIdPending) pending.lctx fvar
  modify fun s => {s with mvars := s.mvars.insert id true}
end

private def runGraph (mctx : MetavarContext) (destination : Option MVarId)
    (lctx : LocalContext) (expressions : Array Expr) : MetaM (Array MVarId × Array LMVarId) := do
  let action : GraphM Unit := expressions.forM (visitExpr mctx destination none lctx)
  match action.run {} with
  | .ok (_, result) => return (result.order, result.levelOrder)
  | .error error => throwError "{error}"

/-- Exact process-local protection of the used references and their raw
    dependency closure, including aliases omitted from the selector table. -/
structure BoundaryReferenceUse where
  references : BoundaryExpressionReferences
  used : Array MVarId
  dependencies : Array MVarId
  levelDependencies : Array LMVarId

private partial def directMVars (e : Expr) : StateM (ExprStructMap Unit × Array MVarId) Unit := do
  if (← get).1.contains ⟨e⟩ then return
  modify fun (seen, ids) => (seen.insert ⟨e⟩ (), ids)
  match e with
  | .mvar id => modify fun (seen, ids) => (seen, if ids.contains id then ids else ids.push id)
  | .app f a => directMVars f; directMVars a
  | .lam _ t b _ | .forallE _ t b _ => directMVars t; directMVars b
  | .letE _ t v b _ => directMVars t; directMVars v; directMVars b
  | .mdata _ b | .proj _ _ b => directMVars b
  | _ => pure ()

def protectBoundaryReferences (refs : BoundaryExpressionReferences)
    (expressions : Array Expr) : MetaM BoundaryReferenceUse := do
  let (_, (_, used)) := (expressions.forM directMVars).run ({}, #[])
  for id in used do
    let some index := refs.mvars.findIdx? (· == id) | throwError "boundary_reference_not_preexisting"
    discard <| refs.resolve index
  let (dependencies, levelDependencies) ← runGraph refs.before none {} (used.map mkMVar)
  return {references := refs, used, dependencies, levelDependencies}

def BoundaryReferenceUse.checkContext (use : BoundaryReferenceUse) (current : MetavarContext) : MetaM Unit := do
  for id in use.dependencies do
    unless unchangedMVar use.references.before current id do
      throwError "boundary_reference_dependency_changed"

  for id in use.levelDependencies do
    let some before := use.references.before.lDecls.find? id | throwError "boundary_reference_unknown_level"
    let some after := current.lDecls.find? id | throwError "boundary_reference_unknown_level"
    unless before.depth == after.depth && before.index == after.index &&
        use.references.before.lAssignment.find? id == current.lAssignment.find? id do
      throwError "boundary_reference_level_changed"

def BoundaryReferenceUse.checkUnchanged (use : BoundaryReferenceUse) : MetaM Unit := do
  use.checkContext (← getMCtx)

/-- Type validation is observational for reference-bearing evidence. Never
    infer an assignment for a protected pre-boundary hole. -/
def withBoundaryReferenceValidation (use : BoundaryReferenceUse) (action : MetaM α) : MetaM α := do
  if use.used.isEmpty then return ← action
  use.checkUnchanged
  let core ← getThe Core.State
  let metaState ← getThe Meta.State
  try
    withoutBoundaryPendingSynthesis <| withNewMCtxDepth action
  finally
    modifyThe Core.State fun _ => core
    modifyThe Meta.State fun _ => metaState


/-- Must run before each method which internally assigns a target/local proof.
    The graph follows raw assignment, delayed fvar, type and context edges. -/
def BoundaryReferenceUse.checkAt (use : BoundaryReferenceUse) (destination : MVarId)
    (expressions : Array Expr) : MetaM Unit := do
  if use.used.isEmpty then return
  use.checkUnchanged
  let mctx ← getMCtx
  let some owner := mctx.decls.find? destination | throwError "boundary_reference_destination_missing"
  -- Check raw dependencies before any observational typing/unification.
  discard <| runGraph mctx (some destination) owner.lctx (expressions ++ use.used.map mkMVar)
  for id in use.used do
    let some decl := mctx.decls.find? id | throwError "boundary_reference_missing"
    -- Context compaction can renumber indices; pinned subprefix preserves the
    -- identity/order relation, not absolute slot numbers across contexts.
    unless decl.lctx.isSubPrefixOf owner.lctx do throwError "boundary_reference_scope_subprefix"
    let mut instancePosition := 0
    for expected in decl.localInstances do
      while instancePosition < owner.localInstances.size &&
          !(owner.localInstances[instancePosition]!.className == expected.className &&
            owner.localInstances[instancePosition]!.fvar.equal expected.fvar) do
        instancePosition := instancePosition + 1
      if instancePosition == owner.localInstances.size then throwError "boundary_reference_scope_instances"
      instancePosition := instancePosition + 1
    for localDecl in decl.lctx do
      let some actual := owner.lctx.find? localDecl.fvarId | throwError "boundary_reference_scope_missing"
      unless localDecl.kind == actual.kind && localDecl.binderInfo == actual.binderInfo &&
          localDecl.isLet (allowNondep := true) == actual.isLet (allowNondep := true) do
        throwError "boundary_reference_scope_shape"
      match localDecl, actual with
      | .ldecl (nondep := a) .., .ldecl (nondep := b) .. =>
          unless a == b do throwError "boundary_reference_scope_nondep"
      | _, _ => pure ()
      let compatible ← withBoundaryReferenceValidation use <| withLCtx owner.lctx owner.localInstances do
        unless ← isDefEq localDecl.type actual.type do return false
        match localDecl.value? (allowNondep := true), actual.value? (allowNondep := true) with
        | some a, some b => isDefEq a b
        | none, none => pure true
        | _, _ => pure false
      unless compatible do throwError "boundary_reference_scope_type_or_value"


end ExplicitLean.SimpEngine.Boundary
