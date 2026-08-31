module
prelude

public meta import Lean.Meta.Basic
public meta import Lean.Meta.InferType
public meta import Lean.Data.Json
public meta import Lean.Elab.Term.TermElabM

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/-
  This module deliberately owns its fingerprint implementation.  In
  particular, it does not import the legacy recording/replay IR or any of the
  simplifier implementation modules.  The selector is an observation of the
  state at the boundary, not an observation of how a tactic reached it.
-/

private def digest (kind payload : String) : String :=
  s!"{kind}-v1:{hash payload}"

private def binderInfoTag : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private def localDeclKindTag : LocalDeclKind → String
  | .default => "default"
  | .implDetail => "implDetail"
  | .auxDecl => "auxDecl"

private def localDeclNondep : LocalDecl → Bool
  | .cdecl .. => false
  | .ldecl (nondep := nondep) .. => nondep

private def metavariableKindTag : MetavarKind → String
  | .natural => "natural"
  | .synthetic => "synthetic"
  | .syntheticOpaque => "syntheticOpaque"

/-
  The selector needs to distinguish states that have the same visible goals but
  differ in continuation-relevant bookkeeping.  These encoders deliberately
  use a length-prefixed representation rather than a human-readable printer:
  delimiters in names, syntax, or expressions therefore cannot make two
  different records share a payload.  The resulting payload is hashed before
  it is put on the wire.

  The routing-state portion below is a conservative observer of inputs that
  can affect the current simp execution.  It starts at the current goals and
  pending term work, then follows every expression and universe metavariable
  referenced by those roots.  Diagnostic tables, the global postponed queue,
  and other continuation state are checked by the result comparator instead of
  selecting a different simp outcome.  Mvars which were allocated by the
  surrounding elaborator but cannot affect this execution are deliberately
  ignored; their allocation order is not stable when the recorder and
  generated replacement have different syntax.  IDs are assigned encounter
  ordinals, never serialized directly.  Free-variable IDs are canonicalized by
  their local-declaration index, with an encounter ordinal only for genuinely
  free IDs.
-/

private def encodeField (value : String) : String :=
  s!"{value.length}:{value}"

private def encodeFields (tag : String) (fields : Array String) : String :=
  fields.foldl (init := encodeField tag) fun result field =>
    result ++ encodeField field

private def encodeList (tag : String) (fields : List String) : String :=
  encodeFields tag fields.toArray

private def encodeOption (f : α → String) : Option α → String
  | none => encodeFields "none" #[]
  | some value => encodeFields "some" #[f value]

private def rawName (name : Name) : String := name.toString

private def structuralName : Name → String
  | .anonymous => encodeFields "anonymous" #[]
  | .str parent component => encodeFields "str" #[structuralName parent, component]
  | .num parent component => encodeFields "num" #[structuralName parent, toString component]

private def declNameGeneratorPayload (generator : DeclNameGenerator) : String :=
  encodeFields "aux-decl-name-generator-v1" #[structuralName generator.namePrefix,
    toString generator.idx, encodeList "parents" (generator.parentIdxs.map toString)]

private structure BoundaryCanonicalIds where
  fvars : Std.HashMap FVarId String := {}
  nextFreeFVar : Nat := 0
  mvars : Std.HashMap MVarId String := {}
  nextFreeMVar : Nat := 0
  lmvars : Std.HashMap LMVarId String := {}
  nextFreeLMVar : Nat := 0
  mvarOrder : Array MVarId := #[]
  lmvarOrder : Array LMVarId := #[]
  missingMVars : Array MVarId := #[]
  missingLMVars : Array LMVarId := #[]
  observeRecAppPositions : Bool := false
  recAppPositions : Array Nat := #[]
  recAppPositionOrder? : Option (Array Nat) := none

private abbrev RawM := StateT BoundaryCanonicalIds MetaM

private def rawOptionM {α : Type} (f : α → RawM String) : Option α → RawM String
  | none => pure <| encodeFields "none" #[]
  | some value => do
      let encoded ← f value
      pure <| encodeFields "some" #[encoded]

private def rawFVarId (id : FVarId) : RawM String := do
  let state ← get
  if let some canonical := state.fvars.get? id then
    return canonical
  let canonical := encodeFields "fvar-free" #[toString state.nextFreeFVar]
  modify fun state => { state with
    fvars := state.fvars.insert id canonical
    nextFreeFVar := state.nextFreeFVar + 1 }
  return canonical

private def seedLocalFVar (id : FVarId) (index : Nat) : RawM Unit := do
  let state ← get
  if state.fvars.contains id then
    pure ()
  else
    -- Local declaration indices are stable across the recorder/materializer
    -- round trip.  Use the index directly, even when independently-created
    -- local contexts contain different FVarId values.
    let canonical := encodeFields "fvar-local" #[toString index]
    modify fun state => { state with fvars := state.fvars.insert id canonical }

private def rawMVarId (id : MVarId) : RawM String := do
  let state ← get
  if let some canonical := state.mvars.get? id then
    return canonical
  let ordinal := state.nextFreeMVar
  let canonical := encodeFields "mvar" #[toString ordinal]
  modify fun state => { state with
    mvars := state.mvars.insert id canonical
    nextFreeMVar := ordinal + 1
    mvarOrder := state.mvarOrder.push id }
  return canonical

private def rawLMVarId (id : LMVarId) : RawM String := do
  let state ← get
  if let some canonical := state.lmvars.get? id then
    return canonical
  let ordinal := state.nextFreeLMVar
  let canonical := encodeFields "lmvar" #[toString ordinal]
  modify fun state => { state with
    lmvars := state.lmvars.insert id canonical
    nextFreeLMVar := ordinal + 1
    lmvarOrder := state.lmvarOrder.push id }
  return canonical

private def rawBinderInfo (binderInfo : BinderInfo) : String := binderInfoTag binderInfo

/-- Only pending-recursion routing quotients relocation of pinned recursive-call
    diagnostics. All other metadata remains intact. Ranking positions preserves
    equality, distinctness, and source order without binding byte offsets. -/
private def rawExprMetadata (data : MData) : RawM String := do
  unless (← get).observeRecAppPositions do return toString data
  let syntaxEntries := data.entries.filter (·.1 == `_recApp)
  let positionEntries := data.entries.filter (·.1 == `_recAppPos)
  if syntaxEntries.isEmpty && positionEntries.isEmpty then return toString data
  unless syntaxEntries.length == 1 do
    throwError "boundary_selector_invalid_rec_app_metadata"
  let some (.ofSyntax recSyntax) := data.find `_recApp
    | throwError "boundary_selector_invalid_rec_app_metadata"
  match recSyntax.getPos?, positionEntries with
  | none, [] => return toString data
  | some position, [(_, .ofNat offset)] =>
      unless position.byteIdx == offset do
        throwError "boundary_selector_invalid_rec_app_metadata"
      match (← get).recAppPositionOrder? with
      | none =>
          unless (← get).recAppPositions.contains offset do
            modify fun state => {state with recAppPositions := state.recAppPositions.push offset}
          return toString data
      | some positions =>
          let some ordinal := positions.findIdx? (· == offset)
            | throwError "boundary_selector_rec_app_position_domain_changed"
          return encodeFields "rec-app-source-order-v1" #[toString (data.setNat `_recAppPos ordinal)]
  | _, _ => throwError "boundary_selector_invalid_rec_app_metadata"

private def rawLiteral : Literal → String
  | .natVal value => encodeFields "natVal" #[toString value]
  | .strVal value => encodeFields "strVal" #[value]

private def observingMetaState (action : MetaM α) : MetaM α := do
  let core ← getThe Core.State
  let metaState ← getThe Meta.State
  try action finally
    modifyThe Core.State fun _ => core
    modifyThe Meta.State fun _ => metaState

mutual

private partial def rawMVarRoot (id : MVarId) : RawM String := do
  let mctx ← getMCtx
  match mctx.eAssignment.find? id with
  | some value =>
      pure <| encodeFields "assigned-root" #[← rawExpr value]
  | none => match mctx.dAssignment.find? id with
    | some assignment =>
        let id ← rawMVarId id
        let fvars ← assignment.fvars.mapM rawExpr
        let pending ← rawMVarRoot assignment.mvarIdPending
        pure <| encodeFields "delayed-root" #[id,
          encodeFields "fvars" fvars, pending]
    | none =>
        pure <| encodeFields "unassigned-root" #[← rawMVarId id]

private partial def rawLevel (input : Level) : RawM String := do
  let input ← instantiateLevelMVars input
  match input with
  | .zero => pure <| encodeFields "zero" #[]
  | .succ level => do
      let level ← rawLevel level
      pure <| encodeFields "succ" #[level]
  | .max lhs rhs => do
      let lhs ← rawLevel lhs
      let rhs ← rawLevel rhs
      pure <| encodeFields "max" #[lhs, rhs]
  | .imax lhs rhs => do
      let lhs ← rawLevel lhs
      let rhs ← rawLevel rhs
      pure <| encodeFields "imax" #[lhs, rhs]
  | .param name => pure <| encodeFields "param" #[rawName name]
  | .mvar id => do
      let id ← rawLMVarId id
      pure <| encodeFields "mvar" #[id]

private partial def rawExpr (input : Expr) : RawM String := do
  let input ← instantiateMVars input
  match input with
  | .bvar index => pure <| encodeFields "bvar" #[toString index]
  | .fvar id => do
      let id ← rawFVarId id
      pure <| encodeFields "fvar" #[id]
  | .mvar id => do
      let id ← rawMVarRoot id
      pure <| encodeFields "mvar" #[id]
  | .sort level => do
      let level ← rawLevel level
      pure <| encodeFields "sort" #[level]
  | .const name levels => do
      let levels ← levels.mapM rawLevel
      pure <| encodeFields "const" #[rawName name, encodeList "levels" levels]
  | .app function argument => do
      let function ← rawExpr function
      let argument ← rawExpr argument
      pure <| encodeFields "app" #[function, argument]
  | .lam _ type body binderInfo => do
      let type ← rawExpr type
      let body ← rawExpr body
      pure <| encodeFields "lam" #[type, body, rawBinderInfo binderInfo]
  | .forallE _ type body binderInfo => do
      let type ← rawExpr type
      let body ← rawExpr body
      pure <| encodeFields "forallE" #[type, body, rawBinderInfo binderInfo]
  | .letE _ type value body nondep => do
      let type ← rawExpr type
      let value ← rawExpr value
      let body ← rawExpr body
      pure <| encodeFields "letE" #[type, value, body, toString nondep]
  | .lit literal => pure <| encodeFields "lit" #[rawLiteral literal]
  | .mdata data child => do
      let child ← rawExpr child
      pure <| encodeFields "mdata" #[← rawExprMetadata data, child]
  | .proj name index child => do
      let child ← rawExpr child
      pure <| encodeFields "proj" #[rawName name, toString index, child]

end

private def rawLocalDecl (decl : LocalDecl) : RawM String := do
  let fvarId ← rawFVarId decl.fvarId
  match decl with
  | .cdecl index _ _ type binderInfo kind =>
      let type ← rawExpr type
      -- Local declaration names are presentation-only.  The visible state
      -- already identifies a local by its stable declaration index, so a
      -- theorem-parameter alpha rename must not invalidate a selector.
      return encodeFields "cdecl" #[toString index, fvarId,
        type, rawBinderInfo binderInfo, localDeclKindTag kind]
  | .ldecl index _ _ type value nondep kind =>
      let type ← rawExpr type
      let value ← rawExpr value
      return encodeFields "ldecl" #[toString index, fvarId,
        type, value, toString nondep, localDeclKindTag kind]

private def rawLocalContext (lctx : LocalContext) : RawM String := do
  for decl? in lctx.decls.toArray do
    if let some decl := decl? then
      seedLocalFVar decl.fvarId decl.index
  let decls ← lctx.decls.toArray.mapM fun decl? =>
    match decl? with
    | none => pure <| encodeFields "empty" #[]
    | some decl => rawLocalDecl decl
  let auxDecls := lctx.auxDeclToFullName.toList.toArray
    |>.qsort (fun lhs rhs => toString lhs.1.name < toString rhs.1.name)
  let auxDecls ← auxDecls.mapM fun (fvarId, fullName) => do
    let fvarId ← rawFVarId fvarId
    return encodeFields "aux" #[fvarId, rawName fullName]
  return encodeFields "local-context" #[encodeFields "decls" decls,
    encodeFields "aux-decls" auxDecls]

private def rawLocalInstances (instances : LocalInstances) : RawM String := do
  let encoded ← instances.mapM fun localInstance => do
    let fvar ← rawExpr localInstance.fvar
    return encodeFields "instance" #[rawName localInstance.className, fvar]
  pure <| encodeFields "local-instances" encoded

private def rawMetavarKind : MetavarKind → String := metavariableKindTag

private def rawMetavarDecl (decl : MetavarDecl) : RawM String := do
  let lctx ← rawLocalContext decl.lctx
  let type ← rawExpr decl.type
  let instances ← rawLocalInstances decl.localInstances
  -- Goal names affect tactic presentation/routing such as `case`, but not the
  -- behavior of simp on this goal.  The unchanged continuation and result
  -- comparator remain responsible for preserving that externally visible
  -- state.
  return encodeFields "metavar-decl" #[lctx, type,
    toString decl.depth, instances, rawMetavarKind decl.kind,
    toString decl.numScopeArgs]

private def rawLevelMetavarDecl (decl : LevelMetavarDecl) : String :=
  encodeFields "level-metavar-decl" #[toString decl.depth]

private def rawMessageDataShape (message : MessageData) : String :=
  -- Message wording and lazy formatting are diagnostics, not execution state.
  encodeFields "message-data" #[rawName (MessageData.kind message),
    toString (MessageData.isTrace message)]

private def syntaxPreresolvedDescriptor : Syntax.Preresolved → String
  | .namespace namespaceName =>
      encodeFields "namespace" #[rawName namespaceName]
  | .decl declarationName fields =>
      encodeFields "declaration" #[rawName declarationName,
        encodeList "fields" fields]

/- SourceInfo is deliberately omitted here: source positions and whitespace
   cannot affect the current simp execution selected by this key, and they
   necessarily move when the authored tactic is replaced.  The post-call
   comparator still checks the full pending Syntax values exactly. -/
private partial def syntaxStableDescriptor : Syntax → String
  | .missing => encodeFields "missing" #[]
  | .atom _ value => encodeFields "atom" #[value]
  | .ident _ rawValue value preresolved =>
      encodeFields "ident" #[Substring.Raw.Internal.toString rawValue,
        rawName value,
        encodeList "preresolved" (preresolved.map syntaxPreresolvedDescriptor)]
  | .node _ kind arguments =>
      encodeFields "node" #[rawName kind,
        encodeFields "arguments" (arguments.map syntaxStableDescriptor)]

private def rawMacroStack (stack : Lean.Elab.MacroStack) : String :=
  encodeList "macro-stack" <| stack.map fun entry =>
    encodeFields "macro" #[syntaxStableDescriptor entry.before,
      syntaxStableDescriptor entry.after]

private def rawSavedContext (context : Lean.Elab.Term.SavedContext) : String :=
  encodeFields "saved-context" #[encodeOption rawName context.declName?,
    toString context.options, encodeList "open-decls" (context.openDecls.map toString),
    rawMacroStack context.macroStack, toString context.errToSorry,
    encodeList "level-names" (context.levelNames.map rawName),
    toString context.fixedTermElabs.size]

private def savedContextHasOpaqueFixedTermElabs
    (context : Lean.Elab.Term.SavedContext) : Bool :=
  !context.fixedTermElabs.isEmpty

private def rawTacticMVarKind : Lean.Elab.Term.TacticMVarKind → String
  | .term => encodeFields "term" #[]
  | .autoParam argName => encodeFields "auto-param" #[rawName argName]
  | .fieldAutoParam fieldName structName =>
      encodeFields "field-auto-param" #[rawName fieldName, rawName structName]

private def rawSyntheticMVarKind : Lean.Elab.Term.SyntheticMVarKind → RawM String
  | .typeClass extraErrorMsg? =>
      pure <| encodeFields "type-class" #[encodeOption rawMessageDataShape extraErrorMsg?]
  | .coe header? expectedType expression function? mkErrorMsg? => do
      let expectedType ← rawExpr expectedType
      let expression ← rawExpr expression
      let function ← rawOptionM rawExpr function?
      return encodeFields "coe" #[encodeOption id header?, expectedType,
        expression, function, toString mkErrorMsg?.isSome]
  | .tactic tacticCode context kind delayOnMVars =>
      pure <| encodeFields "tactic" #[syntaxStableDescriptor tacticCode,
        rawSavedContext context,
        rawTacticMVarKind kind, toString delayOnMVars]
  | .postponed context => pure <| encodeFields "postponed" #[rawSavedContext context]

private def syntheticMVarKindHasOpaqueFixedTermElabs
    : Lean.Elab.Term.SyntheticMVarKind → Bool
  | .typeClass _ => false
  | .coe _ _ _ _ _ => false
  | .tactic _ context _ _ => savedContextHasOpaqueFixedTermElabs context
  | .postponed context => savedContextHasOpaqueFixedTermElabs context

private def termStateHasOpaqueFixedTermElabs
    (state : Lean.Elab.Term.State) : Bool :=
  state.pendingMVars.any fun id =>
    match state.syntheticMVars.toList.find? (fun entry => entry.1 == id) with
    | none => false
    | some (_, decl) => syntheticMVarKindHasOpaqueFixedTermElabs decl.kind

private def rawSyntheticMVarDecl (decl : Lean.Elab.Term.SyntheticMVarDecl) : RawM String := do
  let kind ← rawSyntheticMVarKind decl.kind
  return encodeFields "synthetic-mvar-decl" #[syntaxStableDescriptor decl.stx, kind]

private def rawTerminationBy (terminationBy : Lean.Elab.TerminationBy) : String :=
  encodeFields "termination-by" #[toString terminationBy.ref,
    toString terminationBy.structural,
    encodeList "vars" (terminationBy.vars.toList.map toString),
    toString terminationBy.body, toString terminationBy.synthetic]

private def rawPartialFixpoint (partialFixpoint : Lean.Elab.PartialFixpoint) : String :=
  let kind := match partialFixpoint.fixpointType with
    | .partialFixpoint => "partial"
    | .coinductiveFixpoint => "coinductive"
    | .inductiveFixpoint => "inductive"
  encodeFields "partial-fixpoint" #[toString partialFixpoint.ref,
    encodeOption toString partialFixpoint.term?, kind]

private def rawDecreasingBy (decreasingBy : Lean.Elab.DecreasingBy) : String :=
  encodeFields "decreasing-by" #[toString decreasingBy.ref, toString decreasingBy.tactic]

private def rawTerminationHints (hints : Lean.Elab.TerminationHints) : String :=
  encodeFields "termination-hints" #[toString hints.ref,
    encodeOption toString hints.terminationBy??,
    encodeOption rawTerminationBy hints.terminationBy?,
    encodeOption rawPartialFixpoint hints.partialFixpoint?,
    encodeOption rawDecreasingBy hints.decreasingBy?, toString hints.extraParams]

private def rawAttribute (attr : Lean.Elab.Attribute) : String :=
  encodeFields "attribute" #[toString attr.kind, rawName attr.name, toString attr.stx]

private def rawLetRecToLift (entry : Lean.Elab.Term.LetRecToLift) : RawM String := do
  let fvarId ← rawFVarId entry.fvarId
  let lctx ← rawLocalContext entry.lctx
  let instances ← rawLocalInstances entry.localInstances
  let type ← rawExpr entry.type
  let value ← rawExpr entry.val
  let mvarId ← rawMVarRoot entry.mvarId
  return encodeFields "let-rec" #[toString entry.ref, fvarId,
    encodeList "attributes" (entry.attrs.toList.map rawAttribute),
    rawName entry.shortDeclName, rawName entry.declName,
    encodeOption rawName entry.parentName?, lctx, instances, type, value, mvarId,
    rawTerminationHints entry.termination, toString entry.binders,
    encodeOption (fun doc => encodeFields "doc" #[toString doc.1, toString doc.2])
      entry.docString?]

private def orderedPendingSyntheticEntries
    (state : Lean.Elab.Term.State) : Array (MVarId × Lean.Elab.Term.SyntheticMVarDecl) :=
  state.pendingMVars.toArray.filterMap fun id =>
    state.syntheticMVars.toList.find? (fun entry => entry.1 == id)

private def rawDelayedAssignment (assignment : DelayedMetavarAssignment) : RawM String := do
  let fvars ← assignment.fvars.mapM rawExpr
  let pending ← rawMVarRoot assignment.mvarIdPending
  pure <| encodeFields "delayed" #[encodeFields "fvars" fvars, pending]

private def rawMVarAliases (mctx : MetavarContext) (id : MVarId) : String :=
  let names := mctx.userNames.toList.filter (·.2 == id) |>.map fun entry => rawName entry.1
  encodeList "user-names" names

private def rawMVarRecords (mctx : MetavarContext)
    (visibleGoals : Std.HashSet MVarId) : RawM (Array String) := do
  let mut records := #[]
  let mut next := 0
  while next < (← get).mvarOrder.size do
    let id := (← get).mvarOrder[next]!
    next := next + 1
    match mctx.decls.find? id with
    | none =>
        modify fun state => { state with missingMVars := state.missingMVars.push id }
    | some decl =>
        let declaration ← rawMetavarDecl decl
        let assignment ← match mctx.eAssignment.find? id with
          | none => pure <| encodeFields "none" #[]
          | some value => do
              let value ← rawExpr value
              pure <| encodeFields "some" #[value]
        let delayed ← match mctx.dAssignment.find? id with
          | none => pure <| encodeFields "none" #[]
          | some value => pure <| encodeFields "some" #[(← rawDelayedAssignment value)]
        /- The public goal fingerprint below already covers an active goal's
           target, context, instances, and declaration metadata using the
           proof-insensitive canonical expression policy.  Walking its raw
           declaration above is still necessary to discover nested mvars, but
           serializing it again would make routing depend on proof terms and
           internal goal names. -/
        let isOrdinaryVisibleGoal := visibleGoals.contains id &&
          !mctx.dAssignment.contains id
        unless isOrdinaryVisibleGoal do
          let canonical ← rawMVarId id
          records := records.push <| encodeFields "mvar-record-v1" #[canonical,
            digest "selector-mvar-aliases" (rawMVarAliases mctx id),
            digest "selector-mvar-declaration" declaration,
            digest "selector-mvar-assignment" assignment,
            digest "selector-mvar-delayed" delayed]
  pure records

private def rawLMVarRecords (mctx : MetavarContext) : RawM (Array String) := do
  let mut records := #[]
  let mut next := 0
  while next < (← get).lmvarOrder.size do
    let id := (← get).lmvarOrder[next]!
    next := next + 1
    match mctx.lDecls.find? id with
    | none =>
        modify fun state => { state with missingLMVars := state.missingLMVars.push id }
    | some decl =>
        let assignment ← match mctx.lAssignment.find? id with
          | none => pure <| encodeFields "none" #[]
          | some value => pure <| encodeFields "some" #[(← rawLevel value)]
        let canonical ← rawLMVarId id
        records := records.push <| encodeFields "lmvar-record-v1" #[canonical,
          digest "selector-lmvar-declaration" (rawLevelMetavarDecl decl),
          digest "selector-lmvar-assignment" assignment]
  pure records

private def rawTermRoots (state : Lean.Elab.Term.State) : RawM String := do
  -- `pendingMVars` is Lean's authoritative ordered work list.  `Tactic.run`
  -- temporarily removes dormant sibling work from that list while the active
  -- tactic executes, leaving its table entries as non-routable bookkeeping.
  let pendingMVars ← state.pendingMVars.toArray.mapM rawMVarRoot
  let syntheticMVars ← (orderedPendingSyntheticEntries state).mapM fun (id, decl) => do
    let id ← rawMVarRoot id
    let decl ← rawSyntheticMVarDecl decl
    pure <| encodeFields "synthetic" #[id, decl]
  let letRecs ← state.letRecsToLift.mapM rawLetRecToLift
  let result := encodeFields "term-roots-v1" #[
    encodeFields "pending" #[toString pendingMVars.size,
      digest "selector-pending-mvars" (encodeFields "pending-mvars" pendingMVars)],
    encodeFields "synthetic" #[toString syntheticMVars.size,
      digest "selector-synthetic-mvars" (encodeFields "synthetic-mvars" syntheticMVars)],
    encodeFields "let-recs" #[toString letRecs.length,
      digest "selector-let-recs" (encodeList "let-recs-to-lift" letRecs)]]
  pure result

private def rawSelectorState (goals : List MVarId)
    (termState? : Option (Lean.Elab.Term.State)) : MetaM (String × BoundaryCanonicalIds) := do
  if let some termState := termState? then
    if termStateHasOpaqueFixedTermElabs termState then
      throwError "boundary_selector_opaque_fixed_term_elabs"
  let mctx ← getMCtx
  let action : RawM String := do
    -- The root order is part of the canonical traversal: current goals,
    -- pending/synthetic term work, then let-rec roots.  Referenced
    -- declarations are appended exactly once as the queue is drained below.
    let goalRoots ← goals.toArray.mapM fun goal => do
      let id ← rawMVarRoot goal
      pure <| encodeFields "goal" #[id]
    let termRoots ← match termState? with
      | none => pure <| encodeFields "term-state-absent" #[]
      | some state => rawTermRoots state
    let visibleGoals := goals.foldl (init := {}) fun result goal => result.insert goal
    let mvarRecords ← rawMVarRecords mctx visibleGoals
    let lmvarRecords ← rawLMVarRecords mctx
    let result := encodeFields "selector-state-v1" #[
      encodeFields "depth" #[toString mctx.depth],
      encodeFields "level-assign-depth" #[toString mctx.levelAssignDepth],
      digest "selector-goal-roots" (encodeFields "goals" goalRoots),
      termRoots,
      encodeFields "selector-mvars" mvarRecords,
      encodeFields "selector-lmvars" lmvarRecords]
    return result
  -- Nonempty pending recursion was previously rejected by the boundary guard.
  -- Preserve existing selector bytes for every empty-list state. Only this new
  -- domain needs a second observation pass to rank all distinct source sites.
  let initial : BoundaryCanonicalIds := {
    observeRecAppPositions := termState?.any (fun state => !state.letRecsToLift.isEmpty) }
  let (payload, state) ← action.run initial
  let (payload, state) ← if state.recAppPositions.isEmpty then pure (payload, state) else
    action.run {initial with recAppPositionOrder? := some (state.recAppPositions.qsort (· < ·))}
  unless state.missingMVars.isEmpty do
    throwError "boundary_selector_unknown_reachable_mvar"
  unless state.missingLMVars.isEmpty do
    throwError "boundary_selector_unknown_reachable_level_mvar"
  pure (payload, state)

private def rawSelectorStatePayload (goals : List MVarId)
    (termState? : Option (Lean.Elab.Term.State)) : MetaM String := do
  return (← rawSelectorState goals termState?).1

/-- Reachable universe identities in the selector's canonical encounter order.
The caller must take this observation before executing or decoding a boundary.
Global allocation order and unreachable metavariables are deliberately absent. -/
def boundaryUniverseReferences (goals : List MVarId)
    (termState : Lean.Elab.Term.State) : MetaM (Array LMVarId) := do
  let goals ← goals.filterM fun goal => return !(← goal.isAssigned)
  return (← rawSelectorState goals (some termState)).2.lmvarOrder

private structure CanonicalState where
  exprMVars : Std.HashMap MVarId Nat := {}
  levelMVars : Std.HashMap LMVarId Nat := {}
  freeFVars : Std.HashMap FVarId Nat := {}
  nextExprMVar : Nat := 0
  nextLevelMVar : Nat := 0
  nextFreeFVar : Nat := 0
  exprHashes : ExprStructMap UInt64 := {}
  levelHashes : Std.HashMap Level UInt64 := {}

private abbrev CanonicalM := StateT CanonicalState MetaM

private partial def canonicalLevelHash (level : Level) : CanonicalM UInt64 := do
  if let some cached := (← get).levelHashes.get? level then
    return cached
  let result ← match level with
    | .zero => pure 211
    | .succ child =>
        return mixHash 223 (← canonicalLevelHash child)
    | .max lhs rhs =>
        return mixHash 227 (mixHash (← canonicalLevelHash lhs)
          (← canonicalLevelHash rhs))
    | .imax lhs rhs =>
        return mixHash 229 (mixHash (← canonicalLevelHash lhs)
          (← canonicalLevelHash rhs))
    | .param name => pure <| mixHash 233 (hash name)
    | .mvar id =>
        let state ← get
        if let some ordinal := state.levelMVars.get? id then
          pure <| mixHash 239 (hash ordinal)
        else
          let ordinal := state.nextLevelMVar
          modify fun state => { state with
            levelMVars := state.levelMVars.insert id ordinal
            nextLevelMVar := ordinal + 1 }
          pure <| mixHash 239 (hash ordinal)
  modify fun state => { state with
    levelHashes := state.levelHashes.insert level result }
  return result

/-
  Expression binders are represented with de Bruijn indices.  We therefore
  intentionally discard binder names below.  Bound free variables are assigned
  ordinals while walking the binder; ordinary free variables use their local
  declaration index, which is stable across regenerated contexts.

  When `eraseProofs` is true, every proof-valued subterm contributes the hash
  of its type only.  Proof constructors and private proof declaration names
  consequently cannot make two semantically identical boundary states select
  different variants.
-/
private partial def canonicalExprHash (lctx : LocalContext) (eraseProofs : Bool)
    (boundFVars : Array Expr) (boundOrdinals : Std.HashMap FVarId Nat)
    (expression : Expr) : CanonicalM UInt64 := do
  let expression ← liftM <| (instantiateMVars expression : MetaM Expr)
  let opened := if boundFVars.isEmpty then expression else
    expression.instantiateRev boundFVars
  if eraseProofs && (← liftM <| isProof opened) then
    let type ← liftM <| inferType opened
    return mixHash 293 <| ← canonicalExprHash lctx eraseProofs
      boundFVars boundOrdinals type
  let cacheable := !expression.hasLooseBVars
  if cacheable then
    if let some cached := (← get).exprHashes.get? expression then
      return cached
  let result ← match expression with
    | .bvar index => pure <| mixHash 307 (hash index)
    | .fvar id =>
        let state ← get
        if let some ordinal := boundOrdinals.get? id then
          pure <| mixHash 311 (hash ordinal)
        else if let some decl := lctx.find? id then
          pure <| mixHash 313 (hash decl.index)
        else if let some ordinal := state.freeFVars.get? id then
          pure <| mixHash 317 (hash ordinal)
        else
          let ordinal := state.nextFreeFVar
          modify fun state => { state with
            freeFVars := state.freeFVars.insert id ordinal
            nextFreeFVar := ordinal + 1 }
          pure <| mixHash 317 (hash ordinal)
    | .mvar id =>
        let state ← get
        if let some ordinal := state.exprMVars.get? id then
          pure <| mixHash 319 (hash ordinal)
        else
          let ordinal := state.nextExprMVar
          modify fun state => { state with
            exprMVars := state.exprMVars.insert id ordinal
            nextExprMVar := ordinal + 1 }
          pure <| mixHash 319 (hash ordinal)
    | .sort level => pure <| mixHash 323 (← canonicalLevelHash level)
    | .const name levels => do
        let mut result := mixHash 331 (hash name)
        for level in levels do
          result := mixHash result (← canonicalLevelHash level)
        pure result
    | .app function argument =>
        pure <| mixHash 337 <| mixHash
          (← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals function)
          (← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals argument)
    | .lam name type body binderInfo | .forallE name type body binderInfo => do
        let typeHash ← canonicalExprHash lctx eraseProofs boundFVars
          boundOrdinals type
        let state ← get
        let openedType := type.instantiateRev boundFVars
        let (bodyHash, state) ← liftM <| withLocalDecl name binderInfo openedType fun x =>
          (canonicalExprHash lctx eraseProofs (boundFVars.push x)
            (boundOrdinals.insert x.fvarId! boundFVars.size) body).run state
        set state
        let tag := if expression.isLambda then 347 else 349
        pure <| mixHash tag <| mixHash (hash (binderInfoTag binderInfo)) <|
          mixHash typeHash bodyHash
    | .letE name type value body nondep => do
        let typeHash ← canonicalExprHash lctx eraseProofs boundFVars
          boundOrdinals type
        let valueHash ← canonicalExprHash lctx eraseProofs boundFVars
          boundOrdinals value
        let state ← get
        let openedType := type.instantiateRev boundFVars
        let openedValue := value.instantiateRev boundFVars
        let (bodyHash, state) ← liftM <| withLetDecl name openedType openedValue
          (nondep := nondep) fun x =>
            (canonicalExprHash lctx eraseProofs (boundFVars.push x)
              (boundOrdinals.insert x.fvarId! boundFVars.size) body).run state
        set state
        pure <| mixHash 353 <| mixHash (hash nondep) <|
          mixHash typeHash <| mixHash valueHash bodyHash
    | .lit literal => pure <| mixHash 359 (hash literal)
    | .mdata _ child =>
        canonicalExprHash lctx eraseProofs boundFVars boundOrdinals child
    | .proj name index child =>
        pure <| mixHash 367 <| mixHash (hash name) <|
          mixHash (hash index)
            (← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals child)
  if cacheable then
    modify fun state => { state with
      exprHashes := state.exprHashes.insert expression result }
  return result

private def runCanonicalHash (lctx : LocalContext) (expression : Expr)
    (state : CanonicalState := {}) : MetaM (UInt64 × CanonicalState) := do
  observingMetaState do
    withLCtx lctx (← getLocalInstances) do
      (canonicalExprHash lctx true #[] {} expression).run state

/-- A canonical, ordered fingerprint of one open-goal proof state.

The field names intentionally match the legacy state observer so reports and
diagnostics remain easy to compare while the implementation stays independent
of the legacy recording/replay modules. -/
structure BoundaryStateFingerprint where
  targetFingerprint : String
  localContextFingerprint : String
  metavariableContextFingerprint : String
  goalCount : Nat
  deriving Inhabited, Repr, BEq, Lean.ToJson

abbrev StateFingerprint := BoundaryStateFingerprint

private def localDeclFingerprint (decl : LocalDecl) (state : CanonicalState) :
    MetaM (String × CanonicalState) := do
  let (typeHash, state) ← runCanonicalHash (← getLCtx) decl.type state
  let (valueHash?, state) ← match decl.value? (allowNondep := true) with
    | none => pure (none, state)
    | some value =>
        let (valueHash, state) ← runCanonicalHash (← getLCtx) value state
        pure (some valueHash, state)
  -- User names are intentionally omitted: theorem-parameter alpha-renaming is
  -- an allowed materialization fallback, while declaration order/index keeps
  -- the ordered context and all expression references stable.
  pure (s!"{decl.index}:{binderInfoTag decl.binderInfo}:" ++
    s!"{localDeclKindTag decl.kind}:{localDeclNondep decl}:" ++
    s!"{typeHash}:{valueHash?}", state)

private def goalFingerprint (goal : MVarId) (state : CanonicalState) :
    MetaM (String × String × String × CanonicalState) :=
  goal.withContext do
    let decl ← goal.getDecl
    let (targetHash, state) ← runCanonicalHash decl.lctx decl.type state
    let mut locals := #[]
    let mut state := state
    for localDecl in decl.lctx do
      let (fingerprint, nextState) ← localDeclFingerprint localDecl state
      locals := locals.push fingerprint
      state := nextState
    let mut instances := #[]
    for localInstance in decl.localInstances do
      let (instanceHash, nextState) ← runCanonicalHash decl.lctx
        localInstance.fvar state
      instances := instances.push s!"{localInstance.className}:{instanceHash}"
      state := nextState
    let context := String.intercalate "|" locals.toList
    let metavariable := s!"{decl.depth}:{metavariableKindTag decl.kind}:{decl.numScopeArgs}:" ++
      String.intercalate "|" instances.toList
    pure (s!"{targetHash}", context, metavariable, state)

private def proofStateFingerprintImpl (goals : List MVarId)
    (termState? : Option (Lean.Elab.Term.State) := none) :
    MetaM BoundaryStateFingerprint := do
  let generator := declNameGeneratorPayload (← getDeclNGen)
  -- Lean tactic combinators define the active proof state by its unsolved
  -- goals; assigned entries can remain transiently in `Tactic.State.goals`
  -- until the surrounding evaluator prunes them.  Recorder and generated
  -- syntax can trigger that pruning at different instants, so canonicalize it
  -- here just as `Tactic.getUnsolvedGoals` does at the tactic boundary.
  let goals ← goals.filterM fun goal => return !(← goal.isAssigned)
  -- Capture the continuation graph before any presentation-oriented hashing.
  -- Canonical expression hashing may ask the kernel/meta layer proof/type
  -- questions; each such query is isolated below, but ordering the raw state
  -- first also makes this invariant explicit.
  let completeState ← rawSelectorStatePayload goals termState?
  let mut targets := #[]
  let mut contexts := #[]
  let mut metavariables := #[]
  let mut state : CanonicalState := {}
  for goal in goals do
    unless (← goal.isAssigned) do
      let (target, context, metavariable, nextState) ← goalFingerprint goal state
      targets := targets.push target
      contexts := contexts.push context
      metavariables := metavariables.push metavariable
      state := nextState
  return {
    targetFingerprint := digest "targets" (String.intercalate "|" targets.toList)
    localContextFingerprint := digest "goal-contexts"
      (String.intercalate "|" contexts.toList)
    metavariableContextFingerprint := encodeFields "metavariable-context-v2" #[
      digest "selector-visible-goals" (encodeList "goals" metavariables.toList),
      digest "selector-complete-state" completeState,
      digest "selector-aux-decl-name-generator" generator]
    goalCount := targets.size
  }

/-- Observe the canonical expression hash without changing meta/elaboration state. -/
def boundaryExprFingerprintHash (expression : Expr) : MetaM String :=
  observingMetaState do
    let expression ← instantiateMVars expression
    let (fingerprint, _) ← (canonicalExprHash (← getLCtx) true #[] {}
      expression).run {}
    return s!"boundary-expr-v1:{fingerprint}"

/-- Observe the ordered open goals and their visible contexts without changing state. -/
def boundaryProofStateFingerprint (goals : List MVarId) :
    MetaM BoundaryStateFingerprint :=
  observingMetaState <| proofStateFingerprintImpl goals

/-
  `MetaM` is deliberately not given access to the enclosing `Term.State`.
  Callers that run at the elaborator/tactic boundary should use this helper,
  passing the outer term state they observed at that same boundary.  Keeping
  the original MetaM API above is useful for metaprograms that have no term
  state, while this variant prevents pending/postponed elaboration work from
  being silently omitted by the production selector.
-/
def boundaryProofStateFingerprintWithTerm (goals : List MVarId)
    (termState : Lean.Elab.Term.State) : MetaM BoundaryStateFingerprint :=
  observingMetaState <| proofStateFingerprintImpl goals (some termState)

def boundaryTermStateFingerprint (termState : Lean.Elab.Term.State) : MetaM String :=
  observingMetaState <| do
    let payload ← rawSelectorStatePayload [] (some termState)
    pure <| digest "boundary-term-state" payload

/-- Return a deterministic fingerprint of the complete scoped `Options` map. -/
def boundaryOptionsFingerprint (options : Options) : String :=
  digest "boundary-options" (toString options)

/-- Canonicalize the enclosing declaration used by a boundary selector. Private
declaration prefixes and elaborator macro scopes are implementation details and
must not make the same authored caller select a different variant. -/
def boundaryCallerIdentity (caller : Name) : String :=
  (privateToUserName caller).eraseMacroScopes.toString

/-- Render an optional enclosing declaration for the guard syntax. An absent
caller is represented by the empty string. -/
def boundaryCallerIdentity? (caller? : Option Name) : String :=
  caller?.map boundaryCallerIdentity |>.getD ""

/- Compatibility aliases for callers that already live in the Boundary namespace. -/
def proofStateFingerprint (goals : List MVarId) : MetaM BoundaryStateFingerprint :=
  boundaryProofStateFingerprint goals

def optionsFingerprint (options : Options) : String :=
  boundaryOptionsFingerprint options

end ExplicitLean.SimpEngine.Boundary
