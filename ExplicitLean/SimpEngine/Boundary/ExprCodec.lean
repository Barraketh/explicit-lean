module
prelude

public meta import Lean.Meta.Basic
public meta import Lean.Data.Json.FromToJson

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/- Diagnostic prototype: a closed expression language. No parser extensions,
   term elaborators, tactics, instance synthesis, or coercion insertion run
   during decoding. Sharing keeps repeated dictionaries compact. Unresolved
   metavariables are rejected until a boundary-relative reference is defined. -/

def encodeBoundaryName : Name → Json
  | .anonymous => .arr #[]
  | name => .arr (parts name)
where
  parts : Name → Array Json
    | .anonymous => #[]
    | .str parent value => (parts parent).push (.arr #[.str "s", .str value])
    | .num parent value => (parts parent).push (.arr #[.str "n", toJson value])

def decodeBoundaryName (json : Json) : Except String Name := do
  (← json.getArr?).foldlM (init := .anonymous) fun name part => do
    match part with
    | .arr #[.str "s", .str value] => return .str name value
    | .arr #[.str "n", value] => return .num name (← value.getNat?)
    | _ => throw "invalid expression name"

private partial def encodeLevel (references : Array LMVarId) (level : Level) : MetaM Json := do
  match ← instantiateLevelMVars level with
  | .zero => return .arr #[.str "z"]
  | .succ level => return .arr #[.str "s", ← encodeLevel references level]
  | .max lhs rhs => return .arr #[.str "max", ← encodeLevel references lhs, ← encodeLevel references rhs]
  | .imax lhs rhs => return .arr #[.str "imax", ← encodeLevel references lhs, ← encodeLevel references rhs]
  | .param name => return .arr #[.str "p", encodeBoundaryName name]
  | .mvar id =>
      let some index := references.findIdx? (· == id)
        | throwError "boundary_expr_unresolved_universe"
      return .arr #[.str "r", toJson index]

private def decodeLevel (references : Array LMVarId) : Nat → Json → Except String Level
  | 0, _ => throw "expression universe nesting limit exceeded"
  | _ + 1, .arr #[.str "z"] => return .zero
  | fuel + 1, .arr #[.str "s", level] => return .succ (← decodeLevel references fuel level)
  | fuel + 1, .arr #[.str "max", lhs, rhs] =>
      return .max (← decodeLevel references fuel lhs) (← decodeLevel references fuel rhs)
  | fuel + 1, .arr #[.str "imax", lhs, rhs] =>
      return .imax (← decodeLevel references fuel lhs) (← decodeLevel references fuel rhs)
  | _ + 1, .arr #[.str "p", name] => return .param (← decodeBoundaryName name)
  | _ + 1, .arr #[.str "r", index] => do
      let index ← index.getNat?
      let some id := references[index]? | throw "unknown boundary universe reference"
      return .mvar id
  | _, _ => throw "invalid expression universe"

private def encodeBinderInfo : BinderInfo → Json
  | .default => toJson (0 : Nat)
  | .implicit => toJson (1 : Nat)
  | .strictImplicit => toJson (2 : Nat)
  | .instImplicit => toJson (3 : Nat)

private def decodeBinderInfo (json : Json) : Except String BinderInfo := do
  match ← json.getNat? with
  | 0 => return .default
  | 1 => return .implicit
  | 2 => return .strictImplicit
  | 3 => return .instImplicit
  | _ => throw "invalid expression binder information"

private structure EncodeState where
  references : Array LMVarId := #[]
  nodes : Array Json := #[]
  memo : Std.HashMap Expr Nat := {}
  structural : Bool := false
  structuralMemo : ExprStructMap Nat := {}

private abbrev EncodeM := StateT EncodeState MetaM

private def encodeScalarMetadata (data : MData) : MetaM Json := do
  let entries ← data.entries.toArray.mapM fun (name, value) => do
    let value ← match value with
      | .ofString v => pure <| Json.arr #[.str "string", .str v]
      | .ofBool v => pure <| Json.arr #[.str "bool", .bool v]
      | .ofName v => pure <| Json.arr #[.str "name", encodeBoundaryName v]
      | .ofNat v => pure <| Json.arr #[.str "nat", toJson v]
      | .ofInt v => pure <| Json.arr #[.str "int", toJson v]
      | .ofSyntax _ => throwError "boundary_struct_expr_syntax_metadata_unsupported"
    pure <| Json.arr #[encodeBoundaryName name, value]
  return .arr entries

private def decodeScalarMetadata (json : Json) : Except String MData := do
  let entries ← (← json.getArr?).toList.mapM fun entry => do
    let .arr #[name, value] := entry | throw "invalid structural metadata entry"
    let value ← match value with
      | .arr #[.str "string", .str v] => pure <| DataValue.ofString v
      | .arr #[.str "bool", .bool v] => pure <| DataValue.ofBool v
      | .arr #[.str "name", v] => pure <| DataValue.ofName (← decodeBoundaryName v)
      | .arr #[.str "nat", v] => pure <| DataValue.ofNat (← v.getNat?)
      | .arr #[.str "int", v] => pure <| DataValue.ofInt (← v.getInt?)
      | _ => throw "unsupported structural metadata value"
    pure (← decodeBoundaryName name, value)
  -- Preserve list order and duplicate keys exactly; do not normalize a KVMap.
  return { entries }

private partial def encodeExpr (expr : Expr) : EncodeM Nat := do
  let state ← get
  let structural := state.structural
  let existing := if structural then state.structuralMemo[(⟨expr⟩ : ExprStructEq)]? else state.memo[expr]?
  if let some index := existing then
    return index
  if !structural then
    if let .mdata _ child := expr then
      return ← encodeExpr child
  let references := (← get).references
  let node : Json ← match expr with
    | .bvar index => pure <| .arr #[.str "b", toJson index]
    | .fvar id => do
        let some decl := (← getLCtx).find? id
          | throwError "boundary_expr_unknown_local"
        pure <| .arr #[.str "f", toJson decl.index]
    | .mvar _ => throwError "boundary_expr_unresolved_metavariable"
    | .sort level => do pure <| .arr #[.str "s", ← encodeLevel references level]
    | .const name levels => do pure <| .arr #[.str "c", encodeBoundaryName name, toJson (← levels.mapM (fun level => encodeLevel references level))]
    | .app fn arg => do pure <| .arr #[.str "a", toJson (← encodeExpr fn), toJson (← encodeExpr arg)]
    | .lam name type body info => do
        pure <| .arr #[.str "l", encodeBoundaryName name, encodeBinderInfo info,
          toJson (← encodeExpr type), toJson (← encodeExpr body)]
    | .forallE name type body info => do
        pure <| .arr #[.str "q", encodeBoundaryName name, encodeBinderInfo info,
          toJson (← encodeExpr type), toJson (← encodeExpr body)]
    | .letE name type value body nondep => do
        pure <| .arr #[.str "e", encodeBoundaryName name, toJson (← encodeExpr type),
          toJson (← encodeExpr value), toJson (← encodeExpr body), toJson nondep]
    | .lit (.natVal value) => pure <| .arr #[.str "n", toJson value]
    | .lit (.strVal value) => pure <| .arr #[.str "t", .str value]
    | .proj name index child => do
        pure <| .arr #[.str "p", encodeBoundaryName name, toJson index, toJson (← encodeExpr child)]
    | .mdata data child =>
        pure <| .arr #[.str "m", ← encodeScalarMetadata data, toJson (← encodeExpr child)]
  let index := (← get).nodes.size
  modify fun state => { state with
    nodes := state.nodes.push node
    memo := if structural then state.memo else state.memo.insert expr index
    structuralMemo := if structural then state.structuralMemo.insert ⟨expr⟩ index else state.structuralMemo }
  return index

def encodeBoundaryExpr (expr : Expr) : MetaM String := do
  let expr ← instantiateMVars expr
  let (root, state) ← (encodeExpr expr).run {}
  return (Json.arr #[.str "expr_dag_v1", .arr state.nodes, toJson root]).compress

private def validateUniverseReferences (references : Array LMVarId) : MetaM Unit := do
  let mctx ← getMCtx
  let mut seen : Std.HashSet LMVarId := {}
  for id in references do
    unless mctx.lDecls.contains id do
      throwError "boundary_expr_unknown_reference_universe"
    if seen.contains id then
      throwError "boundary_expr_duplicate_reference_universe"
    seen := seen.insert id

/-- Version two explicitly refers to the pre-boundary selector's reachable
universe variables. It neither creates variables nor infers their assignments. -/
def encodeBoundaryExprWithUniverses (expr : Expr) (references : Array LMVarId) :
    MetaM String := do
  validateUniverseReferences references
  let expr ← instantiateMVars expr
  let (root, state) ← (encodeExpr expr).run { references }
  return (Json.arr #[.str "expr_dag_v2", toJson references.size,
    .arr state.nodes, toJson root]).compress

private def childAt (nodes : Array Expr) (json : Json) : Except String Expr := do
  let index ← json.getNat?
  let some expr := nodes[index]? | throw "expression reference is not an earlier node"
  return expr

private def requireConstant (env : Environment) (name : Name) : Except String Unit := do
  if name == ``sorryAx then
    throw "expression contains forbidden sorryAx"
  -- A normal getConstVal/find? can execute a registered ReservedNameAction.
  -- Such generators are arbitrary metaprograms, so never realize them here.
  unless (env.find? name (skipRealize := true)).isSome do
    throw s!"expression constant is unavailable without generation: {name}"

private def decodeNode (env : Environment) (locals : Std.HashMap Nat FVarId)
    (references : Array LMVarId) (nodes : Array Expr) (json : Json) : Except String Expr := do
  match json with
  | .arr #[.str "b", index] => return mkBVar (← index.getNat?)
  | .arr #[.str "f", index] =>
      let index ← index.getNat?
      let some id := locals[index]?
        | throw "expression local index is unavailable"
      return mkFVar id
  | .arr #[.str "s", level] => return mkSort (← decodeLevel references 256 level)
  | .arr #[.str "c", name, levels] =>
      let name ← decodeBoundaryName name
      requireConstant env name
      return mkConst name (← (← levels.getArr?).toList.mapM (decodeLevel references 256))
  | .arr #[.str "a", fn, arg] => return mkApp (← childAt nodes fn) (← childAt nodes arg)
  | .arr #[.str "l", name, info, type, body] =>
      return mkLambda (← decodeBoundaryName name) (← decodeBinderInfo info) (← childAt nodes type) (← childAt nodes body)
  | .arr #[.str "q", name, info, type, body] =>
      return mkForall (← decodeBoundaryName name) (← decodeBinderInfo info) (← childAt nodes type) (← childAt nodes body)
  | .arr #[.str "e", name, type, value, body, nondep] =>
      return mkLet (← decodeBoundaryName name) (← childAt nodes type) (← childAt nodes value)
        (← childAt nodes body) (← nondep.getBool?)
  | .arr #[.str "n", value] => return .lit (.natVal (← value.getNat?))
  | .arr #[.str "t", .str value] => return .lit (.strVal value)
  | .arr #[.str "p", name, index, child] =>
      let name ← decodeBoundaryName name
      requireConstant env name
      return mkProj name (← index.getNat?) (← childAt nodes child)
  | _ => throw "invalid expression node"

private def decodeBoundaryExprCore (source : String)
    (references? : Option (Array LMVarId)) : MetaM Expr := do
  if source.utf8ByteSize > 64 * 1024 * 1024 then
    throwError "boundary_expr_decode_error: expression source size limit exceeded"
  let lctx ← getLCtx
  let env ← getEnv
  let result : Except String Expr := do
    let mut locals : Std.HashMap Nat FVarId := {}
    for decl in lctx do
      if locals.contains decl.index then
        throw "ambiguous expression local declaration index"
      locals := locals.insert decl.index decl.fvarId
    let json ← Json.parse source
    let (rawNodes, root) ← match references?, json with
      | none, .arr #[.str "expr_dag_v1", .arr rawNodes, root] => pure (rawNodes, root)
      | some refs, .arr #[.str "expr_dag_v2", count, .arr rawNodes, root] => do
          unless (← count.getNat?) == refs.size do
            throw "boundary universe reference count mismatch"
          pure (rawNodes, root)
      | _, _ => throw "invalid expression encoding"
    if rawNodes.size > 2000000 then
      throw "expression node count limit exceeded"
    let mut nodes := #[]
    for node in rawNodes do
      nodes := nodes.push (← decodeNode env locals (references?.getD #[]) nodes node)
    childAt nodes root
  match result with
  | .ok expr => return expr
  | .error error => throwError "boundary_expr_decode_error: {error}"

def decodeBoundaryExpr (source : String) : MetaM Expr :=
  decodeBoundaryExprCore source none

def decodeBoundaryExprWithUniverses (source : String) (references : Array LMVarId) :
    MetaM Expr := do
  validateUniverseReferences references
  decodeBoundaryExprCore source (some references)

/-- Exact closed syntax, including binder names/info and ordered scalar MData.
    ExprStructMap uses Expr.equal, not alpha equivalence or definitional equality.
    Existing expression tags retain their original metadata-erasing semantics. -/
def encodeBoundaryStructExpr (expr : Expr) : MetaM String := do
  if expr.hasFVar || expr.hasMVar || expr.hasLevelMVar then
    throwError "boundary_struct_expr_not_closed"
  let (root, state) ← (encodeExpr expr).run { structural := true }
  return (Json.arr #[.str "expr_struct_dag_v1", .arr state.nodes, toJson root]).compress

def decodeBoundaryStructExpr (source : String) : MetaM Expr := do
  if source.utf8ByteSize > 64 * 1024 * 1024 then
    throwError "boundary_struct_expr_source_limit"
  let env ← getEnv
  let result : Except String Expr := do
    let .arr #[.str "expr_struct_dag_v1", .arr rawNodes, root] ← Json.parse source
      | throw "invalid structural expression encoding"
    if rawNodes.size > 2000000 then throw "structural expression node limit"
    let mut nodes := #[]
    for raw in rawNodes do
      let expr ← match raw with
        | .arr #[.str "m", data, child] =>
          pure <| .mdata (← decodeScalarMetadata data) (← childAt nodes child)
        | _ => decodeNode env {} #[] nodes raw
      nodes := nodes.push expr
    childAt nodes root
  match result with
  | .ok expr => return expr
  | .error error => throwError "boundary_struct_expr_decode_error:{error}"

end ExplicitLean.SimpEngine.Boundary
