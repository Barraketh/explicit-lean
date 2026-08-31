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

private partial def encodeLevel (level : Level) : MetaM Json := do
  match ← instantiateLevelMVars level with
  | .zero => return .arr #[.str "z"]
  | .succ level => return .arr #[.str "s", ← encodeLevel level]
  | .max lhs rhs => return .arr #[.str "max", ← encodeLevel lhs, ← encodeLevel rhs]
  | .imax lhs rhs => return .arr #[.str "imax", ← encodeLevel lhs, ← encodeLevel rhs]
  | .param name => return .arr #[.str "p", encodeBoundaryName name]
  | .mvar _ => throwError "boundary_expr_unresolved_universe"

private def decodeLevel : Nat → Json → Except String Level
  | 0, _ => throw "expression universe nesting limit exceeded"
  | _ + 1, .arr #[.str "z"] => return .zero
  | fuel + 1, .arr #[.str "s", level] => return .succ (← decodeLevel fuel level)
  | fuel + 1, .arr #[.str "max", lhs, rhs] =>
      return .max (← decodeLevel fuel lhs) (← decodeLevel fuel rhs)
  | fuel + 1, .arr #[.str "imax", lhs, rhs] =>
      return .imax (← decodeLevel fuel lhs) (← decodeLevel fuel rhs)
  | _ + 1, .arr #[.str "p", name] => return .param (← decodeBoundaryName name)
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
  nodes : Array Json := #[]
  memo : Std.HashMap Expr Nat := {}

private abbrev EncodeM := StateT EncodeState MetaM

private partial def encodeExpr (expr : Expr) : EncodeM Nat := do
  if let some index := (← get).memo[expr]? then
    return index
  if let .mdata _ child := expr then
    return ← encodeExpr child
  let node : Json ← match expr with
    | .bvar index => pure <| .arr #[.str "b", toJson index]
    | .fvar id => do
        let some decl := (← getLCtx).find? id
          | throwError "boundary_expr_unknown_local"
        pure <| .arr #[.str "f", toJson decl.index]
    | .mvar _ => throwError "boundary_expr_unresolved_metavariable"
    | .sort level => do pure <| .arr #[.str "s", ← encodeLevel level]
    | .const name levels => do pure <| .arr #[.str "c", encodeBoundaryName name, toJson (← levels.mapM (fun level => encodeLevel level))]
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
    | .mdata .. => unreachable!
  let index := (← get).nodes.size
  modify fun state => { nodes := state.nodes.push node, memo := state.memo.insert expr index }
  return index

def encodeBoundaryExpr (expr : Expr) : MetaM String := do
  let expr ← instantiateMVars expr
  let (root, state) ← (encodeExpr expr).run {}
  return (Json.arr #[.str "expr_dag_v1", .arr state.nodes, toJson root]).compress

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
    (nodes : Array Expr) (json : Json) : Except String Expr := do
  match json with
  | .arr #[.str "b", index] => return mkBVar (← index.getNat?)
  | .arr #[.str "f", index] =>
      let index ← index.getNat?
      let some id := locals[index]?
        | throw "expression local index is unavailable"
      return mkFVar id
  | .arr #[.str "s", level] => return mkSort (← decodeLevel 256 level)
  | .arr #[.str "c", name, levels] =>
      let name ← decodeBoundaryName name
      requireConstant env name
      return mkConst name (← (← levels.getArr?).toList.mapM (decodeLevel 256))
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

def decodeBoundaryExpr (source : String) : MetaM Expr := do
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
    let .arr #[.str "expr_dag_v1", .arr rawNodes, root] ← Json.parse source
      | throw "invalid expression encoding"
    if rawNodes.size > 2000000 then
      throw "expression node count limit exceeded"
    let mut nodes := #[]
    for node in rawNodes do
      nodes := nodes.push (← decodeNode env locals nodes node)
    childAt nodes root
  match result with
  | .ok expr => return expr
  | .error error => throwError "boundary_expr_decode_error: {error}"

end ExplicitLean.SimpEngine.Boundary
