module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.ExprCodec
public meta import Lean.AddDecl
public meta import Lean.Meta.Check
public meta import Lean.Data.Json.FromToJson

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/-
  A declaration payload is deliberately separate from the source-term
  protocol.  The expression fields are closed DAGs, and the declaration is
  inserted directly through the checked Core declaration path.  In
  particular, decoding never resolves a reserved name or invokes a term
  elaborator.
-/

private def theoremPayloadTag : String := "boundary_theorem_dag_v1"

private partial def ensureClosedLevel : Level → MetaM Unit
  | .zero => pure ()
  | .succ level => ensureClosedLevel level
  | .max lhs rhs | .imax lhs rhs => do
      ensureClosedLevel lhs
      ensureClosedLevel rhs
  | .param _ => pure ()
  | .mvar _ => throwError "boundary_theorem_unresolved_universe"

private partial def ensureClosedExprAt (boundDepth : Nat) : Expr → MetaM Unit
  | .bvar index =>
      if index < boundDepth then pure ()
      else throwError "boundary_theorem_loose_bound_variable"
  | .fvar _ => throwError "boundary_theorem_foreign_free_variable"
  | .mvar _ => throwError "boundary_theorem_unresolved_metavariable"
  | .sort level => ensureClosedLevel level
  | .const _ levels => levels.forM ensureClosedLevel
  | .app fn arg => do
      ensureClosedExprAt boundDepth fn
      ensureClosedExprAt boundDepth arg
  | .lam _ type body _ | .forallE _ type body _ => do
      ensureClosedExprAt boundDepth type
      ensureClosedExprAt (boundDepth + 1) body
  | .letE _ type value body _ => do
      ensureClosedExprAt boundDepth type
      ensureClosedExprAt boundDepth value
      ensureClosedExprAt (boundDepth + 1) body
  | .lit _ => pure ()
  | .mdata _ child => ensureClosedExprAt boundDepth child
  | .proj _ _ child => ensureClosedExprAt boundDepth child

private def ensureClosedExpr (expr : Expr) : MetaM Unit :=
  ensureClosedExprAt 0 expr

private def encodeLevelParams (levels : List Name) : MetaM Json := do
  if levels.any fun level => level.isAnonymous then
    throwError "boundary_theorem_anonymous_universe_parameter"
  let mut seen : Std.HashSet Name := {}
  let mut result := #[]
  for level in levels do
    if seen.contains level then
      throwError "boundary_theorem_duplicate_universe_parameter"
    seen := seen.insert level
    result := result.push (encodeBoundaryName level)
  pure (.arr result)

private def decodeLevelParams (json : Json) : Except String (List Name) := do
  let parts ← json.getArr?
  let mut seen : Std.HashSet Name := {}
  let mut result := []
  for part in parts do
    let name ← decodeBoundaryName part
    if name.isAnonymous then
      throw "anonymous universe parameter"
    if seen.contains name then
      throw "duplicate universe parameter"
    seen := seen.insert name
    result := result.concat name
  pure result

private def ensureKnownConstants : Expr → MetaM Unit
  | .bvar _ | .fvar _ | .mvar _ | .lit _ => pure ()
  | .sort _ => pure ()
  | .const name _ => do
      unless (← getEnv).containsOnBranch name do
        throwError "boundary_theorem_unknown_constant:{name}"
  | .app fn arg => do
      ensureKnownConstants fn
      ensureKnownConstants arg
  | .lam _ type body _ | .forallE _ type body _ => do
      ensureKnownConstants type
      ensureKnownConstants body
  | .letE _ type value body _ => do
      ensureKnownConstants type
      ensureKnownConstants value
      ensureKnownConstants body
  | .mdata _ child => ensureKnownConstants child
  | .proj name _ child => do
      unless (← getEnv).containsOnBranch name do
        throwError "boundary_theorem_unknown_projection:{name}"
      ensureKnownConstants child

private def ensureCheckedClosed (expr : Expr) : MetaM Unit := do
  ensureClosedExpr expr
  ensureKnownConstants expr
  checkWithKernel expr

private def decodeTheoremNames (json : Json) : Except String (List Name) := do
  let parts ← json.getArr?
  let mut result := []
  for part in parts do
    let name ← decodeBoundaryName part
    if name.isAnonymous then
      throw "anonymous theorem declaration name"
    result := result.concat name
  pure result

private def encodeTheoremNames (names : List Name) : MetaM Json := do
  let mut result := #[]
  for name in names do
    if name.isAnonymous then
      throwError "boundary_theorem_anonymous_declaration_name"
    result := result.push (encodeBoundaryName name)
  pure (.arr result)

private def parseTheoremPayload (source : String) : Except String
    (Name × List Name × List Name × String × String) := do
  let json ← Json.parse source
  let .arr #[.str tag, nameJson, allJson, levelsJson, .str typeSource, .str valueSource] := json
    | throw "invalid theorem payload"
  unless tag == theoremPayloadTag do
    throw "invalid theorem payload tag"
  let name ← decodeBoundaryName nameJson
  if name.isAnonymous then
    throw "anonymous theorem name"
  let all ← decodeTheoremNames allJson
  let levels ← decodeLevelParams levelsJson
  pure (name, all, levels, typeSource, valueSource)

def encodeBoundaryTheorem (thm : TheoremVal) : MetaM String := do
  if thm.name.isAnonymous then
    throwError "boundary_theorem_anonymous_name"
  let all ← encodeTheoremNames thm.all
  ensureClosedExpr thm.type
  ensureClosedExpr thm.value
  ensureKnownConstants thm.type
  ensureKnownConstants thm.value
  checkWithKernel thm.type
  checkWithKernel thm.value
  unless ← isProp thm.type do
    throwError "boundary_theorem_expected_proposition"
  unless ← isDefEq (← inferType thm.value) thm.type do
    throwError "boundary_theorem_value_type_mismatch"
  let typeSource ← encodeBoundaryExpr thm.type
  let valueSource ← encodeBoundaryExpr thm.value
  let levels ← encodeLevelParams thm.levelParams
  return (Json.arr #[.str theoremPayloadTag, encodeBoundaryName thm.name, all, levels,
    .str typeSource, .str valueSource]).compress

def executeBoundaryTheorem (expectedName : Name) (source : String)
    (forceExpose := false) : MetaM Unit := do
  if expectedName.isAnonymous then
    throwError "boundary_theorem_anonymous_expected_name"
  let (name, all, levelParams, typeSource, valueSource) ← match parseTheoremPayload source with
    | .ok payload => pure payload
    | .error error => throwError s!"boundary_theorem_decode_error:{error}"
  unless name == expectedName do
    throwError s!"boundary_theorem_foreign_name:{name}"
  let type ← decodeBoundaryExpr typeSource
  let value ← decodeBoundaryExpr valueSource
  ensureCheckedClosed type
  ensureCheckedClosed value
  unless ← isProp type do
    throwError "boundary_theorem_expected_proposition"
  unless ← isDefEq (← inferType value) type do
    throwError "boundary_theorem_value_type_mismatch"
  let thm : TheoremVal := {
    name := expectedName
    levelParams
    type
    value
    all
  }
  let env ← getEnv
  match env.find? expectedName (skipRealize := true) with
  | some (.thmInfo existing) =>
      unless existing.levelParams == thm.levelParams do
        throwError "boundary_theorem_existing_level_parameters_conflict"
      unless existing.all == thm.all do
        throwError "boundary_theorem_existing_declaration_group_conflict"
      unless ← isDefEq existing.type thm.type do
        throwError "boundary_theorem_existing_type_conflict"
      pure ()
  | some _ =>
      throwError "boundary_theorem_existing_declaration_conflict"
  | none =>
      addDecl (forceExpose := forceExpose) (.thmDecl thm)

/- The matcher prototype only needs safe, nonrecursive singleton definitions.
   Keep this separate from theorem proof irrelevance: a cached definition's
   body and reducibility metadata must agree as well as its type. -/
private def definitionHintsJson : ReducibilityHints → Json
  | .opaque => .arr #[.str "opaque"]
  | .abbrev => .arr #[.str "abbrev"]
  | .regular height => .arr #[.str "regular", toJson height.toNat]

private def decodeDefinitionHints : Json → Except String ReducibilityHints
  | .arr #[.str "opaque"] => pure .opaque
  | .arr #[.str "abbrev"] => pure .abbrev
  | .arr #[.str "regular", heightJson] => do
      let height ← heightJson.getNat?
      if height > 4294967295 then throw "definition height overflow"
      pure (.regular height.toUInt32)
  | _ => throw "invalid definition hints"

def encodeBoundaryDefinition (value : DefinitionVal) (structural := false) : MetaM String := do
  unless value.safety == .safe do
    throwError "boundary_definition_unsafe"
  unless value.all == [value.name] do
    throwError "boundary_definition_unsupported_group"
  if value.name.isAnonymous then throwError "boundary_definition_anonymous_name"
  if (value.type.find? (·.isConstOf value.name)).isSome ||
      (value.value.find? (·.isConstOf value.name)).isSome then
    throwError "boundary_definition_recursive_reference"
  ensureCheckedClosed value.type
  ensureCheckedClosed value.value
  unless ← isDefEq (← inferType value.value) value.type do
    throwError "boundary_definition_value_type_mismatch"
  let levels ← encodeLevelParams value.levelParams
  let encode := if structural then encodeBoundaryStructExpr else encodeBoundaryExpr
  let typeSource ← encode value.type
  let valueSource ← encode value.value
  if structural then
    unless Expr.equal value.type (← decodeBoundaryStructExpr typeSource) &&
        Expr.equal value.value (← decodeBoundaryStructExpr valueSource) do
      throwError "boundary_definition_structural_roundtrip"
  return (Json.arr #[.str (if structural then "boundary_definition_dag_v2" else "boundary_definition_dag_v1"), encodeBoundaryName value.name,
    .arr #[encodeBoundaryName value.name], levels, definitionHintsJson value.hints,
    .str "safe", .str typeSource, .str valueSource]).compress

def executeBoundaryDefinition (expectedName : Name) (source : String) : MetaM Unit := do
  let parsed : Except String (Bool × Name × List Name × ReducibilityHints × String × String) := do
    let json ← Json.parse source
    let .arr #[.str tag, nameJson, .arr #[allNameJson],
        levelsJson, hintsJson, .str "safe", .str typeSource, .str valueSource] := json
      | throw "invalid safe singleton definition payload"
    unless tag == "boundary_definition_dag_v1" || tag == "boundary_definition_dag_v2" do
      throw "invalid definition payload version"
    let name ← decodeBoundaryName nameJson
    unless name == (← decodeBoundaryName allNameJson) do throw "foreign definition group"
    pure (tag == "boundary_definition_dag_v2", name, ← decodeLevelParams levelsJson, ← decodeDefinitionHints hintsJson,
      typeSource, valueSource)
  let (structural, name, levelParams, hints, typeSource, valueSource) ← match parsed with
    | .ok result => pure result
    | .error error => throwError "boundary_definition_decode_error:{error}"
  unless name == expectedName && !name.isAnonymous do
    throwError "boundary_definition_foreign_name"
  let decode := if structural then decodeBoundaryStructExpr else decodeBoundaryExpr
  let type ← decode typeSource
  let value ← decode valueSource
  if (type.find? (·.isConstOf name)).isSome || (value.find? (·.isConstOf name)).isSome then
    throwError "boundary_definition_recursive_reference"
  ensureCheckedClosed type
  ensureCheckedClosed value
  unless ← isDefEq (← inferType value) type do
    throwError "boundary_definition_value_type_mismatch"
  let decl : DefinitionVal := {
    name, levelParams, type, value, hints, safety := .safe, all := [name] }
  match (← getEnv).find? name (skipRealize := true) with
  | some (.defnInfo existing) =>
      unless existing.levelParams == decl.levelParams && existing.all == decl.all &&
          existing.safety == decl.safety &&
          definitionHintsJson existing.hints == definitionHintsJson decl.hints do
        throwError "boundary_definition_existing_metadata_conflict"
      unless ← if structural then pure (Expr.equal existing.type decl.type) else isDefEq existing.type decl.type do
        throwError "boundary_definition_existing_type_conflict"
      unless ← if structural then pure (Expr.equal existing.value decl.value) else isDefEq existing.value decl.value do
        throwError "boundary_definition_existing_value_conflict"
  | some _ => throwError "boundary_definition_existing_kind_conflict"
  | none => addDecl (.defnDecl decl)

end ExplicitLean.SimpEngine.Boundary
