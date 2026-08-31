module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.DeclarationCodec
public meta import Lean.Meta.Tactic.AuxLemma

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/- Ordinary local theorem helpers retain exact public/private names, raw
   canonical proof bodies, tags, and optional auxiliary-cache entries. Capture
   may group multiple helpers; no name generation, simplification, elaboration
   or attribute inference runs during replay. Independently compare every member
   and all local/async effects against the original boundary. -/

private def namesJson (names : List Name) : Json :=
  .arr (names.toArray.map encodeBoundaryName)

private def decodeNames (json : Json) : Except String (List Name) := do
  (← json.getArr?).toList.mapM decodeBoundaryName

private def cacheValueJson : Option (Name × List Name) → Json
  | none => .null
  | some (name, levels) => .arr #[encodeBoundaryName name, namesJson levels]

private def decodeCacheValue (json : Json) : Except String (Option (Name × List Name)) := do
  if json == .null then return none
  let .arr #[name, levels] := json | throw "invalid auxiliary cache value"
  return some (← decodeBoundaryName name, ← decodeNames levels)

/-- Read the actual exported view without realizing a declaration. Theorems
    may deliberately expose their bodies to subsequent imported metaprograms. -/
def boundaryLocalTheoremExportKind (env : Environment) (name : Name) : MetaM String := do
  let some (.thmInfo original) := env.constants.find? name
    | throwError "boundary_local_theorem_missing_checked_theorem"
  match (env.setExporting true).find? name (skipRealize := true) with
  | none => return "private"
  | some (.axiomInfo exposed) =>
      unless exposed.toConstantVal == original.toConstantVal && !exposed.isUnsafe do
        throwError "boundary_local_theorem_exported_signature_conflict"
      return "axiom"
  | some (.thmInfo exposed) =>
      unless exposed.toConstantVal == original.toConstantVal && exposed.all == original.all &&
          exposed.value == original.value do
        throwError "boundary_local_theorem_exported_body_conflict"
      return "theorem"
  | some _ => throwError "boundary_local_theorem_unsupported_exported_kind"

private def validateLocalName (name : Name) : MetaM Unit := do
  if name.isAnonymous then
    throwError "boundary_local_theorem_invalid_name"
  if isReservedName (← getEnv) name then
    throwError "boundary_local_theorem_reserved_name"

def encodeBoundaryLocalTheorem (before : Environment) (thm : TheoremVal) : MetaM String := do
  validateLocalName thm.name
  unless thm.all == [thm.name] do
    throwError "boundary_local_theorem_unsupported_group"
  let env ← getEnv
  let entries := (auxLemmasExt.getState env).lemmas.toArray.filter fun (_, value) =>
    value.1 == thm.name
  if entries.size > 1 then throwError "boundary_local_theorem_multiple_cache_keys"
  let cache : Json ← match entries[0]? with
    | none => pure Json.null
    | some (key, (_, levels)) => do
        if key.type.hasFVar || key.type.hasMVar || key.type.hasLooseBVars then
          throwError "boundary_local_theorem_open_cache_type"
        if isPrivateName thm.name && !key.isPrivate then
          throwError "boundary_local_theorem_public_cache_key_for_private_name"
        unless levels == thm.levelParams do
          throwError "boundary_local_theorem_cache_level_conflict"
        unless key.type == thm.type do
          throwError "boundary_local_theorem_cache_type_conflict"
        let previous := (auxLemmasExt.getState before).lemmas.find? key
        pure (.arr #[.str (← encodeBoundaryExpr key.type), .bool key.isPrivate,
          .bool key.defeq, cacheValueJson previous])
  return (Json.arr #[.str "boundary_local_theorem_v1", .bool (isPrivateName thm.name),
    .str (← boundaryLocalTheoremExportKind env thm.name), .str (← encodeBoundaryTheorem thm),
    .bool (defeqAttr.hasTag env thm.name), .bool (backwardDefeqAttr.hasTag env thm.name),
    cache]).compress

def executeBoundaryLocalTheorem (expectedName : Name) (source : String) : MetaM Unit := do
  validateLocalName expectedName
  let parsed : Except String (String × String × Bool × Bool × Json) := do
    let json ← Json.parse source
    let .arr #[.str "boundary_local_theorem_v1", .bool privateName, .str exportedKind, .str thm, .bool defeqTag,
        .bool backwardTag, cache] := json | throw "invalid local theorem payload"
    unless privateName == isPrivateName expectedName do throw "privacy mismatch"
    unless ["private", "axiom", "theorem"].contains exportedKind do throw "invalid exported kind"
    return (exportedKind, thm, defeqTag, backwardTag, cache)
  let (exportedKind, thm, defeqTag, backwardTag, cache) ← match parsed with
    | .ok result => pure result
    | .error error => throwError "boundary_local_theorem_decode_error:{error}"
  let thmJson ← match Json.parse thm with
    | .ok json => pure json
    | .error error => throwError "boundary_local_theorem_decode_error:{error}"
  let .arr #[.str "boundary_theorem_dag_v1", _, .arr #[groupName], _, _, _] := thmJson
    | throwError "boundary_local_theorem_unsupported_group"
  unless (decodeBoundaryName groupName).toOption == some expectedName do
    throwError "boundary_local_theorem_unsupported_group"
  let existed := (← getEnv).containsOnBranch expectedName
  if let some (.thmInfo existing) := (← getEnv).find? expectedName (skipRealize := true) then
    -- Proof bodies can be inspected by metaprograms (for example rfl tests).
    -- Local helpers use canonical captured bodies even on cache hits.
    unless (← encodeBoundaryTheorem existing) == thm do
      throwError "boundary_local_theorem_existing_declaration_conflict"
  executeBoundaryTheorem expectedName thm (forceExpose := exportedKind == "theorem")
  unless (← boundaryLocalTheoremExportKind (← getEnv) expectedName) == exportedKind do
    throwError "boundary_local_theorem_exported_kind_conflict"
  if !existed then
    if defeqTag then defeqAttr.setTag expectedName
    if backwardTag then backwardDefeqAttr.setTag expectedName
  let env ← getEnv
  unless defeqAttr.hasTag env expectedName == defeqTag &&
      backwardDefeqAttr.hasTag env expectedName == backwardTag do
    throwError "boundary_local_theorem_tag_conflict"
  if cache != .null then
    let .arr #[.str typeSource, .bool isPrivate, .bool defeq, previousJson] := cache
      | throwError "boundary_local_theorem_invalid_cache"
    if isPrivateName expectedName && !isPrivate then
      throwError "boundary_local_theorem_public_cache_key_for_private_name"
    let previous ← match decodeCacheValue previousJson with
      | .ok value => pure value
      | .error error => throwError "boundary_local_theorem_cache_decode_error:{error}"
    let type ← decodeBoundaryExpr typeSource
    if type.hasFVar || type.hasMVar || type.hasLooseBVars then
      throwError "boundary_local_theorem_open_cache_type"
    checkWithKernel type
    let info ← getConstInfo expectedName
    unless type == info.type do
      throwError "boundary_local_theorem_cache_type_conflict"
    let key : AuxLemmaKey := { type, isPrivate, defeq }
    let after := (expectedName, info.levelParams)
    let actual := (auxLemmasExt.getState env).lemmas.find? key
    unless actual == previous || (existed && actual == some after) do
      throwError "boundary_local_theorem_cache_state_conflict"
    modifyEnv fun env => auxLemmasExt.modifyState env fun state =>
      { state with lemmas := state.lemmas.insert key after }

private def helperDependencies (expr : Expr) : NameSet :=
  expr.foldConsts (init := {}) fun name names => names.insert name

/-- Raw closed bodies are preserved. Only the ordering changes: each helper
    depends on the saved environment or an earlier helper in this bundle. -/
def encodeBoundaryLocalTheorems (before : Environment)
    (theorems : Array TheoremVal) : MetaM (Name × String) := do
  if theorems.isEmpty then throwError "boundary_local_theorems_empty"
  let mut pending := theorems.qsort (fun a b => a.name.toString < b.name.toString)
  let anchor := pending[0]!.name
  let mut available : NameSet := {}
  let mut entries := #[]
  while !pending.isEmpty do
    let mut next := #[]
    let mut progress := false
    for thm in pending do
      let dependencies := (helperDependencies thm.type).merge (helperDependencies thm.value)
      if dependencies.toArray.all (fun name => before.containsOnBranch name || available.contains name) then
        entries := entries.push (.arr #[encodeBoundaryName thm.name,
          .str (← encodeBoundaryLocalTheorem before thm)])
        available := available.insert thm.name
        progress := true
      else
        next := next.push thm
    unless progress do throwError "boundary_local_theorems_unsupported_dependency_closure"
    pending := next
  return (anchor, (Json.arr #[.str "boundary_local_theorems_bundle_v1",
    encodeBoundaryName anchor, .arr entries]).compress)

private def parseLocalTheorems (expectedAnchor : Name) (source : String) :
    Except String (Array (Name × String)) := do
  let json ← Json.parse source
  let .arr #[.str "boundary_local_theorems_bundle_v1", anchor, .arr entries] := json
    | throw "invalid local theorem bundle"
  unless (← decodeBoundaryName anchor) == expectedAnchor do throw "foreign bundle anchor"
  if entries.isEmpty then throw "empty local theorem bundle"
  let mut result := #[]
  let mut names : NameSet := {}
  for entry in entries do
    let .arr #[nameJson, .str payload] := entry | throw "invalid local theorem member"
    let name ← decodeBoundaryName nameJson
    if name.isAnonymous || names.contains name then throw "anonymous or duplicate member"
    names := names.insert name
    result := result.push (name, payload)
  let first := ((result.map (·.1)).qsort (fun a b => a.toString < b.toString))[0]!
  unless first == expectedAnchor do
    throw "noncanonical local theorem anchor"
  return result

def boundaryLocalTheoremNames (anchor : Name) (source : String) : MetaM (Array Name) := do
  match parseLocalTheorems anchor source with
  | .ok entries => return entries.map (·.1)
  | .error error => throwError "boundary_local_theorems_decode_error:{error}"

def executeBoundaryLocalTheorems (anchor : Name) (source : String) : MetaM Unit := do
  let entries ← match parseLocalTheorems anchor source with
    | .ok entries => pure entries
    | .error error => throwError "boundary_local_theorems_decode_error:{error}"
  for (name, payload) in entries do
    executeBoundaryLocalTheorem name payload

end ExplicitLean.SimpEngine.Boundary
