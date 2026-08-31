module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.DeclarationCodec
public meta import Lean.Meta.Tactic.AuxLemma

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/- A public theorem introduced by tactic elaboration must remain public and
   retain its exact name. This codec inserts its checked captured declaration;
   it does not recognize generated names by suffix or rerun their generator.
   The optional local auxiliary-lemma cache entry is an explicit typed effect.
   Payloads must come from authenticated capture and pass the independent full
   stock/applied boundary comparison. Kernel checking alone cannot authenticate
   captured tag metadata; this module does not infer or regenerate attributes. -/

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

private def validatePublicName (name : Name) : MetaM Unit := do
  if name.isAnonymous || isPrivateName name then
    throwError "boundary_public_theorem_invalid_name"
  if isReservedName (← getEnv) name then
    throwError "boundary_public_theorem_reserved_name"

def encodeBoundaryPublicTheorem (before : Environment) (thm : TheoremVal) : MetaM String := do
  validatePublicName thm.name
  unless thm.all == [thm.name] do
    throwError "boundary_public_theorem_unsupported_group"
  let env ← getEnv
  let entries := (auxLemmasExt.getState env).lemmas.toArray.filter fun (_, value) =>
    value.1 == thm.name
  if entries.size > 1 then throwError "boundary_public_theorem_multiple_cache_keys"
  let cache : Json ← match entries[0]? with
    | none => pure Json.null
    | some (key, (_, levels)) => do
        if key.type.hasFVar || key.type.hasMVar || key.type.hasLooseBVars then
          throwError "boundary_public_theorem_open_cache_type"
        unless levels == thm.levelParams do
          throwError "boundary_public_theorem_cache_level_conflict"
        unless ← isDefEq key.type thm.type do
          throwError "boundary_public_theorem_cache_type_conflict"
        let previous := (auxLemmasExt.getState before).lemmas.find? key
        pure (.arr #[.str (← encodeBoundaryExpr key.type), .bool key.isPrivate,
          .bool key.defeq, cacheValueJson previous])
  return (Json.arr #[.str "boundary_public_theorem_v1", .str (← encodeBoundaryTheorem thm),
    .bool (defeqAttr.hasTag env thm.name), .bool (backwardDefeqAttr.hasTag env thm.name),
    cache]).compress

def executeBoundaryPublicTheorem (expectedName : Name) (source : String) : MetaM Unit := do
  validatePublicName expectedName
  let parsed : Except String (String × Bool × Bool × Json) := do
    let json ← Json.parse source
    let .arr #[.str "boundary_public_theorem_v1", .str thm, .bool defeqTag,
        .bool backwardTag, cache] := json | throw "invalid public theorem payload"
    return (thm, defeqTag, backwardTag, cache)
  let (thm, defeqTag, backwardTag, cache) ← match parsed with
    | .ok result => pure result
    | .error error => throwError "boundary_public_theorem_decode_error:{error}"
  let thmJson ← match Json.parse thm with
    | .ok json => pure json
    | .error error => throwError "boundary_public_theorem_decode_error:{error}"
  let .arr #[.str "boundary_theorem_dag_v1", _, .arr #[groupName], _, _, _] := thmJson
    | throwError "boundary_public_theorem_unsupported_group"
  unless (decodeBoundaryName groupName).toOption == some expectedName do
    throwError "boundary_public_theorem_unsupported_group"
  let existed := (← getEnv).containsOnBranch expectedName
  if let some (.thmInfo existing) := (← getEnv).find? expectedName (skipRealize := true) then
    -- Proof bodies can be inspected by metaprograms (for example rfl tests).
    -- Public local helpers use canonical captured bodies even on cache hits.
    unless (← encodeBoundaryTheorem existing) == thm do
      throwError "boundary_public_theorem_existing_declaration_conflict"
  executeBoundaryTheorem expectedName thm
  if !existed then
    if defeqTag then defeqAttr.setTag expectedName
    if backwardTag then backwardDefeqAttr.setTag expectedName
  let env ← getEnv
  unless defeqAttr.hasTag env expectedName == defeqTag &&
      backwardDefeqAttr.hasTag env expectedName == backwardTag do
    throwError "boundary_public_theorem_tag_conflict"
  if cache != .null then
    let .arr #[.str typeSource, .bool isPrivate, .bool defeq, previousJson] := cache
      | throwError "boundary_public_theorem_invalid_cache"
    let previous ← match decodeCacheValue previousJson with
      | .ok value => pure value
      | .error error => throwError "boundary_public_theorem_cache_decode_error:{error}"
    let type ← decodeBoundaryExpr typeSource
    if type.hasFVar || type.hasMVar || type.hasLooseBVars then
      throwError "boundary_public_theorem_open_cache_type"
    checkWithKernel type
    let info ← getConstInfo expectedName
    unless ← isDefEq type info.type do
      throwError "boundary_public_theorem_cache_type_conflict"
    let key : AuxLemmaKey := { type, isPrivate, defeq }
    let after := (expectedName, info.levelParams)
    let actual := (auxLemmasExt.getState env).lemmas.find? key
    unless actual == previous || (existed && actual == some after) do
      throwError "boundary_public_theorem_cache_state_conflict"
    modifyEnv fun env => auxLemmasExt.modifyState env fun state =>
      { state with lemmas := state.lemmas.insert key after }

end ExplicitLean.SimpEngine.Boundary
