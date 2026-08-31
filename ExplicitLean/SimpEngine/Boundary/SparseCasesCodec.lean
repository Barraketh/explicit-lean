module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.DeclarationCodec
public meta import Lean.Meta.Constructions.SparseCasesOn
meta import all Lean.Meta.Constructions.SparseCasesOn

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/- Captured sparse eliminators are checked definitions. Replay does not call
   mkSparseCasesOn, construct a recursor, or allocate a declaration name. The
   surrounding matcher action owns the complete local/async cache transition. -/

private def keyJson (key : SparseCasesOnKey) : Json :=
  .arr #[encodeBoundaryName key.indName, .arr (key.ctors.map encodeBoundaryName),
    .bool key.isPrivate]

private def decodeKey (json : Json) : Except String SparseCasesOnKey := do
  let .arr #[indName, .arr ctors, .bool isPrivate] := json
    | throw "invalid sparse cache key"
  let indName ← decodeBoundaryName indName
  let ctors ← ctors.mapM decodeBoundaryName
  if indName.isAnonymous || ctors.any (·.isAnonymous) then
    throw "anonymous sparse cache key"
  if ctors.toList.eraseDups.length != ctors.size then
    throw "duplicate sparse constructor"
  pure { indName, ctors, isPrivate }

private def infoJson (info : SparseCasesOnInfo) : Json :=
  .arr #[encodeBoundaryName info.indName, toJson info.majorPos, toJson info.arity,
    .arr (info.insterestingCtors.map encodeBoundaryName)]

private def decodeInfo (json : Json) : Except String SparseCasesOnInfo := do
  let .arr #[indName, majorPos, arity, .arr ctors] := json
    | throw "invalid sparse metadata"
  pure {
    indName := ← decodeBoundaryName indName, majorPos := ← majorPos.getNat?,
    arity := ← arity.getNat?, insterestingCtors := ← ctors.mapM decodeBoundaryName }

private def cacheJson (cache : PHashMap SparseCasesOnKey Name) : Json :=
  .arr ((cache.toArray.map fun (key, name) =>
    .arr #[keyJson key, encodeBoundaryName name]).qsort fun a b => a.compress < b.compress)

/-- Exact typed cache state, including every unrelated entry. -/
def boundarySparseCacheJson (env : Environment) (owner : Option Name := none) : Json :=
  match owner with
  | none => cacheJson (sparseCasesOnCacheExt.getState env)
  | some name => cacheJson (sparseCasesOnCacheExt.getState env
      (asyncMode := .async .asyncEnv) (asyncDecl := name))

private structure CapturedSparseCases where
  name : Name
  definition : String
  key : SparseCasesOnKey
  info : SparseCasesOnInfo

private def payloadJson (payload : CapturedSparseCases) : Json :=
  .arr #[.str "boundary_sparse_cases_v1", encodeBoundaryName payload.name,
    .str payload.definition, keyJson payload.key, infoJson payload.info]

private def parsePayload (source : String) : Except String CapturedSparseCases := do
  let .arr #[.str "boundary_sparse_cases_v1", name, .str definition, key, info] ← Json.parse source
    | throw "invalid sparse cases payload"
  pure {
    name := ← decodeBoundaryName name, definition,
    key := ← decodeKey key, info := ← decodeInfo info }

private def validatePayload (payload : CapturedSparseCases) : MetaM Unit := do
  unless isPrivateName payload.name && payload.key.isPrivate do
    throwError "boundary_sparse_expected_private_helper"
  let env ← getEnv
  unless env.containsOnBranch payload.key.indName do
    throwError "boundary_sparse_unknown_inductive"
  let some (.inductInfo ind) := env.find? payload.key.indName (skipRealize := true)
    | throwError "boundary_sparse_expected_inductive"
  unless payload.key.ctors.all ind.ctors.contains &&
      payload.key.ctors.size < ind.ctors.length do
    throwError "boundary_sparse_invalid_constructors"
  let expected : SparseCasesOnInfo := {
    indName := ind.name, majorPos := ind.numParams + 1 + ind.numIndices,
    arity := ind.numParams + 1 + ind.numIndices + 1 + payload.key.ctors.size + 1,
    insterestingCtors := payload.key.ctors }
  unless infoJson payload.info == infoJson expected do
    throwError "boundary_sparse_metadata_conflict"
  let json ← match Json.parse payload.definition with
    | .ok json => pure json
    | .error error => throwError "boundary_sparse_definition:{error}"
  let .arr #[.str tag, name, .arr #[allName], _,
      .arr #[.str "abbrev"], .str "safe", _, _] := json
    | throwError "boundary_sparse_expected_safe_abbreviation"
  unless tag == "boundary_definition_dag_v1" || tag == "boundary_definition_dag_v2" do
    throwError "boundary_sparse_definition_version"
  unless name == encodeBoundaryName payload.name && allName == name do
    throwError "boundary_sparse_definition_identity"

private def checkMetadata (payload : CapturedSparseCases) : MetaM Unit := do
  let env ← getEnv
  unless isSparseCasesOn env payload.name do throwError "boundary_sparse_missing_tag"
  unless getReducibilityStatusCore env payload.name == .reducible do
    throwError "boundary_sparse_reducibility_conflict"
  let some actual := getSparseCasesOnInfoCore env payload.name
    | throwError "boundary_sparse_missing_metadata"
  unless infoJson actual == infoJson payload.info do
    throwError "boundary_sparse_existing_metadata_conflict"

def boundarySparseCasesName (source : String) : MetaM Name := do
  let payload ← match parsePayload source with
    | .ok result => pure result
    | .error error => throwError "boundary_sparse_decode_error:{error}"
  validatePayload payload
  return payload.name

/-- Cached matcher replay checks the helper without importing its realization's
    local cache into the caller's distinct local cache. -/
def checkBoundarySparseCases (expectedName : Name) (source : String) : MetaM Unit := do
  let payload ← match parsePayload source with
    | .ok result => pure result
    | .error error => throwError "boundary_sparse_decode_error:{error}"
  unless expectedName == payload.name do throwError "boundary_sparse_foreign_name"
  validatePayload payload
  unless (← getEnv).containsOnBranch expectedName do
    throwError "boundary_sparse_missing_cached_helper"
  executeBoundaryDefinition payload.name payload.definition
  checkMetadata payload

/-- Capture requires actual typed provenance in a completed realization's cache.
    The surrounding action separately checks declaration closure and dependencies. -/
def encodeBoundarySparseCases (before : Environment) (name owner : Name)
    (structural := false) : MetaM String := do
  let env ← getEnv
  if before.containsOnBranch name then throwError "boundary_sparse_not_fresh"
  let cache := sparseCasesOnCacheExt.getState env
    (asyncMode := .async .asyncEnv) (asyncDecl := owner)
  let keys := cache.toArray.filterMap fun (key, value) => if value == name then some key else none
  unless keys.size == 1 do throwError "boundary_sparse_ambiguous_provenance"
  let some key := keys[0]? | throwError "boundary_sparse_missing_provenance"
  let some info := getSparseCasesOnInfoCore env name
    | throwError "boundary_sparse_missing_capture_metadata"
  let some (.defnInfo definition) := env.find? name (skipRealize := true)
    | throwError "boundary_sparse_expected_definition"
  let payload : CapturedSparseCases := {
    name, definition := ← encodeBoundaryDefinition definition structural, key, info }
  validatePayload payload
  checkMetadata payload
  return (payloadJson payload).compress

/-- Canonical pre-cache inferred only for the fresh captured helper entries.
    Replay must compare it to the actual realization entry state before writing. -/
def boundarySparseCacheWithout (env : Environment) (owner : Name)
    (sources : Array String) : MetaM Json := do
  let mut cache := sparseCasesOnCacheExt.getState env
    (asyncMode := .async .asyncEnv) (asyncDecl := owner)
  for source in sources do
    let payload ← match parsePayload source with
      | .ok result => pure result
      | .error error => throwError "boundary_sparse_decode_error:{error}"
    validatePayload payload
    unless cache.find? payload.key == some payload.name do
      throwError "boundary_sparse_missing_transition_entry"
    cache := cache.erase payload.key
  return cacheJson cache

/-- Add the exact closed helper and typed metadata. The caller supplies the
    realization scope and validates its complete before/after cache state. -/
def executeBoundarySparseCases (expectedName : Name) (source : String) : MetaM Unit := do
  let payload ← match parsePayload source with
    | .ok result => pure result
    | .error error => throwError "boundary_sparse_decode_error:{error}"
  unless expectedName == payload.name do throwError "boundary_sparse_foreign_name"
  validatePayload payload
  let env ← getEnv
  let existed := env.containsOnBranch payload.name
  if let some actual := (sparseCasesOnCacheExt.getState env).find? payload.key then
    unless actual == payload.name do throwError "boundary_sparse_cache_conflict"
  executeBoundaryDefinition payload.name payload.definition
  if existed then
    checkMetadata payload
  else
    modifyEnv fun env => sparseCasesOnCacheExt.modifyState env fun state =>
      state.insert payload.key payload.name
    setReducibleAttribute payload.name
    modifyEnv fun env => markSparseCasesOn env payload.name
    modifyEnv fun env => sparseCasesOnInfoExt.insert env payload.name payload.info
    enableRealizationsForConst payload.name
    checkMetadata payload

end ExplicitLean.SimpEngine.Boundary
