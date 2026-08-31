module
prelude
public meta import ExplicitLean.SimpEngine.Boundary.RealizationCodec
meta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
meta import all ExplicitLean.SimpEngine.Boundary.CongruenceCodec
public meta section
open Lean Meta
namespace ExplicitLean.SimpEngine.Boundary

private def congrSequenceState (env : Environment) : Json :=
  .arr #[boundaryMatchStateJson (Match.matchEqnsExt.getState env),
    equationStateJson (eqnsExt.getState env), boundarySparseCacheJson env]

private def congrSequenceSnapshot (env : Environment) (name : Name) : Json :=
  .arr #[boundaryMatchStateJson (Match.matchEqnsExt.getState env
      (asyncMode := .async .asyncEnv) (asyncDecl := name)),
    equationStateJson (eqnsExt.getState env (asyncMode := .async .asyncEnv) (asyncDecl := name)),
    boundarySparseCacheJson env (some name)]

private def checkedNames (env : Environment) : NameSet :=
  env.constants.foldStage2 (fun names name _ => names.insert name) {}

private structure CongruenceSequence where
  fresh : Name
  source : String
  initial : String
  final : String
  state : Json
  snapshot : Json
  owner : Name
  key : Name
  witness : Json
  initialDescriptor : Json
  finalDescriptor : Json
  canonicalModuleDocs : Bool

private def parseCongruenceSequence (anchor : Name) (source : String) : MetaM CongruenceSequence := do
  let .arr #[.str version, fresh, .str congruence,
      .str initial, .str final, state, snapshot] ← ofExcept (Json.parse source)
    | throwError "boundary_congruence_sequence_payload"
  unless version == "boundary_cached_congruence_sequence_v1" || version == "boundary_cached_congruence_sequence_v2" do
    throwError "boundary_congruence_sequence_version"
  let canonicalModuleDocs := version == "boundary_cached_congruence_sequence_v2"
  let fresh ← ofExcept (decodeBoundaryName fresh)
  let initialJson ← ofExcept (Json.parse initial)
  let finalJson ← ofExcept (Json.parse final)
  let .arr initialFields := initialJson | throwError "boundary_congruence_sequence_initial"
  let .arr finalFields := finalJson | throwError "boundary_congruence_sequence_final"
  unless initialFields.size == 11 && finalFields.size == 11 do
    throwError "boundary_congruence_sequence_header"
  let .arr #[ownerJson, keyJson, witness, initialDescriptor, .str rootSource] := initialFields[10]!
    | throwError "boundary_congruence_sequence_root"
  let .arr #[_, _, _, finalDescriptor, .str _] := finalFields[10]!
    | throwError "boundary_congruence_sequence_root"
  let owner ← ofExcept (decodeBoundaryName ownerJson)
  let key ← ofExcept (decodeBoundaryName keyJson)
  unless initialFields.size == 11 && finalFields.size == 11 &&
      initialFields[0]! == .str (if canonicalModuleDocs then "boundary_local_cached_congruence_v2" else "boundary_local_cached_congruence_v1") &&
      initialFields[1]! == .bool true && initialFields[2]! == nameArrayJson #[key] &&
      initialFields[3]! == nameArrayJson #[key] &&
      state == .arr #[initialFields[4]!, initialFields[6]!, initialFields[8]!] &&
      state == .arr #[initialFields[5]!, initialFields[7]!, initialFields[9]!] &&
      initialFields.set! 10 (.arr #[ownerJson, keyJson, witness, finalDescriptor, .str rootSource]) == finalFields &&
      fresh == anchor && fresh != key && !isPrivateName fresh && !isPrivateName key && key.getPrefix == owner do
    throwError "boundary_congruence_sequence_identity"
  let (freshOwner, _, _) ← ofExcept (parseCongruencePayload congruence)
  let (rootOwner, _, _) ← ofExcept (parseCongruencePayload rootSource)
  unless freshOwner == fresh.getPrefix && rootOwner == owner do
    throwError "boundary_congruence_sequence_owner"
  return ⟨fresh, congruence, initial, final, state, snapshot, owner, key, witness,
    initialDescriptor, finalDescriptor, canonicalModuleDocs⟩

def isBoundaryCongruenceSequence (source : String) : Bool :=
  match (Json.parse source).toOption with
  | some (.arr values) => values[0]? == some (.str "boundary_cached_congruence_sequence_v1") ||
      values[0]? == some (.str "boundary_cached_congruence_sequence_v2")
  | _ => false

/-- A distinct bounded contract: one fresh imported-owner congruence followed
    by one authentic completed local cache activation. Both descriptor phases
    remain exact; the fresh checked declaration changes exporter domains. -/
def encodeBoundaryCongruenceSequence? (before stock : Environment) (checkedBefore : NameSet)
    (congruences : Array (Name × String)) : MetaM (Option (Name × String)) := do
  let added ← branchDelta before stock
  let cached := added.filter fun name => checkedBefore.contains name &&
    !stock.isImportedConst name.getPrefix && (congrKindsExt.find? stock name).isSome
  if cached.isEmpty || congruences.isEmpty then return none
  unless cached.size == 1 && congruences.size == 1 do
    throwError "boundary_congruence_sequence_cover"
  let key := cached[0]!
  let (fresh, source) := congruences[0]!
  let owner := key.getPrefix
  unless added == #[fresh, key] && (← branchDelta before stock true) == added &&
      !checkedBefore.contains fresh && before.isImportedConst fresh.getPrefix &&
      !before.containsOnBranch fresh && !before.containsOnBranch key do
    throwError "boundary_congruence_sequence_order"
  let stockFresh := (checkedNames stock).toArray.filter (!checkedBefore.contains ·)
  unless stockFresh == #[fresh] do throwError "boundary_congruence_sequence_checked_cover"
  let state := congrSequenceState before
  unless state == congrSequenceState stock do throwError "boundary_congruence_sequence_state_effect"
  let witness ← withEnv before <| localOwnerWitness before owner
  unless witness == (← withEnv stock <| localOwnerWitness stock owner) do
    throwError "boundary_congruence_sequence_owner_changed"
  let initialDescriptor ← withEnv before <| localCachedDescriptor before owner key true true
  let finalDescriptor ← withEnv stock <| localCachedDescriptor stock owner key true true
  let some (.thmInfo thm) := stock.checked.get.find? key
    | throwError "boundary_congruence_sequence_root_kind"
  let some kinds := congrKindsExt.find? stock key | throwError "boundary_congruence_sequence_kinds"
  let rootSource ← withEnv stock <| encodeBoundaryCongruence owner thm kinds
  let .arr stateParts := state | throwError "boundary_congruence_sequence_state"
  let payload (descriptor : Json) := (Json.arr #[.str "boundary_local_cached_congruence_v2", .bool true,
    nameArrayJson #[key], nameArrayJson #[key], stateParts[0]!, stateParts[0]!, stateParts[1]!, stateParts[1]!,
    stateParts[2]!, stateParts[2]!, .arr #[encodeBoundaryName owner, encodeBoundaryName key,
      witness, descriptor, .str rootSource]]).compress
  let encoded := (Json.arr #[.str "boundary_cached_congruence_sequence_v2", encodeBoundaryName fresh,
    .str source, .str (payload initialDescriptor), .str (payload finalDescriptor), state,
    congrSequenceSnapshot stock fresh]).compress
  discard <| parseCongruenceSequence fresh encoded
  return some (fresh, encoded)

def executeBoundaryCongruenceSequence (anchor : Name) (source : String) : MetaM Unit := do
  let s ← parseCongruenceSequence anchor source
  let before ← getEnv
  let checked := checkedNames before
  unless !before.containsOnBranch s.fresh && !before.containsOnBranch s.key &&
      !checked.contains s.fresh && checked.contains s.key && before.isImportedConst s.fresh.getPrefix &&
      congrSequenceState before == s.state do throwError "boundary_congruence_sequence_before"
  unless (← localOwnerWitness before s.owner) == s.witness &&
      (← localCachedDescriptor before s.owner s.key true s.canonicalModuleDocs) == s.initialDescriptor do
    throwError "boundary_congruence_sequence_initial_authentication"
  executeBoundaryCongruence s.fresh s.source
  let middle ← getEnv
  unless (← branchDelta before middle) == #[s.fresh] &&
      (← branchDelta before middle true) == #[s.fresh] && congrSequenceState middle == s.state &&
      congrSequenceSnapshot middle s.fresh == s.snapshot &&
      (checkedNames middle).toArray.filter (!checked.contains ·) == #[s.fresh] do
    throwError "boundary_congruence_sequence_fresh_transition"
  unless (← localOwnerWitness middle s.owner) == s.witness &&
      (← localCachedDescriptor middle s.owner s.key true s.canonicalModuleDocs) == s.finalDescriptor do
    throwError "boundary_congruence_sequence_middle_authentication"
  executeLocalCachedBatch s.key s.final
  let after ← getEnv
  unless (← branchDelta before after) == #[s.fresh, s.key] &&
      (← branchDelta before after true) == #[s.fresh, s.key] && congrSequenceState after == s.state &&
      congrSequenceSnapshot after s.fresh == s.snapshot &&
      (checkedNames after).toArray.filter (!checked.contains ·) == #[s.fresh] &&
      (← localOwnerWitness after s.owner) == s.witness &&
      (← localCachedDescriptor after s.owner s.key true s.canonicalModuleDocs) == s.finalDescriptor do
    throwError "boundary_congruence_sequence_after"

def boundaryCongruenceSequenceMembers (anchor : Name) (source : String) :
    MetaM (Array Name × Array Name × Array (Name × String)) := do
  let s ← parseCongruenceSequence anchor source
  return (#[s.fresh, s.key], #[s.fresh], #[])

end ExplicitLean.SimpEngine.Boundary
