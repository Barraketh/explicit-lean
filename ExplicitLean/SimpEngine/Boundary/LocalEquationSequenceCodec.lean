module
prelude
public meta import ExplicitLean.SimpEngine.Boundary.RealizationCodec
meta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
meta import all ExplicitLean.SimpEngine.Boundary.EquationCodec
public meta section
open Lean Meta
namespace ExplicitLean.SimpEngine.Boundary

private def localEquationState (env : Environment) : Json :=
  .arr #[boundaryMatchStateJson (Match.matchEqnsExt.getState env),
    equationStateJson (eqnsExt.getState env), boundarySparseCacheJson env]

private def localEquationSnapshot (env : Environment) (name : Name) : Json :=
  .arr #[boundaryMatchStateJson (Match.matchEqnsExt.getState env
      (asyncMode := .async .asyncEnv) (asyncDecl := name)),
    equationStateJson (eqnsExt.getState env (asyncMode := .async .asyncEnv) (asyncDecl := name)),
    boundarySparseCacheJson env (some name)]

private def localEquationChecked (env : Environment) : NameSet :=
  env.constants.foldStage2 (fun names name _ => names.insert name) {}

private def registeredState (state : EqnsExtState) (key : Name) (source : String) : MetaM EqnsExtState := do
  let (owner, _, _, _, registration) ← ofExcept (parseEquationPayload source)
  if let some existing := state.mapInv.find? key then
    unless registration && existing == owner do throwError "boundary_local_equation_registration_conflict"
  return if registration then { state with mapInv := state.mapInv.insert key owner } else state

private structure LocalEquationSequence where
  fresh : Name
  source : String
  freshOwner : Name
  freshWitness : Json
  freshDescriptor : Json
  final : String
  owner : Name
  key : Name
  witness : Json
  initialDescriptor : Json
  finalDescriptor : Json
  beforeState : Json
  middleState : Json
  afterState : Json
  snapshot : Json

private def parseLocalEquationSequence (anchor : Name) (source : String) : MetaM LocalEquationSequence := do
  let .arr #[.str "boundary_local_equation_sequence_v1", freshJson, .str equation,
      freshWitness, freshDescriptor, .str initial, .str final,
      beforeState, middleState, afterState, snapshot] ← ofExcept (Json.parse source)
    | throwError "boundary_local_equation_sequence_payload"
  let fresh ← ofExcept (decodeBoundaryName freshJson)
  let (freshOwner, _, _, _, _) ← ofExcept (parseEquationPayload equation)
  let initialJson ← ofExcept (Json.parse initial)
  let finalJson ← ofExcept (Json.parse final)
  let .arr initialFields := initialJson | throwError "boundary_local_equation_sequence_initial"
  let .arr finalFields := finalJson | throwError "boundary_local_equation_sequence_final"
  unless initialFields.size == 11 && finalFields.size == 11 do
    throwError "boundary_local_equation_sequence_header"
  let .arr #[ownerJson, keyJson, witness, initialDescriptor, .str rootSource] := initialFields[10]!
    | throwError "boundary_local_equation_sequence_root"
  let .arr #[_, _, _, finalDescriptor, .str _] := finalFields[10]!
    | throwError "boundary_local_equation_sequence_root"
  let owner ← ofExcept (decodeBoundaryName ownerJson)
  let key ← ofExcept (decodeBoundaryName keyJson)
  let (rootOwner, _, _, _, _) ← ofExcept (parseEquationPayload rootSource)
  unless fresh == anchor && fresh != key && freshOwner != owner &&
      fresh.getPrefix == freshOwner && key.getPrefix == owner && rootOwner == owner &&
      !isPrivateName fresh && !isPrivateName key &&
      initialFields[0]! == .str "boundary_local_cached_equation_v2" &&
      initialFields[1]! == .bool true && initialFields[2]! == nameArrayJson #[key] &&
      initialFields[3]! == nameArrayJson #[key] &&
      middleState == .arr #[initialFields[4]!, initialFields[6]!, initialFields[8]!] &&
      afterState == .arr #[initialFields[5]!, initialFields[7]!, initialFields[9]!] &&
      initialFields.set! 10 (.arr #[ownerJson, keyJson, witness, finalDescriptor, .str rootSource]) == finalFields do
    throwError "boundary_local_equation_sequence_identity"
  return ⟨fresh, equation, freshOwner, freshWitness, freshDescriptor, final, owner, key,
    witness, initialDescriptor, finalDescriptor, beforeState, middleState, afterState, snapshot⟩

def isBoundaryLocalEquationSequence (source : String) : Bool :=
  match (Json.parse source).toOption with
  | some (.arr fields) => fields[0]? == some (.str "boundary_local_equation_sequence_v1")
  | _ => false

/-- A separate bounded contract for two safe local owners. A fresh closed
    equation recipe is followed by an authenticated completed cached equation.
    The full fresh DAG authenticates the producer outcome; no local generator
    is inferred or invoked, and the existing imported contracts stay unchanged. -/
def encodeBoundaryLocalEquationSequence? (before stock : Environment) (checkedBefore : NameSet)
    (equations : Array (Name × String)) : MetaM (Option (Name × String)) := do
  let added ← branchDelta before stock
  let cached := added.filter fun name => checkedBefore.contains name &&
    !stock.isImportedConst name.getPrefix && match name with
      | .str _ suffix => isEqnLikeSuffix suffix
      | _ => false
  if cached.isEmpty || equations.isEmpty then return none
  unless cached.size == 1 && equations.size == 1 do throwError "boundary_local_equation_sequence_cover"
  let key := cached[0]!
  let (fresh, equation) := equations[0]!
  let freshOwner := fresh.getPrefix
  let owner := key.getPrefix
  -- This is not an alternate path for the existing imported-owner sequence.
  if before.isImportedConst freshOwner then return none
  unless freshOwner != owner && added == #[fresh, key] &&
      (← branchDelta before stock true) == added && !checkedBefore.contains fresh &&
      !before.containsOnBranch fresh && !before.containsOnBranch key &&
      (localEquationChecked stock).toArray.filter (!checkedBefore.contains ·) == #[fresh] do
    throwError "boundary_local_equation_sequence_order"
  let freshWitness ← withEnv before <| localOwnerWitness before freshOwner
  let witness ← withEnv before <| localOwnerWitness before owner
  unless freshWitness == (← withEnv stock <| localOwnerWitness stock freshOwner) &&
      witness == (← withEnv stock <| localOwnerWitness stock owner) do
    throwError "boundary_local_equation_sequence_owner_changed"
  let some (.thmInfo thm) := stock.checked.get.find? key
    | throwError "boundary_local_equation_sequence_root_kind"
  let mapping := (eqnsExt.getState stock).mapInv.find? key
  unless mapping.isNone || mapping == some owner do throwError "boundary_local_equation_sequence_root_mapping"
  let rootSource ← withEnv stock <| encodeBoundaryEquation owner thm
    (defeqAttr.hasTag stock key) (backwardDefeqAttr.hasTag stock key) mapping.isSome
  let beforeState := localEquationState before
  let middleEquations ← registeredState (eqnsExt.getState before) fresh equation
  let afterEquations ← registeredState middleEquations key rootSource
  let matchState := boundaryMatchStateJson (Match.matchEqnsExt.getState before)
  let sparseState := boundarySparseCacheJson before
  let middleState := Json.arr #[matchState, equationStateJson middleEquations, sparseState]
  let afterState := Json.arr #[matchState, equationStateJson afterEquations, sparseState]
  unless afterState == localEquationState stock do throwError "boundary_local_equation_sequence_state_effect"
  let initialDescriptor ← withEnv before <| localCachedDescriptor before owner key true true
  let finalDescriptor ← withEnv stock <| localCachedDescriptor stock owner key true true
  let freshDescriptor ← withEnv stock <| localCachedDescriptor stock freshOwner fresh true true
  let payload (descriptor : Json) := (Json.arr #[.str "boundary_local_cached_equation_v2", .bool true,
    nameArrayJson #[key], nameArrayJson #[key], matchState, matchState,
    equationStateJson middleEquations, equationStateJson afterEquations, sparseState, sparseState,
    .arr #[encodeBoundaryName owner, encodeBoundaryName key, witness, descriptor, .str rootSource]]).compress
  let result := (Json.arr #[.str "boundary_local_equation_sequence_v1", encodeBoundaryName fresh,
    .str equation, freshWitness, freshDescriptor, .str (payload initialDescriptor), .str (payload finalDescriptor),
    beforeState, middleState, afterState, localEquationSnapshot stock fresh]).compress
  discard <| parseLocalEquationSequence fresh result
  return some (fresh, result)

def executeBoundaryLocalEquationSequence (anchor : Name) (source : String) : MetaM Unit := do
  let s ← parseLocalEquationSequence anchor source
  let before ← getEnv
  let checked := localEquationChecked before
  unless !before.containsOnBranch s.fresh && !before.containsOnBranch s.key &&
      !checked.contains s.fresh && checked.contains s.key && localEquationState before == s.beforeState do
    throwError "boundary_local_equation_sequence_before"
  unless (← localOwnerWitness before s.freshOwner) == s.freshWitness &&
      (← localOwnerWitness before s.owner) == s.witness &&
      (← localCachedDescriptor before s.owner s.key true true) == s.initialDescriptor do
    throwError "boundary_local_equation_sequence_initial_authentication"
  -- EquationCodec uses only the supplied closed theorem and exact tags and
  -- registration. realizeBoundaryConst retains the owner's saved context and
  -- reinstalls the no-synthesis barrier inside a fresh producer MetaM runner.
  executeBoundaryEquation s.fresh s.source
  let middle ← getEnv
  unless (← branchDelta before middle) == #[s.fresh] &&
      (← branchDelta before middle true) == #[s.fresh] && localEquationState middle == s.middleState &&
      localEquationSnapshot middle s.fresh == s.snapshot &&
      (localEquationChecked middle).toArray.filter (!checked.contains ·) == #[s.fresh] do
    throwError "boundary_local_equation_sequence_fresh_transition"
  unless (← localOwnerWitness middle s.freshOwner) == s.freshWitness &&
      (← localCachedDescriptor middle s.freshOwner s.fresh true true) == s.freshDescriptor &&
      (← localOwnerWitness middle s.owner) == s.witness &&
      (← localCachedDescriptor middle s.owner s.key true true) == s.finalDescriptor do
    throwError "boundary_local_equation_sequence_middle_authentication"
  executeLocalCachedBatch s.key s.final
  let after ← getEnv
  unless (← branchDelta before after) == #[s.fresh, s.key] &&
      (← branchDelta before after true) == #[s.fresh, s.key] && localEquationState after == s.afterState &&
      localEquationSnapshot after s.fresh == s.snapshot &&
      (localEquationChecked after).toArray.filter (!checked.contains ·) == #[s.fresh] &&
      (← localOwnerWitness after s.freshOwner) == s.freshWitness &&
      (← localOwnerWitness after s.owner) == s.witness &&
      (← localCachedDescriptor after s.freshOwner s.fresh true true) == s.freshDescriptor &&
      (← localCachedDescriptor after s.owner s.key true true) == s.finalDescriptor do
    throwError "boundary_local_equation_sequence_after"

def boundaryLocalEquationSequenceMembers (anchor : Name) (source : String) :
    MetaM (Array Name × Array Name × Array (Name × String)) := do
  let s ← parseLocalEquationSequence anchor source
  return (#[s.fresh, s.key], #[s.fresh], #[])

end ExplicitLean.SimpEngine.Boundary
