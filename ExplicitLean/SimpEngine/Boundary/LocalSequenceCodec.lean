module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.RealizationCodec
public meta import ExplicitLean.SimpEngine.Boundary.LocalTheoremCodec
meta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
meta import all ExplicitLean.SimpEngine.Boundary.EquationCodec

public meta section
open Lean Meta
namespace ExplicitLean.SimpEngine.Boundary

/- A separate contract: one completed local cached equation, interleaved with
   fresh ordinary theorem helpers. No local producer or imported registration
   is inferred, and the imported sequence and standalone batch stay unchanged. -/
private structure LocalSequence where
  added : Array Name
  publicAdded : Array Name
  fresh : Array Name
  beforeState : Json
  afterState : Json
  owner : Name
  key : Name
  witness : Json
  descriptor : Json
  equation : String
  steps : Array Json

private def localSequenceState (env : Environment) : Json :=
  .arr #[boundaryMatchStateJson (Match.matchEqnsExt.getState env),
    equationStateJson (eqnsExt.getState env), boundarySparseCacheJson env]

private def localHelperState (env : Environment) (name : Name) : Json :=
  .arr #[boundaryMatchStateJson (Match.matchEqnsExt.getState env
      (asyncMode := .async .asyncEnv) (asyncDecl := name)),
    equationStateJson (eqnsExt.getState env (asyncMode := .async .asyncEnv) (asyncDecl := name)),
    boundarySparseCacheJson env (some name)]

private def localSequenceJson (s : LocalSequence) : Json :=
  .arr #[.str "boundary_local_cached_sequence_v1", nameArrayJson s.added,
    nameArrayJson s.publicAdded, nameArrayJson s.fresh, s.beforeState, s.afterState,
    .arr #[encodeBoundaryName s.owner, encodeBoundaryName s.key, s.witness, s.descriptor, .str s.equation],
    .arr s.steps]

def isBoundaryLocalSequence (source : String) : Bool :=
  match (Json.parse source).toOption with
  | some (.arr values) => values[0]? == some (.str "boundary_local_cached_sequence_v1")
  | _ => false

def encodeBoundaryLocalSequence? (before stock : Environment) (checkedBefore : NameSet)
    (declarations : Array Name) (equations matchers : Array (Name × String))
    (helpers : Array TheoremVal) : MetaM (Option (Name × String)) := withEnv stock do
  let added ← branchDelta before stock
  if !(added.any checkedBefore.contains && added.any (!checkedBefore.contains ·)) then return none
  let groups ← candidateGroups stock
  let localGroups := groups.filter fun group => !stock.isImportedConst group.owner &&
    added.contains group.key
  if localGroups.isEmpty || helpers.isEmpty then return none
  unless localGroups.size == 1 && equations.isEmpty && matchers.isEmpty do
    throwError "boundary_local_sequence_root_shape"
  let group := localGroups[0]!
  let key := group.key
  let publicAdded ← branchDelta before stock true
  let fresh := added.filter (!checkedBefore.contains ·)
  unless group.members == #[key] && group.publicMembers == #[key] &&
      checkedBefore.contains key && !before.containsOnBranch key &&
      fresh.qsort Name.quickLt == declarations.qsort Name.quickLt &&
      fresh.qsort Name.quickLt == (helpers.map (·.name)).qsort Name.quickLt &&
      added.size == helpers.size + 1 && publicAdded.contains key do
    throwError "boundary_local_sequence_cover"
  let witness ← withEnv before <| localOwnerWitness before group.owner
  unless witness == (← localOwnerWitness stock group.owner) do
    throwError "boundary_local_sequence_owner_changed"
  let descriptor ← withEnv before <| localCachedDescriptor before group.owner key
  unless descriptor == (← localCachedDescriptor stock group.owner key) do
    throwError "boundary_local_sequence_descriptor_changed"
  let some (.thmInfo thm) := stock.checked.get.find? key
    | throwError "boundary_local_sequence_root_kind"
  let mapping := (eqnsExt.getState stock).mapInv.find? key
  unless mapping.isNone || mapping == some group.owner do
    throwError "boundary_local_sequence_root_mapping"
  let equation ← encodeBoundaryEquation group.owner thm
    (defeqAttr.hasTag stock key) (backwardDefeqAttr.hasTag stock key) mapping.isSome
  let mut available := #[]
  let mut steps := #[]
  let mut stateEnv := before
  for name in added do
    if name == key then
      -- Cached activation preserves caller extensions, apart from the exact
      -- equation registration recorded here. Per-step replay checks this.
      if mapping.isSome then
        stateEnv := eqnsExt.modifyState stateEnv fun state =>
          { state with mapInv := state.mapInv.insert key group.owner }
      steps := steps.push (.arr #[.str "root", localSequenceState stateEnv])
    else
      let some helper := helpers.find? (·.name == name)
        | throwError "boundary_local_sequence_missing_helper"
      unless !(groups.any fun candidate => candidate.members.contains name) do
        throwError "boundary_local_sequence_helper_overlap"
      let dependencies := (helper.type.foldConsts (init := {}) fun n names => names.insert n : NameSet).merge
        (helper.value.foldConsts (init := {}) fun n names => names.insert n : NameSet)
      unless dependencies.toArray.all (fun n => before.containsOnBranch n || available.contains n) do
        throwError "boundary_local_sequence_helper_dependency_order"
      let source ← encodeBoundaryLocalTheorem before helper
      let payload := (Json.arr #[.str "boundary_local_theorems_bundle_v1", encodeBoundaryName name,
        .arr #[.arr #[encodeBoundaryName name, .str source]]]).compress
      let snapshot := localHelperState stock name
      unless snapshot == localSequenceState stateEnv do
        throwError "boundary_local_sequence_helper_capture_snapshot"
      steps := steps.push (.arr #[.str "helper", encodeBoundaryName name, .str payload,
        .bool (publicAdded.contains name), snapshot])
    available := available.push name
  let sequence : LocalSequence := {
    added, publicAdded, fresh, key, witness, descriptor, equation, steps
    owner := group.owner
    beforeState := localSequenceState before
    afterState := localSequenceState stock }
  return some (added[0]!, (localSequenceJson sequence).compress)

private def parseLocalSequence (anchor : Name) (source : String) : MetaM LocalSequence := do
  let .arr #[.str "boundary_local_cached_sequence_v1", added, publicAdded, fresh, beforeState, afterState,
      .arr #[owner, key, witness, descriptor, .str equation], .arr steps] ← ofExcept (Json.parse source)
    | throwError "boundary_local_sequence_payload"
  let added ← namesFromJson added
  let publicAdded ← namesFromJson publicAdded
  let fresh ← namesFromJson fresh
  let owner ← ofExcept (decodeBoundaryName owner)
  let key ← ofExcept (decodeBoundaryName key)
  unless added[0]? == some anchor && fresh.size + 1 == added.size && !fresh.isEmpty &&
      added.filter (· != key) == fresh && publicAdded.contains key &&
      !isPrivateName key && key.getPrefix == owner do
    throwError "boundary_local_sequence_identity"
  let (equationOwner, _, _, _, _) ← ofExcept (parseEquationPayload equation)
  unless equationOwner == owner do throwError "boundary_local_sequence_equation_owner"
  validateEquationAnchor owner key
  let mut seen := #[]
  let mut seenPublic := #[]
  for step in steps do
    match step with
    | .arr #[.str "root", _] =>
      if seen.contains key then throwError "boundary_local_sequence_duplicate_root"
      seen := seen.push key
      seenPublic := seenPublic.push key
    | .arr #[.str "helper", name, .str payload, .bool publicMember, _] =>
      let name ← ofExcept (decodeBoundaryName name)
      unless fresh.contains name && !seen.contains name &&
          (← boundaryLocalTheoremNames name payload) == #[name] do
        throwError "boundary_local_sequence_helper_identity"
      seen := seen.push name
      if publicMember then seenPublic := seenPublic.push name
    | _ => throwError "boundary_local_sequence_step"
  unless seen == added && seenPublic == publicAdded do throwError "boundary_local_sequence_order"
  return { added, publicAdded, fresh, beforeState, afterState, owner, key, witness, descriptor, equation, steps }

def executeBoundaryLocalSequence (anchor : Name) (source : String) : MetaM Unit := do
  let sequence ← parseLocalSequence anchor source
  let before ← getEnv
  unless sequence.added.all (!before.containsOnBranch ·) &&
      localSequenceState before == sequence.beforeState do throwError "boundary_local_sequence_before"
  -- Authenticate the original caller before any helper can change its domain.
  unless (← localOwnerWitness before sequence.owner) == sequence.witness &&
      (← localCachedDescriptor before sequence.owner sequence.key) == sequence.descriptor do
    throwError "boundary_local_sequence_original_authentication"
  let checked ← IO.wait before.checked
  unless (checked.find? sequence.key).isSome && sequence.fresh.all (fun name => (checked.find? name).isNone) do
    throwError "boundary_local_sequence_checked_partition"
  let mut seen := #[]
  let mut seenPublic := #[]
  for step in sequence.steps do
    let expected ← match step with
    | .arr #[.str "root", expected] => do
      executeLocalCachedRoot sequence.owner sequence.key sequence.witness sequence.descriptor sequence.equation
      seen := seen.push sequence.key
      seenPublic := seenPublic.push sequence.key
      pure expected
    | .arr #[.str "helper", name, .str payload, .bool publicMember, expected] => do
      let name ← ofExcept (decodeBoundaryName name)
      executeBoundaryLocalTheorems name payload
      unless localHelperState (← getEnv) name == expected do
        throwError "boundary_local_sequence_helper_snapshot"
      seen := seen.push name
      if publicMember then seenPublic := seenPublic.push name
      pure expected
    | _ => throwError "boundary_local_sequence_step"
    unless (← branchDelta before (← getEnv)) == seen &&
        (← branchDelta before (← getEnv) true) == seenPublic && localSequenceState (← getEnv) == expected do
      throwError "boundary_local_sequence_transition"
  unless localSequenceState (← getEnv) == sequence.afterState &&
      (← localOwnerWitness (← getEnv) sequence.owner) == sequence.witness &&
      (← localCachedDescriptor (← getEnv) sequence.owner sequence.key) == sequence.descriptor do
    throwError "boundary_local_sequence_after"

def boundaryLocalSequenceMembers (anchor : Name) (source : String) :
    MetaM (Array Name × Array Name × Array (Name × String)) := do
  let sequence ← parseLocalSequence anchor source
  let helpers ← sequence.steps.foldlM (init := #[]) fun helpers step => do
    match step with
    | .arr #[.str "helper", name, .str payload, .bool _, _] =>
      return helpers.push (← ofExcept (decodeBoundaryName name), payload)
    | _ => return helpers
  return (sequence.added, #[], helpers)

end ExplicitLean.SimpEngine.Boundary
