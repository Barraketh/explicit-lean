module
prelude

public import Init.Prelude
public meta import ExplicitLean.SimpEngine.Boundary.RealizationCodec
public meta import ExplicitLean.SimpEngine.Boundary.LocalTheoremCodec
public meta import ExplicitLean.SimpEngine.Boundary.CongruenceSequenceCodec
public meta import ExplicitLean.SimpEngine.Boundary.LocalSequenceCodec
meta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
meta import all ExplicitLean.SimpEngine.Boundary.EquationCodec
meta import all ExplicitLean.SimpEngine.Boundary.MatcherCodec

public meta section
open Lean Meta
namespace ExplicitLean.SimpEngine.Boundary

/- A mixed sequence is a separate contract from uniform realization batches.
   Its only direct leaves are ordinary closed theorem helpers; realization
   producers retain the existing bounded recursive closure contract. -/
private inductive SequenceCandidate where
  | group (value : CachedGroup)
  | helper (name : Name) (publicMember : Bool)
  deriving Inhabited

private def SequenceCandidate.key : SequenceCandidate → Name
  | .group value => value.key
  | .helper name _ => name

private def SequenceCandidate.members : SequenceCandidate → Array Name
  | .group value => value.members
  | .helper name _ => #[name]

private def SequenceCandidate.publicMembers : SequenceCandidate → Array Name
  | .group value => value.publicMembers
  | .helper name publicMember => if publicMember then #[name] else #[]

private partial def sequenceCovers (candidates : Array SequenceCandidate)
    (privateNames publicNames : Array Name) (activePrivate activePublic : Array Name := #[]) :
    Array (Array SequenceCandidate) := Id.run do
  if privateNames.isEmpty then return if publicNames.isEmpty then #[#[]] else #[]
  let mut results := #[]
  for candidate in candidates do
    if activePrivate.contains candidate.key then continue
    let newPrivate := candidate.members.filter (!activePrivate.contains ·)
    let newPublic := candidate.publicMembers.filter (!activePublic.contains ·)
    if newPrivate.isEmpty || privateNames.take newPrivate.size != newPrivate ||
        publicNames.take newPublic.size != newPublic then continue
    for suffix in sequenceCovers candidates (privateNames.drop newPrivate.size)
        (publicNames.drop newPublic.size) (activePrivate ++ newPrivate) (activePublic ++ newPublic) do
      results := results.push (#[candidate] ++ suffix)
      if results.size > 1 then return results
  return results

private inductive SequenceStep where
  | group (index : Nat)
  | helper (name : Name) (payload : String) (publicMember : Bool) (equations : Json)
  | registration (name : Name) (payload : String)
  deriving Inhabited

private structure RealizationSequence where
  added : Array Name
  publicAdded : Array Name
  fresh : Array Name
  matchBefore : Json
  matchAfter : Json
  equationBefore : Json
  equationAfter : Json
  sparseBefore : Json
  sparseAfter : Json
  nodes : Array RealizationNode
  cached : Array Bool
  steps : Array SequenceStep

private def sequenceStepJson : SequenceStep → Json
  | .group index => .arr #[.str "group", toJson index]
  | .helper name source publicMember equations =>
      .arr #[.str "helper", encodeBoundaryName name, .str source, .bool publicMember, equations]
  | .registration name source => .arr #[.str "registration", encodeBoundaryName name, .str source]

private def sequenceJson (sequence : RealizationSequence) : Json :=
  .arr #[.str "boundary_realization_sequence_v1", nameArrayJson sequence.added,
    nameArrayJson sequence.publicAdded, nameArrayJson sequence.fresh,
    sequence.matchBefore, sequence.matchAfter, sequence.equationBefore, sequence.equationAfter,
    sequence.sparseBefore, sequence.sparseAfter,
    .arr (sequence.nodes.map realizationNodeJson), toJson sequence.cached,
    .arr (sequence.steps.map sequenceStepJson)]

def isBoundaryRealizationSequence (source : String) : Bool :=
  isBoundaryCongruenceSequence source || isBoundaryLocalSequence source || match (Json.parse source).toOption with
  | some (.arr values) => values[0]? == some (.str "boundary_realization_sequence_v1")
  | _ => false

private def activeRegistrationSignature (env : Environment) (owner name : Name) : MetaM Json := do
  unless !isPrivateName name && env.isImportedConst owner && env.isImportedConst name &&
      env.containsOnBranch owner && env.containsOnBranch name && name.getPrefix == owner do
    throwError "boundary_sequence_registration_not_active_import"
  let .str _ suffix := name | throwError "boundary_sequence_registration_name"
  unless isEqnLikeSuffix suffix do throwError "boundary_sequence_registration_name"
  let some info := env.constants.find? name
    | throwError "boundary_sequence_registration_not_checked_theorem"
  let signature ← match info with
    | .thmInfo _ => constantSignature info (structural := true)
    | .axiomInfo value => do
      unless !value.isUnsafe && getOriginalConstKind? env name == some .thm do
        throwError "boundary_sequence_registration_not_original_theorem"
      constantSignature info (publicProofView := true) (structural := true)
    | _ => throwError "boundary_sequence_registration_not_checked_theorem"
  return .arr #[.str "boundary_active_equation_registration_v1", encodeBoundaryName owner,
    encodeBoundaryName name, signature,
    .bool (defeqAttr.hasTag env name), .bool (backwardDefeqAttr.hasTag env name)]

private def authenticateActiveRegistration (env : Environment) (name : Name) (source : String) : MetaM Name := do
  let json ← ofExcept (Json.parse source)
  let .arr #[.str "boundary_active_equation_registration_v1", owner, nameJson, _, .bool _, .bool _] := json
    | throwError "boundary_sequence_registration_payload"
  let owner ← ofExcept (decodeBoundaryName owner)
  unless (← ofExcept (decodeBoundaryName nameJson)) == name &&
      (← activeRegistrationSignature env owner name) == json do
    throwError "boundary_sequence_registration_signature"
  return owner

private def executeActiveRegistration (name : Name) (source : String) : MetaM Unit := do
  let owner ← authenticateActiveRegistration (← getEnv) name source
  if ((eqnsExt.getState (← getEnv)).mapInv.find? name).isSome then
    throwError "boundary_sequence_registration_collision"
  -- The only effect is this absent-key insertion. No realizeConst, theorem
  -- insertion, defeq check, attribute inference, or name allocation runs here.
  modifyEnv fun env => eqnsExt.modifyState env fun state =>
    { state with mapInv := state.mapInv.insert name owner }

/-- Only a genuine mixed checked/fresh branch delta enters this contract.
    Unsupported mixed effects throw instead of falling back to sorted actions. -/
def encodeBoundaryRealizationSequence? (before stock : Environment) (checkedBefore : NameSet)
    (declarations : Array Name) (equations matchers : Array (Name × String))
    (helpers : Array TheoremVal) : MetaM (Option (Name × String)) := withEnv stock do
  if let some sequence ← encodeBoundaryLocalSequence? before stock checkedBefore declarations equations matchers helpers then
    return some sequence
  let added ← branchDelta before stock
  if !(added.any checkedBefore.contains && added.any (!checkedBefore.contains ·)) then return none
  if helpers.size > 1 then throwError "boundary_sequence_multiple_helpers_unsupported"
  let publicAdded ← branchDelta before stock true
  let fresh := added.filter (!checkedBefore.contains ·)
  unless fresh.qsort Name.quickLt == declarations.qsort Name.quickLt do
    throwError "boundary_sequence_unclaimed_checked_delta"
  let groups ← candidateGroups stock
  let eligible := groups.filter fun group => !group.members.isEmpty &&
    group.members.all added.contains && group.members.all (!before.containsOnBranch ·) &&
    !isPrivateName group.key && group.key.getPrefix == group.owner && stock.isImportedConst group.owner
  let mut candidates := eligible.map SequenceCandidate.group
  for helper in helpers do
    unless fresh.contains helper.name &&
        !(groups.any fun group => group.members.contains helper.name) do
      throwError "boundary_sequence_helper_realization_overlap"
    candidates := candidates.push (.helper helper.name (publicAdded.contains helper.name))
  let covers := sequenceCovers candidates added publicAdded
  unless covers.size == 1 do throwError "boundary_sequence_ambiguous_or_missing_cover"
  let mut nodes : Array RealizationNode := #[]
  let mut steps := #[]
  let mut available := #[]
  for candidate in covers[0]! do
    match candidate with
    | .group group =>
      let cached := group.members.all checkedBefore.contains
      unless cached || group.members.all (!checkedBefore.contains ·) do
        throwError "boundary_sequence_mixed_root_closure"
      let (index, newNodes) ← (captureRealizationNode 3 stock cached groups equations matchers group).run nodes
      nodes := newNodes
      steps := steps.push (.group index)
    | .helper name publicMember =>
      let some helper := helpers.find? (·.name == name)
        | throwError "boundary_sequence_missing_helper"
      let dependencies := (helper.type.foldConsts (init := {}) fun name names => names.insert name : NameSet).merge
        (helper.value.foldConsts (init := {}) fun name names => names.insert name : NameSet)
      unless dependencies.toArray.all (fun name => before.containsOnBranch name || available.contains name) do
        throwError "boundary_sequence_helper_dependency_order"
      let source ← encodeBoundaryLocalTheorem before helper
      let payload := (Json.arr #[.str "boundary_local_theorems_bundle_v1", encodeBoundaryName name,
        .arr #[.arr #[encodeBoundaryName name, .str source]]]).compress
      let equations := equationStateJson (eqnsExt.getState stock
        (asyncMode := .async .asyncEnv) (asyncDecl := name))
      steps := steps.push (.helper name payload publicMember equations)
    available := available ++ candidate.members.filter (!available.contains ·)
  let cached ← nodes.mapM fun node => do
    let (members, _) ← descriptorNames node.owner node.key node.descriptor
    let cached := members.all checkedBefore.contains
    unless cached || members.all (!checkedBefore.contains ·) do
      throwError "boundary_sequence_mixed_node_closure"
    return cached
  let freshNodes := (nodes.zip cached).filter (!·.2) |>.map (·.1)
  unless (freshNodes.filter (·.kind == "equation") |>.map (·.key)).qsort Name.quickLt ==
      (equations.map (·.1)).qsort Name.quickLt &&
      (freshNodes.filter (·.kind == "matcher") |>.map (·.owner)).qsort Name.quickLt ==
      (matchers.map (·.1)).qsort Name.quickLt do
    throwError "boundary_sequence_unclaimed_actions"
  let beforeMap := (eqnsExt.getState before).mapInv
  let afterMap := (eqnsExt.getState stock).mapInv
  unless beforeMap.toArray.all (fun (name, owner) => afterMap.find? name == some owner) do
    throwError "boundary_sequence_changed_prior_equation_mapping"
  let mut registrations := #[]
  for (name, owner) in afterMap.toArray.qsort (fun a b => Name.quickLt a.1 b.1) do
    if (beforeMap.find? name).isSome || nodes.any (·.key == name) then continue
    let source := (← activeRegistrationSignature before owner name).compress
    registrations := registrations.push (SequenceStep.registration name source)
  -- Imported cached activations preserve the caller's base extensions. These
  -- disjoint, absent-key insertions commute with them, but not with creation of
  -- a helper whose async snapshot observes the map. Canonically place them just
  -- before the sole helper (or after roots when there is no helper).
  if !registrations.isEmpty then
    let mut inserted := false
    let mut ordered := #[]
    for step in steps do
      if let .helper .. := step then
        ordered := ordered ++ registrations
        inserted := true
      ordered := ordered.push step
    steps := if inserted then ordered else ordered ++ registrations
  let sequence : RealizationSequence := {
    added, publicAdded, fresh, nodes, cached, steps
    matchBefore := boundaryMatchStateJson (Match.matchEqnsExt.getState before)
    matchAfter := boundaryMatchStateJson (Match.matchEqnsExt.getState stock)
    equationBefore := equationStateJson (eqnsExt.getState before)
    equationAfter := equationStateJson (eqnsExt.getState stock)
    sparseBefore := boundarySparseCacheJson before
    sparseAfter := boundarySparseCacheJson stock }
  return some (covers[0]![0]!.key, (sequenceJson sequence).compress)

private def parseSequence (expectedAnchor : Name) (source : String) : MetaM RealizationSequence := do
  let .arr #[.str "boundary_realization_sequence_v1", added, publicAdded, fresh,
      matchBefore, matchAfter, equationBefore, equationAfter, sparseBefore, sparseAfter,
      .arr values, .arr modes, .arr stepValues] ← ofExcept (Json.parse source)
    | throwError "boundary_sequence_invalid_payload"
  let added ← namesFromJson added
  let publicAdded ← namesFromJson publicAdded
  let fresh ← namesFromJson fresh
  let cached ← modes.mapM (Lean.ofExcept ∘ Json.getBool?)
  unless values.size == cached.size && !values.isEmpty && !stepValues.isEmpty do
    throwError "boundary_sequence_invalid_modes"
  -- Child modes must agree, so every reachable closure uses exactly the old
  -- homogeneous recursive contract. Independent roots may use another mode.
  let mut nodes : Array RealizationNode := #[]
  let mut depths : Array Nat := #[]
  for i in [:values.size] do
    let .arr #[.str kind, owner, key, payload, .arr children, descriptor] := values[i]!
      | throwError "boundary_sequence_invalid_node"
    let owner ← ofExcept (decodeBoundaryName owner)
    let key ← ofExcept (decodeBoundaryName key)
    unless (← getEnv).isImportedConst owner && !key.isAnonymous &&
        !(nodes.any fun node => node.owner == owner && node.key == key) do
      throwError "boundary_sequence_node_identity"
    let children ← children.mapM (Lean.ofExcept ∘ Json.getNat?)
    unless children.all (· < i) && children.toList.eraseDups.length == children.size &&
        children.all (fun child => cached[child]! == cached[i]!) do
      throwError "boundary_sequence_child_mode_or_order"
    let depth := children.foldl (fun depth child => max depth (depths[child]! + 1)) 0
    if depth > 2 then throwError "boundary_sequence_depth_unsupported"
    let (members, publicMembers) ← descriptorNames owner key descriptor
    if kind == "matcher" then
      unless isPrivateName key && children.isEmpty && publicMembers.isEmpty do
        throwError "boundary_sequence_invalid_matcher"
      if cached[i]! then
        unless payload == .null do throwError "boundary_sequence_cached_matcher_producer"
      else
        let .str source := payload | throwError "boundary_sequence_missing_matcher"
        unless (← ofExcept (parseMatcher source)).declarationOrder.isSome &&
            (← boundaryMatcherDeclarationNames owner source) == members do
          throwError "boundary_sequence_matcher_members"
    else if kind == "equation" then
      let .str source := payload | throwError "boundary_sequence_missing_equation"
      let (equationOwner, _, _, _, _) ← ofExcept (parseEquationPayload source)
      unless equationOwner == owner && !isPrivateName key do
        throwError "boundary_sequence_equation_owner"
      validateEquationAnchor owner key
      let mut childMembers := #[]
      let mut childPublic := #[]
      for child in children do
        let node := nodes[child]!
        let (privateNames, publicNames) ← descriptorNames node.owner node.key node.descriptor
        childMembers := childMembers ++ privateNames
        childPublic := childPublic ++ publicNames
        if node.kind == "equation" then
          let .str source := node.source | throwError "boundary_sequence_missing_equation"
          let (_, _, _, _, registration) ← ofExcept (parseEquationPayload source)
          if registration then throwError "boundary_sequence_nested_registration"
      unless childMembers.push key == members && childPublic.push key == publicMembers do
        throwError "boundary_sequence_nested_closure"
    else throwError "boundary_sequence_unknown_node"
    nodes := nodes.push { kind, owner, key, source := payload, children, descriptor }
    depths := depths.push depth
  let mut steps := #[]
  let mut reachable := #[]
  let mut seen := #[]
  let mut seenPublic := #[]
  let mut seenFresh := #[]
  let mut helperCount := 0
  let mut registrations : Array Name := #[]
  for value in stepValues do
    if let .arr #[.str "registration", name, .str payload] := value then
      let name ← ofExcept (decodeBoundaryName name)
      if added.contains name || registrations.contains name then
        throwError "boundary_sequence_registration_overlap"
      discard <| authenticateActiveRegistration (← getEnv) name payload
      registrations := registrations.push name
      steps := steps.push (.registration name payload)
      continue
    let (step, key, members, publicMembers, isFresh) ← match value with
    | .arr #[.str "group", index] => do
      let index ← ofExcept index.getNat?
      unless index < nodes.size && nodes[index]!.kind == "equation" do
        throwError "boundary_sequence_invalid_root"
      let node := nodes[index]!
      let (members, publicMembers) ← descriptorNames node.owner node.key node.descriptor
      reachable := reachable.push index
      pure (SequenceStep.group index, node.key, members, publicMembers, !cached[index]!)
    | .arr #[.str "helper", name, .str payload, .bool publicMember, equations] => do
      helperCount := helperCount + 1
      let name ← ofExcept (decodeBoundaryName name)
      unless (← boundaryLocalTheoremNames name payload) == #[name] do
        throwError "boundary_sequence_invalid_helper"
      for node in nodes do
        let (members, _) ← descriptorNames node.owner node.key node.descriptor
        if members.contains name then throwError "boundary_sequence_helper_realization_overlap"
      pure (SequenceStep.helper name payload publicMember equations, name, #[name],
        if publicMember then #[name] else #[], true)
    | _ => throwError "boundary_sequence_invalid_step"
    if seen.isEmpty && key != expectedAnchor then throwError "boundary_sequence_foreign_anchor"
    if seen.contains key then throwError "boundary_sequence_root_already_active"
    let newMembers := members.filter (!seen.contains ·)
    unless newMembers.all (fun name => fresh.contains name == isFresh) do
      throwError "boundary_sequence_fresh_membership"
    seen := seen ++ newMembers
    seenPublic := seenPublic ++ publicMembers.filter (!seenPublic.contains ·)
    if isFresh then seenFresh := seenFresh ++ newMembers
    steps := steps.push step
  if helperCount > 1 then throwError "boundary_sequence_multiple_helpers_unsupported"
  for i in (List.range nodes.size).reverse do
    if reachable.contains i then
      for child in nodes[i]!.children do
        if !reachable.contains child then reachable := reachable.push child
  unless reachable.size == nodes.size && seen == added && seenPublic == publicAdded && seenFresh == fresh &&
      !fresh.isEmpty && fresh.size < added.size do
    throwError "boundary_sequence_cover_or_delta"
  return {
    added := added
    publicAdded := publicAdded
    fresh := fresh
    matchBefore := matchBefore
    matchAfter := matchAfter
    equationBefore := equationBefore
    equationAfter := equationAfter
    sparseBefore := sparseBefore
    sparseAfter := sparseAfter
    nodes := nodes
    cached := cached
    steps := steps }

private partial def preflightSequenceNode (nodes : Array RealizationNode) (index : Nat) : MetaM Unit := do
  let node := nodes[index]!
  discard <| completedCacheResult (← getEnv) node.owner node.key
  for child in node.children do preflightSequenceNode nodes child

private partial def executeSequenceNode (sequence : RealizationSequence) (index : Nat) : MetaM Unit := do
  let node := sequence.nodes[index]!
  if (← getEnv).containsOnBranch node.key then throwError "boundary_sequence_root_already_active"
  let existing ← lookupCacheTask (← getEnv) node.owner node.key
  let reuse := sequence.cached[index]! || existing.isSome
  if reuse then preflightSequenceNode sequence.nodes index
  if node.kind == "matcher" then
    if reuse then realizeBoundaryConst node.owner node.key (throwError "boundary_realization_forbidden_callback")
    else
      let .str source := node.source | throwError "boundary_sequence_missing_matcher"
      executeBoundaryMatcher node.owner source
    let state := Match.matchEqnsExt.getState (← getEnv)
      (asyncMode := .async .asyncEnv) (asyncDecl := node.key)
    unless (state.map.find? node.owner).map (·.splitterName) == some node.key do
      throwError "boundary_sequence_matcher_key"
  else
    let .str source := node.source | throwError "boundary_sequence_missing_equation"
    let (_, theoremSource, defeqTag, backwardTag, registration) ← ofExcept (parseEquationPayload source)
    if reuse then realizeBoundaryConst node.owner node.key (throwError "boundary_realization_forbidden_callback")
    else
      realizeBoundaryConst node.owner node.key do
        unless boundaryMatchStateJson (Match.matchEqnsExt.getState (← getEnv)) == .arr #[.arr #[], .arr #[]] &&
            equationStateJson (eqnsExt.getState (← getEnv)) == .arr #[] &&
            boundarySparseCacheJson (← getEnv) == .arr #[] && (auxLemmasExt.getState (← getEnv)).lemmas.isEmpty do
          throwError "boundary_sequence_nonempty_producer_context"
        for child in node.children do executeSequenceNode sequence child
        realizeCapturedEquation node.key theoremSource defeqTag backwardTag
    executeBoundaryTheorem node.key theoremSource
    unless defeqAttr.hasTag (← getEnv) node.key == defeqTag &&
        backwardDefeqAttr.hasTag (← getEnv) node.key == backwardTag do
      throwError "boundary_sequence_equation_tags"
    registerCapturedEquation node.owner node.key registration

private def executeSequence (anchor : Name) (source : String) : MetaM Unit := do
  let sequence ← parseSequence anchor source
  let before ← getEnv
  unless sequence.added.all (!before.containsOnBranch ·) &&
      boundaryMatchStateJson (Match.matchEqnsExt.getState before) == sequence.matchBefore &&
      equationStateJson (eqnsExt.getState before) == sequence.equationBefore &&
      boundarySparseCacheJson before == sequence.sparseBefore do
    throwError "boundary_sequence_caller_before"
  -- Check imported/active membership against the original caller, not against
  -- a state in which an earlier root might have activated an unavailable key.
  for step in sequence.steps do
    if let .registration name source := step then
      discard <| authenticateActiveRegistration before name source
      if ((eqnsExt.getState before).mapInv.find? name).isSome then
        throwError "boundary_sequence_registration_collision"
  let mut seen := #[]
  let mut seenPublic := #[]
  for step in sequence.steps do
    let (members, publicMembers) ← match step with
    | .group index => do
      let node := sequence.nodes[index]!
      executeSequenceNode sequence index
      descriptorNames node.owner node.key node.descriptor
    | .helper name payload publicMember equations => do
      executeBoundaryLocalTheorems name payload
      unless equationStateJson (eqnsExt.getState (← getEnv)
          (asyncMode := .async .asyncEnv) (asyncDecl := name)) == equations do
        throwError "boundary_sequence_helper_equation_snapshot"
      pure (#[name], if publicMember then #[name] else #[])
    | .registration name source => do
      executeActiveRegistration name source
      pure (#[], #[])
    seen := seen ++ members.filter (!seen.contains ·)
    seenPublic := seenPublic ++ publicMembers.filter (!seenPublic.contains ·)
    unless (← branchDelta before (← getEnv)) == seen &&
        (← branchDelta before (← getEnv) true) == seenPublic do
      throwError "boundary_sequence_branch_transition"
  -- Persistent exporters require the final checked domain. Every descriptor is
  -- mandatory here; no successful sequence can return an unchecked receipt.
  for node in sequence.nodes do checkDescriptor node.owner node.key node.descriptor
  let after ← getEnv
  unless boundaryMatchStateJson (Match.matchEqnsExt.getState after) == sequence.matchAfter do
    throwError "boundary_sequence_caller_after:match"
  unless equationStateJson (eqnsExt.getState after) == sequence.equationAfter do
    throwError "boundary_sequence_caller_after:equations:expected={sequence.equationAfter.compress}:actual={(equationStateJson (eqnsExt.getState after)).compress}"
  unless boundarySparseCacheJson after == sequence.sparseAfter do
    throwError "boundary_sequence_caller_after:sparse"

def executeBoundaryRealizationEffects (anchor : Name) (source : String) : MetaM Unit := do
  if isBoundaryCongruenceSequence source then executeBoundaryCongruenceSequence anchor source
  else if isBoundaryLocalSequence source then executeBoundaryLocalSequence anchor source
  else if isBoundaryRealizationSequence source then executeSequence anchor source
  else executeBoundaryRealizationBatch anchor source

/-- Required members, freshly declared public group members, and exact helper
    payloads are distinct. Boundary must retain all helper-specific checks. -/
def boundaryRealizationSequenceMembers (anchor : Name) (source : String) :
    MetaM (Array Name × Array Name × Array (Name × String)) := do
  if isBoundaryCongruenceSequence source then return ← boundaryCongruenceSequenceMembers anchor source
  if isBoundaryLocalSequence source then return ← boundaryLocalSequenceMembers anchor source
  let sequence ← parseSequence anchor source
  let helpers := sequence.steps.filterMap fun step => match step with
    | .helper name payload _ _ => some (name, payload)
    | _ => none
  let newPublic := sequence.publicAdded.filter fun name => sequence.fresh.contains name &&
    !(helpers.any (·.1 == name))
  return (sequence.added, newPublic, helpers)

end ExplicitLean.SimpEngine.Boundary
