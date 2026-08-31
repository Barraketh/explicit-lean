module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.ModuleDataObservation
public meta import ExplicitLean.SimpEngine.Boundary.EquationCodec
public meta import ExplicitLean.SimpEngine.Boundary.MatcherCodec
public meta import Lean.Meta.Tactic.AuxLemma
public meta import ExplicitLean.SimpEngine.Boundary.SparseCasesCodec
meta import all Lean.Environment
meta import all Lean.Meta.Basic
meta import all ExplicitLean.SimpEngine.Boundary.EquationCodec
meta import all ExplicitLean.SimpEngine.Boundary.MatcherCodec

public meta section
open Lean Meta
namespace ExplicitLean.SimpEngine.Boundary

private partial def snapshotQuietFinished (snap : Language.SnapshotTree) : IO Bool := do
  if !snap.element.diagnostics.msgLog.toArray.isEmpty ||
      !snap.element.traces.traces.isEmpty || snap.element.infoTree?.isSome || snap.element.isFatal then
    return false
  for child in snap.children do
    unless ← IO.hasFinished child.task do return false
    unless ← snapshotQuietFinished child.task.get do return false
  return true



private unsafe def lookupCacheTaskImpl (env : Environment) (owner key : Name) : IO (Option (Task Dynamic)) := do
  let ctx ← if env.isImportedConst owner then
      env.importRealizationCtx?.getDM (throw <| IO.userError "activation_missing_import_context")
    else (env.localRealizationCtxMap.find? owner).getDM (throw <| IO.userError "activation_missing_local_context")
  let values ← ctx.realizeMapRef.get
  let some raw := values.find? (TypeName.typeName Environment.RealizeConstKey) | return none
  -- Exactly the heterogeneous map/type key used by pinned Environment.realizeValue.
  let values := unsafeCast (β := PHashMap Environment.RealizeConstKey (Task Dynamic)) raw
  return values.find? { constName := key }

@[implemented_by lookupCacheTaskImpl]
private opaque lookupCacheTask (env : Environment) (owner key : Name) : IO (Option (Task Dynamic))

private def completedCacheResult (env : Environment) (owner key : Name) : IO Environment.RealizeConstResult := do
  let some task ← lookupCacheTask env owner key
    | throw <| IO.userError "activation_cache_absent"
  unless ← IO.hasFinished task do throw <| IO.userError "activation_cache_pending"
  let some result := task.get.get? Environment.RealizeConstResult
    | throw <| IO.userError "activation_cache_type"
  let some status := result.dyn.get? Lean.Meta.RealizeConstantResult
    | throw <| IO.userError "activation_result_type"
  unless status.error?.isNone do throw <| IO.userError "activation_cached_error"
  if let some snapshot := status.snap? then
    unless ← snapshotQuietFinished snapshot do
      throw <| IO.userError s!"activation_nonquiet_snapshot:messages={snapshot.element.diagnostics.msgLog.toArray.size}:traces={snapshot.element.traces.traces.size}:info={snapshot.element.infoTree?.isSome}:fatal={snapshot.element.isFatal}:children={snapshot.children.size}:finished={(← snapshot.children.mapM fun child => IO.hasFinished child.task)}"
  unless result.newConsts.private.any (·.constInfo.name == key) do
    throw <| IO.userError "activation_key_not_member"
  let mut seen : NameSet := {}
  for member in result.newConsts.private do
    if seen.contains member.constInfo.name then throw <| IO.userError "activation_duplicate_member"
    seen := seen.insert member.constInfo.name
    unless member.isRealized do throw <| IO.userError "activation_unrealized_member"
    unless ← IO.hasFinished member.constInfo.constInfo do throw <| IO.userError "activation_pending_declaration"
    unless ← IO.hasFinished member.aconstsImpl do throw <| IO.userError "activation_pending_branch"
    let some exts := member.exts? | throw <| IO.userError "activation_missing_extensions"
    unless ← IO.hasFinished exts do throw <| IO.userError "activation_pending_extensions"
  for member in result.newConsts.public do
    unless seen.contains member.constInfo.name do throw <| IO.userError "activation_foreign_public_member"
    unless ← IO.hasFinished member.constInfo.constInfo do throw <| IO.userError "activation_pending_public_declaration"
    unless ← IO.hasFinished member.aconstsImpl do throw <| IO.userError "activation_pending_public_branch"
    let some exts := member.exts? | throw <| IO.userError "activation_missing_public_extensions"
    unless ← IO.hasFinished exts do throw <| IO.userError "activation_pending_public_extensions"
  return result

private def nameArrayJson (names : Array Name) : Json := .arr (names.map encodeBoundaryName)

private def constantSignature (info : ConstantInfo) (publicProofView := false)
    (structural := false) : MetaM Json := do
  let encode := if structural then encodeBoundaryStructExpr else encodeBoundaryExpr
  let common := #[encodeBoundaryName info.name, nameArrayJson info.levelParams.toArray,
    .str (← encode info.type)]
  match info with
  | .thmInfo info => return .arr (#[.str "theorem"] ++ common ++ #[nameArrayJson info.all.toArray])
  | .defnInfo info =>
    let hints := match info.hints with
      | .opaque => Json.arr #[.str "opaque"]
      | .abbrev => Json.arr #[.str "abbrev"]
      | .regular h => Json.arr #[.str "regular", toJson h.toNat]
    unless info.safety == .safe do throwError "activation_unsafe_definition"
    return .arr (#[.str "definition"] ++ common ++ #[nameArrayJson info.all.toArray,
      hints, .str (← encode info.value)])
  | .axiomInfo info =>
    unless publicProofView && !info.isUnsafe do throwError "activation_unexpected_axiom"
    return .arr (#[.str "public-proof-interface"] ++ common)
  | _ => throwError "activation_unsupported_declaration_kind:{info.name}:axiom={info.isAxiom}"

private unsafe def serializeGroupDataImpl (data : ModuleData) : IO ByteArray := do
  IO.FS.withTempFile fun _ path => do
    let compactor ← CompactedRegion.save path `_boundary_realization_extension data #[] none
    Runtime.forget compactor
    IO.FS.readBinFile path

@[implemented_by serializeGroupDataImpl]
private opaque serializeGroupData (data : ModuleData) : IO ByteArray

private def bytesHex (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut result := ""
  for byte in bytes.data do
    result := result.push digits[byte.toNat / 16]!
    result := result.push digits[byte.toNat % 16]!
  return result

private def memberEnvironment (env : Environment) (member : AsyncConst) : IO Environment := do
  let some exts := member.exts? | throw <| IO.userError "activation_missing_extensions"
  let extensions := exts.get
  let checked := { env.checked.get with extensions }
  return { env with
    checked := .pure checked
    base := {
      «private» := { env.base.private with extensions }
      «public» := { env.base.public with extensions } } }

private def memberMetadata (env : Environment) (member : AsyncConst) : MetaM Json := do
  let view ← memberEnvironment env member
  let aux := auxLemmasExt.getState view
  -- The first bounded group contract admits no auxiliary proof cache effects.
  unless aux.lemmas.isEmpty do throwError "activation_nonempty_aux_cache"
  let matchState := boundaryMatchStateJson (Match.matchEqnsExt.getState view)
  let eqnState := equationStateJson (eqnsExt.getState view)
  let data ← observePrivateModuleData view
  let mut entries := #[]
  for (name, values) in data.entries.qsort (fun a b => Name.quickLt a.1 b.1) do
    -- The same three diagnostic/private-proof bookkeeping exceptions used by
    -- Boundary's persistent-state comparator; no matcher/computation exemption.
    if name == `Lean.declRangeExt ||
        name == "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt".toName ||
        name == "_private.Lean.OriginalConstKind.0.Lean.privateConstKindsExt".toName then continue
    let normalized : ModuleData := {
      isModule := true
      imports := #[]
      constNames := #[]
      constants := #[]
      extraConstNames := #[]
      entries := #[(name, values)] }
    let first ← serializeGroupData normalized
    unless first == (← serializeGroupData normalized) do
      throwError "activation_nondeterministic_extension_serialization"
    entries := entries.push (.arr #[encodeBoundaryName name, .str (bytesHex first)])
  return .arr #[matchState, eqnState, boundarySparseCacheJson view, .arr entries]

private partial def nestedMemberJson (fuel : Nat) (env : Environment)
    (allowed : Array Name) (member : AsyncConst) (publicView : Bool)
    (structural := false) : MetaM Json := do
  if fuel == 0 then throwError "activation_nested_branch_depth"
  unless (← IO.hasFinished member.constInfo.constInfo) &&
      (← IO.hasFinished member.constInfo.sig) && (← IO.hasFinished member.aconstsImpl) do
    throwError "activation_nested_branch_pending"
  let info := member.constInfo.constInfo.get
  let sig := member.constInfo.sig.get
  unless member.constInfo.name == info.name && member.constInfo.kind == ConstantKind.ofConstantInfo info &&
      sig.name == info.name && sig.levelParams == info.levelParams &&
      (if structural then Expr.equal sig.type info.type else sig.type == info.type) do
    throwError "activation_async_signature_conflict"
  let signature ← constantSignature info publicView structural
  let metadata ← match member.exts? with
    | none => pure Json.null
    | some task => do
      unless ← IO.hasFinished task do throwError "activation_nested_extensions_pending"
      memberMetadata env member
  let some children := member.aconstsImpl.get.get? AsyncConsts
    | throwError "activation_nested_branch_type"
  let entries := children.revList.toArray.reverse
  let names := entries.map (·.constInfo.name)
  unless entries.size == children.size && children.map.toArray.size == entries.size &&
      children.normalizedTrie.toArray.size == entries.size && names.all allowed.contains do
    throwError "activation_nested_branch_members"
  let mut seen : NameSet := {}
  let mut nested := #[]
  for child in entries do
    if seen.contains child.constInfo.name then throwError "activation_nested_branch_duplicate"
    seen := seen.insert child.constInfo.name
    let prior := allowed.takeWhile (· != child.constInfo.name)
    let expected ← nestedMemberJson (fuel - 1) env prior child publicView structural
    let some mapped := children.map.find? child.constInfo.name
      | throwError "activation_nested_branch_map"
    let some normalized := children.normalizedTrie.find? (privateToUserName child.constInfo.name)
      | throwError "activation_nested_branch_trie"
    unless (← nestedMemberJson (fuel - 1) env prior mapped publicView structural) == expected &&
        (← nestedMemberJson (fuel - 1) env prior normalized publicView structural) == expected do
      throwError "activation_nested_branch_lookup_conflict"
    nested := nested.push expected
  return .arr #[signature, .bool member.isRealized, metadata, .arr nested]

private def completedCacheDescriptor (env : Environment) (owner key : Name)
    (structural := false) : MetaM Json := do
  let checked ← IO.wait env.checked
  let result ← completedCacheResult env owner key
  let mut privateMembers := #[]
  let mut priorNames := #[]
  for member in result.newConsts.private do
    let info := member.constInfo.constInfo.get
    let some checked := checked.find? info.name
      | throwError "activation_unchecked_member:{info.name}"
    let signature ← constantSignature info (structural := structural)
    unless (← constantSignature checked (structural := structural)) == signature do
      throwError "activation_checked_member_conflict:{info.name}"
    let tree ← nestedMemberJson (result.newConsts.private.length + 1) env priorNames member false structural
    privateMembers := privateMembers.push (.arr #[signature, ← memberMetadata env member, tree])
    priorNames := priorNames.push info.name
  let mut publicMembers := #[]
  priorNames := #[]
  for member in result.newConsts.public do
    let info := member.constInfo.constInfo.get
    let some privateMember := result.newConsts.private.find? (·.constInfo.name == info.name)
      | throwError "activation_foreign_public_member"
    let privateInfo := privateMember.constInfo.constInfo.get
    unless privateInfo.isTheorem && privateInfo.levelParams == info.levelParams &&
        (if structural then Expr.equal privateInfo.type info.type else privateInfo.type == info.type) do
      throwError "activation_public_view_conflict"
    let tree ← nestedMemberJson (result.newConsts.public.length + 1) env priorNames member true structural
    publicMembers := publicMembers.push (.arr #[← constantSignature info true structural,
      ← memberMetadata env member, tree])
    priorNames := priorNames.push info.name
  return .arr #[.str (if structural then "completed_realization_v2" else "completed_realization_v1"), .bool (env.isImportedConst owner),
    encodeBoundaryName owner, encodeBoundaryName key, .arr privateMembers, .arr publicMembers]

/- A group descriptor is a validation witness, never a constructor for Lean's
   internal realization cache. Only the pinned realizeConst API writes it. -/
private structure CachedGroup where
  owner : Name
  key : Name
  members : Array Name
  publicMembers : Array Name
  deriving Inhabited

private unsafe def candidateGroupsImpl (env : Environment) : IO (Array CachedGroup) := do
  let mut contexts := env.localRealizationCtxMap.toArray.map fun (owner, ctx) => (some owner, ctx)
  if let some ctx := env.importRealizationCtx? then contexts := contexts.push (none, ctx)
  let mut groups := #[]
  for (owner?, ctx) in contexts do
    let values ← ctx.realizeMapRef.get
    let some raw := values.find? (TypeName.typeName Environment.RealizeConstKey) | continue
    let values := unsafeCast (β := PHashMap Environment.RealizeConstKey (Task Dynamic)) raw
    for (key, task) in values.toArray do
      unless ← IO.hasFinished task do continue
      let some result := task.get.get? Environment.RealizeConstResult | continue
      let owner := owner?.getD (privateToUserName key.constName |>.getPrefix)
      if owner?.isNone && !env.isImportedConst owner then continue
      groups := groups.push {
        owner, key := key.constName
        members := result.newConsts.private.toArray.map (·.constInfo.name)
        publicMembers := result.newConsts.public.toArray.map (·.constInfo.name) }
  return groups

@[implemented_by candidateGroupsImpl]
private opaque candidateGroups (env : Environment) : IO (Array CachedGroup)

private def branchNames (env : Environment) (publicView := false) : Array Name :=
  let branch := if publicView then env.asyncConstsMap.public else env.asyncConstsMap.private
  branch.revList.toArray.reverse.map (·.constInfo.name)

private def branchDelta (before after : Environment) (publicView := false) : MetaM (Array Name) := do
  let old := branchNames before publicView
  let new := branchNames after publicView
  unless new.extract 0 old.size == old do throwError "boundary_realization_branch_prefix_changed"
  return new.extract old.size new.size

private partial def groupCovers (groups : Array CachedGroup) (names : Array Name)
    (offset : Nat := 0) : Array (Array CachedGroup) := Id.run do
  if offset == names.size then return #[#[]]
  let mut solutions := #[]
  for group in groups do
    if group.members.isEmpty || group.members.size + offset > names.size then continue
    unless names.extract offset (offset + group.members.size) == group.members do continue
    for suffix in groupCovers groups names (offset + group.members.size) do
      solutions := solutions.push (#[group] ++ suffix)
      if solutions.size > 1 then return solutions
  return solutions

private def namesFromJson (json : Json) : MetaM (Array Name) := do
  let values ← ofExcept json.getArr?
  let result ← values.mapM (Lean.ofExcept ∘ decodeBoundaryName)
  let mut seen : NameSet := {}
  for name in result do
    if name.isAnonymous || seen.contains name then throwError "boundary_realization_invalid_names"
    seen := seen.insert name
  return result

private def checkDescriptor (owner key : Name) (expected : Json) : MetaM Unit := do
  let structural := match expected with
    | .arr values => values[0]? == some (.str "completed_realization_v2")
    | _ => false
  let actual ← completedCacheDescriptor (← getEnv) owner key structural
  unless actual == expected do throwError "boundary_realization_cached_descriptor_conflict:{key}"

private def nestedMatcherPayload (source : String) : MetaM String := do
  let bundle ← ofExcept (parseMatcher source)
  unless bundle.equations.all (·.localRegistration.isNone) &&
      boundaryMatchStateJson bundle.localState == .arr #[.arr #[], .arr #[]] do
    throwError "boundary_realization_nonempty_nested_caller"
  -- A nested matcher runs in the imported equation callback, not in the
  -- original theorem caller. The producer below requires this exact empty
  -- callback context; the batch separately authenticates the outer caller.
  let bundle := { bundle with
    localEquationBefore := .arr #[]
    localEquationAfter := .arr #[]
    localSparseState := .arr #[] }
  return (matcherJson bundle).compress

/-- Capture only a unique ordered cover of actual completed realization groups.
    Fresh production initially supports an equation root with zero or more
    independently closed matcher children in the empty imported callback state.
    Every other closure stays unsupported. -/
private def encodeBoundaryRealizationBatchV1? (before stock : Environment) (checkedBefore : NameSet)
    (equations matchers : Array (Name × String)) : MetaM (Option (Name × String)) := do
  let added ← branchDelta before stock
  if added.isEmpty then return none
  let candidates ← candidateGroups stock
  let eligible := candidates.filter fun group => !group.members.isEmpty &&
    group.members.all added.contains && group.members.all (!before.containsOnBranch ·)
  let covers := groupCovers eligible added
  unless covers.size == 1 do throwError "boundary_realization_ambiguous_or_missing_group_cover"
  let groups := covers[0]!
  let cached := added.all checkedBefore.contains
  unless cached || added.all (!checkedBefore.contains ·) do
    throwError "boundary_realization_mixed_checked_closure"
  -- Preserve the old narrow action paths unless this boundary needs grouped
  -- production or activation without a checked-declaration delta.
  unless cached || groups.any (fun group => group.members.size > 1 && !isPrivateName group.key) do
    return none
  let mut roots := #[]
  let mut claimedMatchers : Array Name := #[]
  let mut claimedEquations : Array Name := #[]
  for group in groups do
    unless group.key.getPrefix == group.owner && !isPrivateName group.key &&
        stock.isImportedConst group.owner && group.members.back? == some group.key do
      throwError "boundary_realization_unsupported_root"
    let source ← if cached then withEnv stock do
        let some (.thmInfo thm) := stock.checked.get.find? group.key
          | throwError "boundary_realization_root_not_theorem"
        let mapping := (eqnsExt.getState stock).mapInv.find? group.key
        unless mapping.isNone || mapping == some group.owner do
          throwError "boundary_realization_root_mapping"
        encodeBoundaryEquation group.owner thm (defeqAttr.hasTag stock group.key)
          (backwardDefeqAttr.hasTag stock group.key) mapping.isSome
      else
        let some (_, source) := equations.find? (·.1 == group.key)
          | throwError "boundary_realization_missing_captured_root"
        claimedEquations := claimedEquations.push group.key
        pure source
    let childNames := group.members.pop
    let childCandidates := candidates.filter fun child => child.members.size < group.members.size &&
      !child.members.isEmpty && child.members.all childNames.contains
    let childCovers := groupCovers childCandidates childNames
    unless childCovers.size == 1 do throwError "boundary_realization_ambiguous_nested_cover"
    let mut children := #[]
    for child in childCovers[0]! do
      let matcherSource ← if cached then pure Json.null else do
        let some (_, source) := matchers.find? (·.1 == child.owner)
          | throwError "boundary_realization_missing_captured_matcher"
        let names ← withEnv stock <| boundaryMatcherDeclarationNames child.owner source
        unless names == child.members && names.back? == some child.key do
          throwError "boundary_realization_matcher_members_conflict"
        claimedMatchers := claimedMatchers.push child.owner
        pure (.str (← nestedMatcherPayload source))
      children := children.push (.arr #[encodeBoundaryName child.owner,
        encodeBoundaryName child.key, matcherSource,
        ← withEnv stock <| completedCacheDescriptor stock child.owner child.key])
    roots := roots.push (.arr #[encodeBoundaryName group.owner, encodeBoundaryName group.key,
      .str source, .arr children, ← withEnv stock <| completedCacheDescriptor stock group.owner group.key])
  unless cached || (claimedEquations.qsort Name.quickLt == (equations.map (·.1)).qsort Name.quickLt &&
      claimedMatchers.qsort Name.quickLt == (matchers.map (·.1)).qsort Name.quickLt) do
    throwError "boundary_realization_unclaimed_actions"
  let publicAdded ← branchDelta before stock true
  unless publicAdded == groups.flatMap (·.publicMembers) do
    throwError "boundary_realization_public_branch_order"
  let payload := Json.arr #[.str "boundary_realization_batch_v1", .bool cached,
    nameArrayJson added, nameArrayJson publicAdded,
    boundaryMatchStateJson (Match.matchEqnsExt.getState before),
    boundaryMatchStateJson (Match.matchEqnsExt.getState stock),
    equationStateJson (eqnsExt.getState before), equationStateJson (eqnsExt.getState stock),
    boundarySparseCacheJson before, boundarySparseCacheJson stock, .arr roots]
  return some (groups[0]!.key, payload.compress)

private def executeCapturedRoot (children : Array Json) (root : Name)
    (source : String) : MetaM Unit := do
  unless boundaryMatchStateJson (Match.matchEqnsExt.getState (← getEnv)) == .arr #[.arr #[], .arr #[]] &&
      equationStateJson (eqnsExt.getState (← getEnv)) == .arr #[] &&
      boundarySparseCacheJson (← getEnv) == .arr #[] &&
      (auxLemmasExt.getState (← getEnv)).lemmas.isEmpty do
    throwError "boundary_realization_nonempty_producer_context"
  for child in children do
    let .arr #[anchor, _, .str payload, _] := child
      | throwError "boundary_realization_missing_child_producer"
    executeBoundaryMatcher (← ofExcept <| decodeBoundaryName anchor) payload
  let (_, theoremSource, defeqTag, backwardTag, _) ← ofExcept (parseEquationPayload source)
  realizeCapturedEquation root theoremSource defeqTag backwardTag

/-- No generator is invoked. Cached mode preflights completed tasks and uses a
    failure-only callback; producer mode runs only the captured closed closure. -/
private def executeBoundaryRealizationBatchV1 (expectedAnchor : Name) (source : String) : MetaM Unit := do
  let .arr #[.str "boundary_realization_batch_v1", .bool cached, privateNames, publicNames,
      matchBefore, matchAfter, eqnsBefore, eqnsAfter, sparseBefore, sparseAfter, .arr roots] ← ofExcept (Json.parse source)
    | throwError "boundary_realization_invalid_payload"
  unless !roots.isEmpty do throwError "boundary_realization_empty_batch"
  let added ← namesFromJson privateNames
  let publicAdded ← namesFromJson publicNames
  let before ← getEnv
  unless added.all (!before.containsOnBranch ·) do throwError "boundary_realization_members_already_active"
  unless boundaryMatchStateJson (Match.matchEqnsExt.getState before) == matchBefore &&
      equationStateJson (eqnsExt.getState before) == eqnsBefore &&
      boundarySparseCacheJson before == sparseBefore do
    throwError "boundary_realization_caller_before_conflict"
  let mut index := 0
  for item in roots do
    let .arr #[ownerJson, keyJson, .str equationSource, .arr children, descriptor] := item
      | throwError "boundary_realization_invalid_root"
    let owner ← ofExcept (decodeBoundaryName ownerJson)
    let key ← ofExcept (decodeBoundaryName keyJson)
    if index == 0 && key != expectedAnchor then throwError "boundary_realization_foreign_anchor"
    index := index + 1
    let (equationOwner, theoremSource, defeqTag, backwardTag, registerEqn) ←
      ofExcept (parseEquationPayload equationSource)
    unless owner == equationOwner && before.isImportedConst owner do
      throwError "boundary_realization_foreign_owner"
    validateEquationAnchor owner key
    let existing ← lookupCacheTask (← getEnv) owner key
    if cached || existing.isSome then
      -- A fresh producer's recorder trial sees the stock memo before its
      -- declarations are checked on the restored caller branch. Preflight
      -- completion without forcing generation, activate through Lean's checked
      -- path, then require the full descriptor before any continuation.
      if cached then checkDescriptor owner key descriptor
      else discard <| completedCacheResult (← getEnv) owner key
      for child in children do
        let .arr #[childOwner, childKey, _, childDescriptor] := child
          | throwError "boundary_realization_invalid_child"
        let childOwner ← ofExcept <| decodeBoundaryName childOwner
        let childKey ← ofExcept <| decodeBoundaryName childKey
        if cached then checkDescriptor childOwner childKey childDescriptor
        else discard <| completedCacheResult (← getEnv) childOwner childKey
    if cached || existing.isSome then
      realizeConst owner key (throwError "boundary_realization_forbidden_callback")
    else
      realizeConst owner key (executeCapturedRoot children key equationSource)
    -- Presence, exact descriptor and nested metadata are required after either
    -- cache reuse or closed production. No cache entry is forged or coalesced.
    checkDescriptor owner key descriptor
    for child in children do
      let .arr #[childOwner, childKey, _, childDescriptor] := child
        | throwError "boundary_realization_invalid_child"
      checkDescriptor (← ofExcept <| decodeBoundaryName childOwner)
        (← ofExcept <| decodeBoundaryName childKey) childDescriptor
    executeBoundaryTheorem key theoremSource
    unless defeqAttr.hasTag (← getEnv) key == defeqTag &&
        backwardDefeqAttr.hasTag (← getEnv) key == backwardTag do
      throwError "boundary_realization_root_tags"
    registerCapturedEquation owner key registerEqn
  let after ← getEnv
  unless (← branchDelta before after) == added && (← branchDelta before after true) == publicAdded do
    throwError "boundary_realization_branch_transition_conflict"
  unless boundaryMatchStateJson (Match.matchEqnsExt.getState after) == matchAfter &&
      equationStateJson (eqnsExt.getState after) == eqnsAfter &&
      boundarySparseCacheJson after == sparseAfter do
    throwError "boundary_realization_caller_after_conflict"

/- Version two retains complete descriptors but models the actual deduplicating
   activation API. A root may include a completed earlier group's members.
   Nodes are a finite topological producer table, never inferred on replay. -/
private structure RealizationNode where
  kind : String
  owner : Name
  key : Name
  source : Json
  children : Array Nat
  descriptor : Json
  deriving Inhabited

private def realizationNodeJson (node : RealizationNode) : Json :=
  .arr #[.str node.kind, encodeBoundaryName node.owner, encodeBoundaryName node.key,
    node.source, toJson node.children, node.descriptor]

private partial def projectedCovers (groups : Array CachedGroup)
    (privateNames publicNames : Array Name) (activePrivate activePublic : Array Name := #[]) :
    Array (Array CachedGroup) := Id.run do
  if privateNames.isEmpty then return if publicNames.isEmpty then #[#[]] else #[]
  let mut results := #[]
  for group in groups do
    if activePrivate.contains group.key then continue
    let newPrivate := group.members.filter (!activePrivate.contains ·)
    let newPublic := group.publicMembers.filter (!activePublic.contains ·)
    if newPrivate.isEmpty || privateNames.take newPrivate.size != newPrivate ||
        publicNames.take newPublic.size != newPublic then continue
    for suffix in projectedCovers groups (privateNames.drop newPrivate.size)
        (publicNames.drop newPublic.size) (activePrivate ++ newPrivate) (activePublic ++ newPublic) do
      results := results.push (#[group] ++ suffix)
      if results.size > 1 then return results
  return results

private def descriptorNames (owner key : Name) (descriptor : Json) : MetaM (Array Name × Array Name) := do
  let .arr #[.str "completed_realization_v2", .bool true, ownerJson, keyJson,
      .arr privateEntries, .arr publicEntries] := descriptor
    | throwError "boundary_realization_v2_descriptor"
  unless ownerJson == encodeBoundaryName owner && keyJson == encodeBoundaryName key do
    throwError "boundary_realization_v2_descriptor_identity"
  let names ← #[privateEntries, publicEntries] |>.mapM fun entries => do
    let values ← entries.mapM fun entry => do
      let .arr #[.arr signature, _, _] := entry
        | throwError "boundary_realization_v2_member"
      let some name := signature[1]? | throwError "boundary_realization_v2_signature"
      pure name
    namesFromJson (.arr values)
  unless names[0]!.back? == some key && names[1]!.all names[0]!.contains do
    throwError "boundary_realization_v2_member_identity"
  return (names[0]!, names[1]!)

private partial def captureRealizationNode (fuel : Nat) (stock : Environment)
    (cached : Bool) (candidates : Array CachedGroup) (equations matchers : Array (Name × String))
    (group : CachedGroup) : StateT (Array RealizationNode) MetaM Nat := do
  if fuel == 0 then throwError "boundary_realization_v2_depth_unsupported"
  if let some index := (← get).findIdx? (fun node => node.owner == group.owner && node.key == group.key) then
    return index
  unless stock.isImportedConst group.owner && group.members.back? == some group.key do
    throwError "boundary_realization_v2_owner"
  let descriptor ← completedCacheDescriptor stock group.owner group.key (structural := true)
  let (kind, source, children) ← if isPrivateName group.key then do
      let state := Match.matchEqnsExt.getState stock (asyncMode := .async .asyncEnv) (asyncDecl := group.key)
      let some eqns := state.map.find? group.owner
        | throwError "boundary_realization_v2_child_not_matcher"
      unless eqns.splitterName == group.key && group.publicMembers.isEmpty do
        throwError "boundary_realization_v2_matcher_key"
      let source ← if cached then pure Json.null else do
        let some (_, source) := matchers.find? (·.1 == group.owner)
          | throwError "boundary_realization_missing_captured_matcher"
        unless (← boundaryMatcherDeclarationNames group.owner source) == group.members do
          throwError "boundary_realization_matcher_members_conflict"
        pure (.str (← nestedMatcherPayload source))
      pure ("matcher", source, #[])
    else do
      unless group.key.getPrefix == group.owner do throwError "boundary_realization_v2_equation_owner"
      let source ← if cached then do
          let some (.thmInfo thm) := stock.checked.get.find? group.key
            | throwError "boundary_realization_root_not_theorem"
          let mapping := (eqnsExt.getState stock).mapInv.find? group.key
          unless mapping.isNone || mapping == some group.owner do throwError "boundary_realization_root_mapping"
          encodeBoundaryEquation group.owner thm (defeqAttr.hasTag stock group.key)
            (backwardDefeqAttr.hasTag stock group.key) mapping.isSome
        else do
          let some (_, source) := equations.find? (·.1 == group.key)
            | throwError "boundary_realization_missing_captured_root"
          pure source
      let childNames := group.members.pop
      let childCandidates := candidates.filter fun child => child.members.size < group.members.size &&
        !child.members.isEmpty && child.members.all childNames.contains
      let covers := groupCovers childCandidates childNames
      unless covers.size == 1 do throwError "boundary_realization_ambiguous_nested_cover"
      let children ← covers[0]!.mapM fun child =>
        captureRealizationNode (fuel - 1) stock cached candidates equations matchers child
      pure ("equation", Json.str source, children)
  let nodes ← get
  let index := nodes.size
  set (nodes.push { kind, owner := group.owner, key := group.key, source, children, descriptor })
  return index

private def encodeBoundaryRealizationBatchV2? (before stock : Environment) (checkedBefore : NameSet)
    (equations matchers : Array (Name × String)) : MetaM (Option (Name × String)) := withEnv stock do
  let added ← branchDelta before stock
  if added.isEmpty then return none
  let publicAdded ← branchDelta before stock true
  let candidates ← candidateGroups stock
  let eligible := candidates.filter fun group => !group.members.isEmpty &&
    group.members.all added.contains && group.members.all (!before.containsOnBranch ·) &&
    !isPrivateName group.key && group.key.getPrefix == group.owner && stock.isImportedConst group.owner
  let covers := projectedCovers eligible added publicAdded
  unless covers.size == 1 do throwError "boundary_realization_ambiguous_or_missing_projected_cover"
  let groups := covers[0]!
  let cached := added.all checkedBefore.contains
  unless cached || added.all (!checkedBefore.contains ·) do
    throwError "boundary_realization_mixed_checked_closure"
  let (roots, nodes) ← (groups.mapM fun group =>
    captureRealizationNode 3 stock cached candidates equations matchers group).run #[]
  unless cached || ((nodes.filter (·.kind == "equation") |>.map (·.key)).qsort Name.quickLt ==
      (equations.map (·.1)).qsort Name.quickLt &&
      (nodes.filter (·.kind == "matcher") |>.map (·.owner)).qsort Name.quickLt ==
      (matchers.map (·.1)).qsort Name.quickLt) do
    throwError "boundary_realization_unclaimed_actions"
  let payload := Json.arr #[.str "boundary_realization_batch_v2", .bool cached,
    nameArrayJson added, nameArrayJson publicAdded,
    boundaryMatchStateJson (Match.matchEqnsExt.getState before),
    boundaryMatchStateJson (Match.matchEqnsExt.getState stock),
    equationStateJson (eqnsExt.getState before), equationStateJson (eqnsExt.getState stock),
    boundarySparseCacheJson before, boundarySparseCacheJson stock,
    .arr (nodes.map realizationNodeJson), toJson roots]
  return some (groups[0]!.key, payload.compress)


/- Local cached activation is deliberately separate from imported production.
   Pinned Environment.realizeValue returns a completed hit before reading its
   saved env/options. We authenticate that hit and never supply a producer.
   No saved-context claim is made for cache misses (which remain unsupported). -/
private def localConstantJson (info : ConstantInfo) : MetaM Json := do
  let common := #[encodeBoundaryName info.name, nameArrayJson info.levelParams.toArray,
    .str (← encodeBoundaryStructExpr info.type)]
  let names := fun ns : List Name => nameArrayJson ns.toArray
  let body := fun e => Json.str <$> encodeBoundaryStructExpr e
  match info with
  | .axiomInfo v => return .arr (#[.str "axiom"] ++ common ++ #[.bool v.isUnsafe])
  | .defnInfo v =>
    let hints := match v.hints with
      | .opaque => Json.arr #[.str "opaque"]
      | .abbrev => Json.arr #[.str "abbrev"]
      | .regular n => Json.arr #[.str "regular", toJson n.toNat]
    let safety := match v.safety with
      | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"
    return .arr (#[.str "definition"] ++ common ++ #[← body v.value, hints, .str safety, names v.all])
  | .thmInfo v => return .arr (#[.str "theorem"] ++ common ++ #[← body v.value, names v.all])
  | .opaqueInfo v => return .arr (#[.str "opaque"] ++ common ++ #[← body v.value, .bool v.isUnsafe, names v.all])
  | .quotInfo v =>
    let kind := match v.kind with
      | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
    return .arr (#[.str "quotient"] ++ common ++ #[.str kind])
  | .inductInfo v => return .arr (#[.str "inductive"] ++ common ++
      #[toJson v.numParams, toJson v.numIndices, names v.all, names v.ctors,
        toJson v.numNested, .bool v.isRec, .bool v.isUnsafe, .bool v.isReflexive])
  | .ctorInfo v => return .arr (#[.str "constructor"] ++ common ++
      #[encodeBoundaryName v.induct, toJson v.cidx, toJson v.numParams, toJson v.numFields, .bool v.isUnsafe])
  | .recInfo v =>
    let rules ← v.rules.toArray.mapM fun rule => do
      return Json.arr #[encodeBoundaryName rule.ctor, toJson rule.nfields, ← body rule.rhs]
    return .arr (#[.str "recursor"] ++ common ++
      #[names v.all, toJson v.numParams, toJson v.numIndices, toJson v.numMotives,
        toJson v.numMinors, .arr rules, .bool v.k, .bool v.isUnsafe])

private structure LocalDagState where
  nodes : Array Json := #[]
  -- Retaining objects makes the pointer memo safe from address reuse. Pointer
  -- identity is only an optimization: output deduplication uses exact JSON.
  memo : Array (AsyncConst × Nat) := #[]
  visiting : Array AsyncConst := #[]

private def sameAsyncObject (a b : AsyncConst) : Bool := unsafe ptrEq a b

private partial def localDagNode (env : Environment) (member : AsyncConst) :
    StateT LocalDagState MetaM Nat := do
  if let some (_, index) := (← get).memo.find? (fun (other, _) => sameAsyncObject member other) then
    return index
  let state ← get
  if state.visiting.size >= 512 || state.memo.size >= 4096 || state.nodes.size >= 2048 then
    throwError "boundary_local_cached_graph_limit"
  if state.visiting.any (sameAsyncObject member) then throwError "boundary_local_cached_graph_cycle"
  modify fun state => { state with visiting := state.visiting.push member }
  unless (← IO.hasFinished member.constInfo.constInfo) && (← IO.hasFinished member.constInfo.sig) &&
      (← IO.hasFinished member.aconstsImpl) do throwError "boundary_local_cached_pending_node"
  let info := member.constInfo.constInfo.get
  let sig := member.constInfo.sig.get
  unless member.constInfo.name == info.name && member.constInfo.kind == ConstantKind.ofConstantInfo info &&
      sig.name == info.name && sig.levelParams == info.levelParams && Expr.equal sig.type info.type do
    throwError "boundary_local_cached_async_signature"
  let signature ← localConstantJson info
  let metadata ← match member.exts? with
    | none => pure Json.null
    | some task => do
      unless ← IO.hasFinished task do throwError "boundary_local_cached_pending_extensions"
      memberMetadata env member
  let some children := member.aconstsImpl.get.get? AsyncConsts
    | throwError "boundary_local_cached_graph_type"
  let entries := children.revList.toArray.reverse
  unless entries.size == children.size && children.map.toArray.size == entries.size &&
      children.normalizedTrie.toArray.size == entries.size do
    throwError "boundary_local_cached_graph_cardinality"
  let mut seen : NameSet := {}
  let mut normalizedSeen : NameSet := {}
  let mut refs := #[]
  for child in entries do
    let name := child.constInfo.name
    let normalizedName := privateToUserName name
    if seen.contains name || normalizedSeen.contains normalizedName then
      throwError "boundary_local_cached_graph_duplicate"
    seen := seen.insert name
    normalizedSeen := normalizedSeen.insert normalizedName
    let childId ← localDagNode env child
    let some mapped := children.map.find? name | throwError "boundary_local_cached_graph_map"
    let some normalized := children.normalizedTrie.find? normalizedName
      | throwError "boundary_local_cached_graph_trie"
    unless (← localDagNode env mapped) == childId && (← localDagNode env normalized) == childId do
      throwError "boundary_local_cached_graph_lookup_conflict"
    refs := refs.push childId
  let node := Json.arr #[signature, .bool member.isRealized, metadata, toJson refs]
  let state ← get
  let index := (state.nodes.findIdx? (· == node)).getD state.nodes.size
  let nodes := if index == state.nodes.size then state.nodes.push node else state.nodes
  set ({ nodes, memo := state.memo.push (member, index), visiting := state.visiting.pop } : LocalDagState)
  return index

private def localOwnerWitness (env : Environment) (owner : Name) : MetaM Json := do
  unless !isPrivateName owner && !env.isImportedConst owner && env.containsOnBranch owner &&
      env.localRealizationCtxMap.contains owner do throwError "boundary_local_cached_owner_context"
  let some (.defnInfo info) := (← IO.wait env.checked).find? owner
    | throwError "boundary_local_cached_owner_kind"
  unless info.safety == .safe do throwError "boundary_local_cached_owner_safety"
  let some onBranch := env.find? owner (skipRealize := true)
    | throwError "boundary_local_cached_owner_branch"
  let witness ← localConstantJson (.defnInfo info)
  unless (← localConstantJson onBranch) == witness do throwError "boundary_local_cached_owner_checked"
  return witness

/-- Complete bounded descriptor of the authentic completed local cache task.
    Every ConstantInfo field (including proof bodies) and async nested lookup is
    represented. Persistent metadata retains the existing three diagnostic
    exclusions; this introduces no new extension or descriptor exemption. -/
private def localCachedDescriptor (env : Environment) (owner key : Name) : MetaM Json := do
  discard <| localOwnerWitness env owner
  let result ← completedCacheResult env owner key
  let [member] := result.newConsts.private | throwError "boundary_local_cached_group_shape"
  let [publicMember] := result.newConsts.public | throwError "boundary_local_cached_group_shape"
  unless member.constInfo.name == key && publicMember.constInfo.name == key do
    throwError "boundary_local_cached_group_shape"
  let info := member.constInfo.constInfo.get
  unless info.isTheorem do throwError "boundary_local_cached_root_kind"
  let some checked := (← IO.wait env.checked).find? key
    | throwError "boundary_local_cached_unchecked_root"
  unless (← localConstantJson checked) == (← localConstantJson info) do
    throwError "boundary_local_cached_checked_root"
  let .axiomInfo publicInfo := publicMember.constInfo.constInfo.get
    | throwError "boundary_local_cached_public_kind"
  unless !publicInfo.isUnsafe && publicInfo.name == info.name &&
      publicInfo.levelParams == info.levelParams && Expr.equal publicInfo.type info.type do
    throwError "boundary_local_cached_public_interface"
  let (roots, state) ← (do
    let privateRoot ← localDagNode env member
    let publicRoot ← localDagNode env publicMember
    pure (privateRoot, publicRoot)).run {}
  return .arr #[.str "completed_local_cached_v1", encodeBoundaryName owner,
    encodeBoundaryName key, .arr state.nodes, toJson roots.1, toJson roots.2]

private def encodeLocalCachedBatch? (before stock : Environment) (checkedBefore : NameSet)
    (equations matchers : Array (Name × String)) : MetaM (Option (Name × String)) := do
  let added ← branchDelta before stock
  let localGroups := (← candidateGroups stock).filter fun group =>
    !stock.isImportedConst group.owner && group.members == added
  if localGroups.isEmpty then return none
  unless localGroups.size == 1 && added.size == 1 && checkedBefore.contains added[0]! &&
      equations.isEmpty && matchers.isEmpty do throwError "boundary_local_cached_only"
  let group := localGroups[0]!
  unless group.key == added[0]! && !isPrivateName group.key && group.key.getPrefix == group.owner &&
      (← branchDelta before stock true) == added do throwError "boundary_local_cached_group_shape"
  let ownerWitness ← withEnv before <| localOwnerWitness before group.owner
  unless ownerWitness == (← withEnv stock <| localOwnerWitness stock group.owner) do
    throwError "boundary_local_cached_owner_changed"
  -- checkedBefore is the immutable pre-stock declaration domain. The cache
  -- reference is shared and mutable, so this is not historical proof of a
  -- pre-stock memo hit. Replay independently requires its own completed hit;
  -- standalone source replay remains necessary even after recorder trials.
  let descriptor ← withEnv before <| localCachedDescriptor before group.owner group.key
  unless descriptor == (← withEnv stock <| localCachedDescriptor stock group.owner group.key) do
    throwError "boundary_local_cached_descriptor_changed"
  let some (.thmInfo thm) := stock.checked.get.find? group.key
    | throwError "boundary_local_cached_root_kind"
  let mapping := (eqnsExt.getState stock).mapInv.find? group.key
  unless mapping.isNone || mapping == some group.owner do throwError "boundary_local_cached_root_mapping"
  let source ← withEnv stock <| encodeBoundaryEquation group.owner thm
    (defeqAttr.hasTag stock group.key) (backwardDefeqAttr.hasTag stock group.key) mapping.isSome
  return some (group.key, (Json.arr #[.str "boundary_local_cached_v1", .bool true,
    nameArrayJson added, nameArrayJson added,
    boundaryMatchStateJson (Match.matchEqnsExt.getState before),
    boundaryMatchStateJson (Match.matchEqnsExt.getState stock),
    equationStateJson (eqnsExt.getState before), equationStateJson (eqnsExt.getState stock),
    boundarySparseCacheJson before, boundarySparseCacheJson stock,
    .arr #[encodeBoundaryName group.owner, encodeBoundaryName group.key,
      ownerWitness, descriptor, .str source]]).compress)

private def executeLocalCachedBatch (anchor : Name) (source : String) : MetaM Unit := do
  let .arr #[.str "boundary_local_cached_v1", .bool true, privateNames, publicNames,
      matchBefore, matchAfter, eqnsBefore, eqnsAfter, sparseBefore, sparseAfter,
      .arr #[ownerJson, keyJson, witness, descriptor, .str equationSource]] ← ofExcept (Json.parse source)
    | throwError "boundary_local_cached_invalid_payload"
  let owner ← ofExcept (decodeBoundaryName ownerJson)
  let key ← ofExcept (decodeBoundaryName keyJson)
  let before ← getEnv
  unless key == anchor && !isPrivateName key && key.getPrefix == owner &&
      (← namesFromJson privateNames) == #[key] && (← namesFromJson publicNames) == #[key] &&
      !before.containsOnBranch key do throwError "boundary_local_cached_identity"
  let (equationOwner, theoremSource, defeqTag, backwardTag, registration) ←
    ofExcept (parseEquationPayload equationSource)
  unless equationOwner == owner do throwError "boundary_local_cached_equation_owner"
  validateEquationAnchor owner key
  unless boundaryMatchStateJson (Match.matchEqnsExt.getState before) == matchBefore &&
      equationStateJson (eqnsExt.getState before) == eqnsBefore && boundarySparseCacheJson before == sparseBefore do
    throwError "boundary_local_cached_before"
  unless (← localOwnerWitness before owner) == witness do throwError "boundary_local_cached_owner_conflict"
  unless (← localCachedDescriptor before owner key) == descriptor do
    throwError "boundary_local_cached_descriptor_conflict"
  realizeConst owner key (throwError "boundary_local_cached_forbidden_callback")
  unless (← localCachedDescriptor (← getEnv) owner key) == descriptor do
    throwError "boundary_local_cached_descriptor_after"
  executeBoundaryTheorem key theoremSource
  unless defeqAttr.hasTag (← getEnv) key == defeqTag && backwardDefeqAttr.hasTag (← getEnv) key == backwardTag do
    throwError "boundary_local_cached_tags"
  registerCapturedEquation owner key registration
  let after ← getEnv
  unless (← branchDelta before after) == #[key] && (← branchDelta before after true) == #[key] &&
      boundaryMatchStateJson (Match.matchEqnsExt.getState after) == matchAfter &&
      equationStateJson (eqnsExt.getState after) == eqnsAfter && boundarySparseCacheJson after == sparseAfter do
    throwError "boundary_local_cached_after"

def encodeBoundaryRealizationBatch? (before stock : Environment) (checkedBefore : NameSet)
    (equations matchers : Array (Name × String)) : MetaM (Option (Name × String)) := do
  let added ← branchDelta before stock
  if added.isEmpty then return none
  if let some localBatch ← encodeLocalCachedBatch? before stock checkedBefore equations matchers then
    return some localBatch
  let candidates ← candidateGroups stock
  let eligible := candidates.filter fun group => !group.members.isEmpty &&
    group.members.all added.contains && group.members.all (!before.containsOnBranch ·)
  -- Do not reinterpret a legacy cover or recover from arbitrary capture errors.
  if (groupCovers eligible added).isEmpty then
    encodeBoundaryRealizationBatchV2? before stock checkedBefore equations matchers
  else
    encodeBoundaryRealizationBatchV1? before stock checkedBefore equations matchers

private def parseRealizationNodes (cached : Bool) (values : Array Json) : MetaM (Array RealizationNode) := do
  let mut nodes : Array RealizationNode := #[]
  let mut depths : Array Nat := #[]
  for value in values do
    let .arr #[.str kind, owner, key, source, .arr children, descriptor] := value
      | throwError "boundary_realization_v2_node"
    let owner ← ofExcept (decodeBoundaryName owner)
    let key ← ofExcept (decodeBoundaryName key)
    unless (← getEnv).isImportedConst owner && !key.isAnonymous &&
        !(nodes.any fun node => node.owner == owner && node.key == key) do
      throwError "boundary_realization_v2_node_identity"
    let children ← children.mapM (Lean.ofExcept ∘ Json.getNat?)
    unless children.all (· < nodes.size) && children.toList.eraseDups.length == children.size do
      throwError "boundary_realization_v2_non_topological_children"
    let depth := children.foldl (fun depth i => max depth (depths[i]! + 1)) 0
    if depth > 2 then throwError "boundary_realization_v2_depth_unsupported"
    let (members, publicMembers) ← descriptorNames owner key descriptor
    if kind == "matcher" then
      unless isPrivateName key && children.isEmpty && publicMembers.isEmpty do
        throwError "boundary_realization_v2_matcher_node"
      if cached then
        unless source == .null do throwError "boundary_realization_v2_cached_producer"
      else
        let .str source := source | throwError "boundary_realization_v2_missing_matcher"
        unless (← ofExcept (parseMatcher source)).declarationOrder.isSome do
          throwError "boundary_realization_v2_unordered_matcher"
        unless (← boundaryMatcherDeclarationNames owner source) == members do
          throwError "boundary_realization_matcher_members_conflict"
    else if kind == "equation" then
      let .str source := source | throwError "boundary_realization_v2_missing_equation"
      let (equationOwner, _, _, _, _) ← ofExcept (parseEquationPayload source)
      unless equationOwner == owner && !isPrivateName key do throwError "boundary_realization_v2_equation_owner"
      validateEquationAnchor owner key
      let mut childMembers := #[]
      let mut childPublic := #[]
      for i in children do
        let child := nodes[i]!
        let (privateNames, publicNames) ← descriptorNames child.owner child.key child.descriptor
        childMembers := childMembers ++ privateNames
        childPublic := childPublic ++ publicNames
        if child.kind == "equation" then
          let .str source := child.source | throwError "boundary_realization_v2_missing_equation"
          let (_, _, _, _, registration) ← ofExcept (parseEquationPayload source)
          if registration then throwError "boundary_realization_v2_nested_registration_unsupported"
      unless childMembers.push key == members && childPublic.push key == publicMembers do
        throwError "boundary_realization_v2_nested_closure"
    else throwError "boundary_realization_v2_unknown_kind"
    nodes := nodes.push { kind, owner, key, source, children, descriptor }
    depths := depths.push depth
  return nodes

private partial def preflightNodeCaches (nodes : Array RealizationNode) (cached : Bool) (index : Nat) : MetaM Unit := do
  let node := nodes[index]!
  if cached then checkDescriptor node.owner node.key node.descriptor
  else discard <| completedCacheResult (← getEnv) node.owner node.key
  for child in node.children do preflightNodeCaches nodes cached child

private partial def executeRealizationNode (nodes : Array RealizationNode) (cached : Bool) (index : Nat) : MetaM Unit := do
  let node := nodes[index]!
  if (← getEnv).containsOnBranch node.key then throwError "boundary_realization_v2_root_already_active"
  let existing ← lookupCacheTask (← getEnv) node.owner node.key
  if cached || existing.isSome then preflightNodeCaches nodes cached index
  if node.kind == "matcher" then
    if cached || existing.isSome then
      realizeConst node.owner node.key (throwError "boundary_realization_forbidden_callback")
    else
      let .str source := node.source | throwError "boundary_realization_v2_missing_matcher"
      executeBoundaryMatcher node.owner source
    let state := Match.matchEqnsExt.getState (← getEnv)
      (asyncMode := .async .asyncEnv) (asyncDecl := node.key)
    let some eqns := state.map.find? node.owner
      | throwError "boundary_realization_v2_child_not_matcher"
    unless eqns.splitterName == node.key do throwError "boundary_realization_v2_matcher_key"
  else
    let .str source := node.source | throwError "boundary_realization_v2_missing_equation"
    let (_, theoremSource, defeqTag, backwardTag, registration) ← ofExcept (parseEquationPayload source)
    if cached || existing.isSome then
      realizeConst node.owner node.key (throwError "boundary_realization_forbidden_callback")
    else
      realizeConst node.owner node.key do
        unless boundaryMatchStateJson (Match.matchEqnsExt.getState (← getEnv)) == .arr #[.arr #[], .arr #[]] &&
            equationStateJson (eqnsExt.getState (← getEnv)) == .arr #[] &&
            boundarySparseCacheJson (← getEnv) == .arr #[] &&
            (auxLemmasExt.getState (← getEnv)).lemmas.isEmpty do
          throwError "boundary_realization_nonempty_producer_context"
        for child in node.children do executeRealizationNode nodes cached child
        realizeCapturedEquation node.key theoremSource defeqTag backwardTag
    executeBoundaryTheorem node.key theoremSource
    unless defeqAttr.hasTag (← getEnv) node.key == defeqTag &&
        backwardDefeqAttr.hasTag (← getEnv) node.key == backwardTag do
      throwError "boundary_realization_root_tags"
    registerCapturedEquation node.owner node.key registration
  -- Full descriptors are checked after the complete batch. Persistent export
  -- functions also inspect the checked declaration domain (e.g. symbolFrequency),
  -- so an intermediate imported callback is not the captured final domain.

private def executeBoundaryRealizationBatchV2 (expectedAnchor : Name) (source : String) : MetaM Unit := do
  let .arr #[.str "boundary_realization_batch_v2", .bool cached, privateNames, publicNames,
      matchBefore, matchAfter, eqnsBefore, eqnsAfter, sparseBefore, sparseAfter, .arr values, .arr roots] ← ofExcept (Json.parse source)
    | throwError "boundary_realization_invalid_payload"
  let added ← namesFromJson privateNames
  let publicAdded ← namesFromJson publicNames
  let nodes ← parseRealizationNodes cached values
  let roots ← roots.mapM (Lean.ofExcept ∘ Json.getNat?)
  unless !roots.isEmpty && roots.all (· < nodes.size) &&
      roots.toList.eraseDups.length == roots.size do throwError "boundary_realization_v2_roots"
  unless nodes[roots[0]!]!.key == expectedAnchor do throwError "boundary_realization_foreign_anchor"
  let mut reachable := roots
  for i in (List.range nodes.size).reverse do
    if reachable.contains i then
      for child in nodes[i]!.children do
        if !reachable.contains child then reachable := reachable.push child
  unless reachable.size == nodes.size do throwError "boundary_realization_v2_unused_node"
  let before ← getEnv
  unless added.all (!before.containsOnBranch ·) do throwError "boundary_realization_members_already_active"
  unless boundaryMatchStateJson (Match.matchEqnsExt.getState before) == matchBefore &&
      equationStateJson (eqnsExt.getState before) == eqnsBefore && boundarySparseCacheJson before == sparseBefore do
    throwError "boundary_realization_caller_before_conflict"
  let mut seenPrivate := #[]
  let mut seenPublic := #[]
  for root in roots do
    let node := nodes[root]!
    unless node.kind == "equation" do throwError "boundary_realization_v2_private_root"
    let (members, publicMembers) ← descriptorNames node.owner node.key node.descriptor
    seenPrivate := seenPrivate ++ members.filter (!seenPrivate.contains ·)
    seenPublic := seenPublic ++ publicMembers.filter (!seenPublic.contains ·)
    executeRealizationNode nodes cached root
    unless (← branchDelta before (← getEnv)) == seenPrivate &&
        (← branchDelta before (← getEnv) true) == seenPublic do
      throwError "boundary_realization_branch_transition_conflict"
  unless seenPrivate == added && seenPublic == publicAdded do throwError "boundary_realization_v2_projected_order"
  for node in nodes do checkDescriptor node.owner node.key node.descriptor
  let after ← getEnv
  unless boundaryMatchStateJson (Match.matchEqnsExt.getState after) == matchAfter &&
      equationStateJson (eqnsExt.getState after) == eqnsAfter && boundarySparseCacheJson after == sparseAfter do
    throwError "boundary_realization_caller_after_conflict"

def executeBoundaryRealizationBatch (expectedAnchor : Name) (source : String) : MetaM Unit := do
  let json ← ofExcept (Json.parse source)
  match json with
  | .arr values =>
    if values[0]? == some (.str "boundary_local_cached_v1") then
      executeLocalCachedBatch expectedAnchor source
    else if values[0]? == some (.str "boundary_realization_batch_v2") then
      executeBoundaryRealizationBatchV2 expectedAnchor source
    else executeBoundaryRealizationBatchV1 expectedAnchor source
  | _ => throwError "boundary_realization_invalid_payload"

/-- Every listed member remains independently required by Boundary's checker.
    Cached activations add no checked declarations. -/
def boundaryRealizationBatchMembers (source : String) : MetaM (Bool × Array Name × Array Name) := do
  let (cached, privateNames, publicNames) ← match ← ofExcept (Json.parse source) with
    | .arr #[.str "boundary_local_cached_v1", .bool true, privateNames, publicNames,
        _, _, _, _, _, _, _] => pure (true, privateNames, publicNames)
    | .arr #[.str "boundary_realization_batch_v1", .bool cached, privateNames, publicNames,
        _, _, _, _, _, _, _] => pure (cached, privateNames, publicNames)
    | .arr #[.str "boundary_realization_batch_v2", .bool cached, privateNames, publicNames,
        _, _, _, _, _, _, _, _] => pure (cached, privateNames, publicNames)
    | _ => throwError "boundary_realization_invalid_payload"
  return (cached, ← namesFromJson privateNames, ← namesFromJson publicNames)

end ExplicitLean.SimpEngine.Boundary
