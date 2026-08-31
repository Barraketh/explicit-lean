module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.DeclarationCodec
public meta import ExplicitLean.SimpEngine.Boundary.SparseCasesCodec
public meta import Lean.Meta.Match.MatchEqsExt
public meta import Lean.Meta.Eqns
public meta import Lean.Compiler.InlineAttrs
public meta import Lean.Compiler.Main

public meta section

open Lean Meta
open Lean.Meta.Match

namespace ExplicitLean.SimpEngine.Boundary

/- Capture supplies checked declarations and typed metadata;
   execution never invokes match/equation generation or simplification. -/

private def optionNatJson : Option Nat → Json
  | none => .null
  | some n => toJson n

private def optionNameJson : Option Name → Json
  | none => .null
  | some n => encodeBoundaryName n

private def decodeOptionNat (json : Json) : Except String (Option Nat) :=
  if json == .null then pure none else some <$> json.getNat?

private def decodeOptionName (json : Json) : Except String (Option Name) :=
  if json == .null then pure none else some <$> decodeBoundaryName json

def boundaryMatcherInfoJson (info : MatcherInfo) : Json :=
  .arr #[toJson info.numParams, toJson info.numDiscrs,
    .arr (info.altInfos.map fun a => .arr #[toJson a.numFields, toJson a.numOverlaps,
      .bool a.hasUnitThunk]), optionNatJson info.uElimPos?,
    .arr (info.discrInfos.map fun d => optionNameJson d.hName?),
    .arr ((info.overlaps.map.toArray.qsort (fun a b => a.1 < b.1)).map fun (key, values) =>
      .arr #[toJson key, toJson values.toArray])]

private def decodeMatcherInfo (json : Json) : Except String MatcherInfo := do
  let .arr #[params, discrs, .arr alts, uPos, .arr discrInfos, .arr overlaps] := json
    | throw "invalid matcher info"
  let numParams ← params.getNat?
  let numDiscrs ← discrs.getNat?
  let altInfos ← alts.mapM fun json => do
    let .arr #[fields, overlaps, .bool thunk] := json | throw "invalid alternative info"
    pure ({
      numFields := ← fields.getNat?, numOverlaps := ← overlaps.getNat?,
      hasUnitThunk := thunk } : AltParamInfo)
  let discrInfos ← discrInfos.mapM fun json => do
    pure ({ hName? := ← decodeOptionName json } : DiscrInfo)
  unless discrInfos.size == numDiscrs do throw "discriminant count mismatch"
  let mut map : Std.HashMap Nat (Std.TreeSet Nat) := {}
  for json in overlaps do
    let .arr #[keyJson, .arr values] := json | throw "invalid overlap entry"
    let key ← keyJson.getNat?
    unless key < altInfos.size do throw "overlap key out of range"
    if map.contains key then throw "duplicate overlap key"
    let mut set : Std.TreeSet Nat := {}
    for json in values do
      let value ← json.getNat?
      unless value < altInfos.size do throw "overlap value out of range"
      if set.contains value then throw "duplicate overlap value"
      set := set.insert value
    map := map.insert key set
  pure {
    numParams, numDiscrs, altInfos, uElimPos? := ← decodeOptionNat uPos,
    discrInfos, overlaps := { map } }

def boundaryMatchEqnsJson (eqns : MatchEqns) : Json :=
  .arr #[.arr (eqns.eqnNames.map encodeBoundaryName), encodeBoundaryName eqns.splitterName,
    boundaryMatcherInfoJson eqns.splitterMatchInfo]

private def decodeNames (json : Json) : Except String (Array Name) := do
  let values ← json.getArr?
  let mut names := #[]
  for value in values do
    let name ← decodeBoundaryName value
    if name.isAnonymous || names.contains name then throw "anonymous or duplicate name"
    names := names.push name
  pure names

private def decodeMatchEqns (json : Json) : Except String MatchEqns := do
  let .arr #[names, splitter, info] := json | throw "invalid match equations"
  let eqnNames ← decodeNames names
  let splitterName ← decodeBoundaryName splitter
  let splitterMatchInfo ← decodeMatcherInfo info
  if splitterName.isAnonymous || eqnNames.contains splitterName then throw "invalid splitter name"
  unless eqnNames.size == splitterMatchInfo.altInfos.size do throw "equation count mismatch"
  pure { eqnNames, splitterName, splitterMatchInfo }

def boundaryMatchStateJson (state : MatchEqnsExtState) : Json :=
  .arr #[.arr ((state.map.toArray.qsort (fun a b => Name.quickLt a.1 b.1)).map
      fun (key, eqns) => .arr #[encodeBoundaryName key, boundaryMatchEqnsJson eqns]),
    .arr ((state.eqns.toList.toArray.qsort Name.quickLt).map encodeBoundaryName)]

private def decodeMatchState (json : Json) : Except String MatchEqnsExtState := do
  let .arr #[.arr entries, names] := json | throw "invalid match state"
  let mut state : MatchEqnsExtState := {}
  for entry in entries do
    let .arr #[keyJson, valueJson] := entry | throw "invalid match state entry"
    let key ← decodeBoundaryName keyJson
    if key.isAnonymous || state.map.contains key then throw "invalid match state key"
    state := { state with map := state.map.insert key (← decodeMatchEqns valueJson) }
  for name in ← decodeNames names do
    state := { state with eqns := state.eqns.insert name }
  pure state

private def equationStateJson (state : EqnsExtState) : Json :=
  .arr ((state.mapInv.toArray.qsort (fun a b => Name.quickLt a.1 b.1)).map
    fun (key, value) => .arr #[encodeBoundaryName key, encodeBoundaryName value])

private def inlineJson : Option Compiler.InlineAttributeKind → Json
  | none => .null
  | some .inline => .str "inline"
  | some .noinline => .str "noinline"
  | some .macroInline => .str "macroInline"
  | some .inlineIfReduce => .str "inlineIfReduce"
  | some .alwaysInline => .str "alwaysInline"

private def decodeInline : Json → Except String (Option Compiler.InlineAttributeKind)
  | .null => pure none
  | .str "inline" => pure (some .inline)
  | .str "noinline" => pure (some .noinline)
  | .str "macroInline" => pure (some .macroInline)
  | .str "inlineIfReduce" => pure (some .inlineIfReduce)
  | .str "alwaysInline" => pure (some .alwaysInline)
  | _ => throw "invalid inline attribute"

private structure CapturedEquation where
  name : Name
  source : String
  defeqTag : Bool
  backwardTag : Bool
  asyncRegistration : Option Name
  localRegistration : Option Name

private structure CapturedMatcher where
  anchor : Name
  anchorInfo : MatcherInfo
  eqns : MatchEqns
  splitterSource : String
  splitterInline : Option Compiler.InlineAttributeKind
  splitterInfo : Option MatcherInfo
  equations : Array CapturedEquation
  snapshotBefore : MatchEqnsExtState
  snapshotAfter : MatchEqnsExtState
  localState : MatchEqnsExtState
  asyncEquationBefore : Json
  asyncEquationAfter : Json
  localEquationBefore : Json
  localEquationAfter : Json
  sparseHelpers : Array (Name × String)
  asyncSparseBefore : Json
  asyncSparseAfter : Json
  localSparseState : Json

private def matcherJson (bundle : CapturedMatcher) : Json :=
  .arr #[.str "boundary_matcher_bundle_v2", encodeBoundaryName bundle.anchor,
    boundaryMatcherInfoJson bundle.anchorInfo, boundaryMatchEqnsJson bundle.eqns,
    .str bundle.splitterSource, inlineJson bundle.splitterInline,
    (bundle.splitterInfo.map boundaryMatcherInfoJson).getD .null,
    .arr (bundle.equations.map fun eqn => .arr #[encodeBoundaryName eqn.name,
      .str eqn.source, .bool eqn.defeqTag, .bool eqn.backwardTag,
      optionNameJson eqn.asyncRegistration, optionNameJson eqn.localRegistration]),
    boundaryMatchStateJson bundle.snapshotBefore, boundaryMatchStateJson bundle.snapshotAfter,
    boundaryMatchStateJson bundle.localState, bundle.asyncEquationBefore,
    bundle.asyncEquationAfter, bundle.localEquationBefore, bundle.localEquationAfter,
    .arr (bundle.sparseHelpers.map fun (name, source) => .arr #[encodeBoundaryName name, .str source]),
    bundle.asyncSparseBefore, bundle.asyncSparseAfter, bundle.localSparseState]

private def parseMatcher (source : String) : Except String CapturedMatcher := do
  let json ← Json.parse source
  let .arr #[.str "boundary_matcher_bundle_v2", anchor, anchorInfo, eqns,
      .str splitterSource, inlineAttr, splitterInfo, .arr equations,
      snapshotBefore, snapshotAfter, localState, asyncEquationBefore, asyncEquationAfter,
      localEquationBefore, localEquationAfter, .arr sparseHelpers,
      asyncSparseBefore, asyncSparseAfter, localSparseState] := json | throw "invalid matcher bundle"
  let sparseHelpers ← sparseHelpers.mapM fun json => do
    let .arr #[name, .str source] := json | throw "invalid sparse helper"
    pure (← decodeBoundaryName name, source)
  let equations ← equations.mapM fun json => do
    let .arr #[name, .str source, .bool defeqTag, .bool backwardTag, asyncReg, localReg] := json
      | throw "invalid captured equation"
    pure {
      name := ← decodeBoundaryName name, source, defeqTag, backwardTag,
      asyncRegistration := ← decodeOptionName asyncReg,
      localRegistration := ← decodeOptionName localReg : CapturedEquation }
  pure {
    anchor := ← decodeBoundaryName anchor, anchorInfo := ← decodeMatcherInfo anchorInfo,
    eqns := ← decodeMatchEqns eqns, splitterSource,
    splitterInline := ← decodeInline inlineAttr,
    splitterInfo := ← if splitterInfo == .null then pure none
      else some <$> decodeMatcherInfo splitterInfo,
    equations, snapshotBefore := ← decodeMatchState snapshotBefore,
    snapshotAfter := ← decodeMatchState snapshotAfter, localState := ← decodeMatchState localState,
    asyncEquationBefore, asyncEquationAfter, localEquationBefore, localEquationAfter,
    sparseHelpers, asyncSparseBefore, asyncSparseAfter, localSparseState }

private def matcherStateAt (env : Environment) (name : Name) : MatchEqnsExtState :=
  matchEqnsExt.getState env (asyncMode := .async .asyncEnv) (asyncDecl := name)

private def equationStateAt (env : Environment) (name : Name) : EqnsExtState :=
  eqnsExt.getState env (asyncMode := .async .asyncEnv) (asyncDecl := name)

private def checkState (label : String) (actual expected : MatchEqnsExtState) : MetaM Unit :=
  unless boundaryMatchStateJson actual == boundaryMatchStateJson expected do
    throwError "boundary_matcher_state_conflict:{label}"

private def checkEquationState (label : String) (actual : EqnsExtState) (expected : Json) : MetaM Unit :=
  unless equationStateJson actual == expected do
    throwError "boundary_matcher_equation_state_conflict:{label}"

private def checkSparseState (label : String) (actual expected : Json) : MetaM Unit := do
  unless actual == expected do throwError "boundary_matcher_sparse_cache_conflict:{label}"

private def insertCapturedEquation (name : Name) (registration : Option Name) : MetaM Unit := do
  match (eqnsExt.getState (← getEnv)).mapInv.find? name with
  | some actual =>
      unless registration == some actual do throwError "boundary_matcher_equation_registration_conflict"
  | none =>
      if let some anchor := registration then
        modifyEnv fun env => eqnsExt.modifyState env fun state =>
          { state with mapInv := state.mapInv.insert name anchor }

private def validateBundle (bundle : CapturedMatcher) : MetaM Unit := do
  let env ← getEnv
  unless env.containsOnBranch bundle.anchor do throwError "boundary_matcher_unknown_anchor"
  let some actualInfo := Match.Extension.getMatcherInfo? env bundle.anchor
    | throwError "boundary_matcher_anchor_not_matcher"
  unless boundaryMatcherInfoJson actualInfo == boundaryMatcherInfoJson bundle.anchorInfo do
    throwError "boundary_matcher_anchor_metadata_conflict"
  let some anchorDecl := env.find? bundle.anchor (skipRealize := true)
    | throwError "boundary_matcher_unknown_anchor"
  if let some pos := bundle.eqns.splitterMatchInfo.uElimPos? then
    unless pos < anchorDecl.levelParams.length do throwError "boundary_matcher_universe_position"
  unless bundle.eqns.eqnNames == bundle.equations.map (·.name) do
    throwError "boundary_matcher_equation_order"
  unless bundle.eqns.eqnNames.size == bundle.anchorInfo.altInfos.size do
    throwError "boundary_matcher_alternative_count"
  -- Pinned Match.mkMatcherAuxDefinition suppresses persistent MatcherInfo for
  -- isSplitter=true; the alias splitter branch does not register it either.
  unless bundle.splitterInfo.isNone do
    throwError "boundary_matcher_unexpected_splitter_info"
  -- Pinned matcher generation may deliberately omit executable code when
  -- bootstrap.genMatcherCode is false. This bounded prototype must not create
  -- executable code absent from that stock result.
  unless bundle.splitterInline == some .inline do
    throwError "boundary_matcher_uncompiled_splitter_unsupported"
  unless bundle.eqns.eqnNames.size > 0 &&
      bundle.eqns.eqnNames.all isPrivateName && isPrivateName bundle.eqns.splitterName do
    throwError "boundary_matcher_expected_private_bundle"
  -- Naming is an additional pinned-format check, not the capture provenance
  -- test: capture also requires the actual typed entry in the async snapshot.
  let baseName := mkPrivateName env bundle.anchor
  unless bundle.eqns.splitterName == baseName ++ `splitter &&
      bundle.eqns.eqnNames == (List.range bundle.eqns.eqnNames.size).toArray.map
        (fun i => Name.str baseName s!"eq_{i + 1}") do
    throwError "boundary_matcher_member_identity"
  let metadataWithoutAlts := { bundle.eqns.splitterMatchInfo with
    altInfos := bundle.anchorInfo.altInfos }
  unless boundaryMatcherInfoJson metadataWithoutAlts == boundaryMatcherInfoJson bundle.anchorInfo do
    throwError "boundary_matcher_unrelated_splitter_metadata"
  let mut sparseNames : NameSet := {}
  for (name, source) in bundle.sparseHelpers do
    unless (← boundarySparseCasesName source) == name &&
        bundle.eqns.splitterName.isPrefixOf name && name != bundle.eqns.splitterName &&
        !bundle.eqns.eqnNames.contains name && !sparseNames.contains name do
      throwError "boundary_matcher_sparse_helper_identity"
    sparseNames := sparseNames.insert name
  for eqn in bundle.equations do
    let theoremJson ← match Json.parse eqn.source with
      | .ok json => pure json
      | .error error => throwError "boundary_matcher_theorem_metadata:{error}"
    let .arr #[.str "boundary_theorem_dag_v1", name, all, _, _, _] := theoremJson
      | throwError "boundary_matcher_theorem_metadata"
    -- getEquationsForImpl creates independent theorems with the default
    -- singleton declaration group. Kernel checking alone does not enforce it.
    unless name == encodeBoundaryName eqn.name && all == .arr #[name] do
      throwError "boundary_matcher_theorem_group"
    unless eqn.asyncRegistration.all (· == bundle.anchor) &&
        eqn.localRegistration.all (· == bundle.anchor) do
      throwError "boundary_matcher_foreign_equation_registration"
  unless !(bundle.snapshotBefore.map.contains bundle.anchor) &&
      bundle.eqns.eqnNames.all (!bundle.snapshotBefore.eqns.contains ·) do
    throwError "boundary_matcher_nonfresh_snapshot"
  let expected : MatchEqnsExtState := {
    map := bundle.snapshotBefore.map.insert bundle.anchor bundle.eqns
    eqns := bundle.eqns.eqnNames.foldl (init := bundle.snapshotBefore.eqns) (·.insert ·) }
  checkState "payload-transition" expected bundle.snapshotAfter

private def checkCapturedMatcherConstants (before : Environment) (available : NameSet)
    (value : Expr) : MetaM Unit := do
  if let some bad := value.find? fun expression => match expression with
      | .const name _ | .proj name _ _ =>
          !before.containsOnBranch name && !available.contains name
      | _ => false then
    throwError "boundary_matcher_foreign_declaration_dependency:{bad}"

/-- Capture one exact generated bundle. The caller must separately capture all
    explicitly named other declarations, including disjoint matcher bundles.
    Bundle bodies cannot depend on those declarations, so global action ordering
    requires no hidden resolution. -/
def encodeBoundaryMatcher (before : Environment) (checkedBefore : NameSet) (anchor : Name)
    (eqns : MatchEqns) (otherDeclarations : Array Name := #[])
    (priorEquationDeclarations : Array Name := #[])
    (sparseDeclarations : Array Name := #[]) : MetaM String := do
  let stock ← getEnv
  let members := sparseDeclarations ++ eqns.eqnNames.push eqns.splitterName
  unless members.all (!before.containsOnBranch ·) do throwError "boundary_matcher_not_fresh"
  let delta := stock.constants.foldStage2 (s := #[]) fun names name _ =>
    if checkedBefore.contains name then names else names.push name
  unless delta.qsort Name.quickLt == (members ++ otherDeclarations).qsort Name.quickLt do
    throwError "boundary_matcher_unsupported_declaration_closure:{delta}"
  let snapshotAfter := matcherStateAt stock eqns.splitterName
  let some captured := snapshotAfter.map.find? anchor
    | throwError "boundary_matcher_missing_provenance"
  unless boundaryMatchEqnsJson captured == boundaryMatchEqnsJson eqns do
    throwError "boundary_matcher_foreign_provenance"
  let snapshotBefore : MatchEqnsExtState := {
    map := snapshotAfter.map.erase anchor,
    eqns := eqns.eqnNames.foldl (init := snapshotAfter.eqns) (·.erase ·) }
  let localState := matchEqnsExt.getState before
  checkState "capture-local" (matchEqnsExt.getState stock) localState
  let asyncEquationAfter := equationStateAt stock eqns.splitterName
  let asyncEquationBefore : EqnsExtState := {
    mapInv := eqns.eqnNames.foldl (init := asyncEquationAfter.mapInv) (·.erase ·) }
  let stockLocalEquations := eqnsExt.getState stock
  let addRegistration := fun (state : EqnsExtState) (name : Name) =>
    match stockLocalEquations.mapInv.find? name with
    | none => state
    | some anchor => { state with mapInv := state.mapInv.insert name anchor }
  let localBefore := eqnsExt.getState before
  -- Other supported equation actions and earlier bundles' equations may precede
  -- this bundle. Capture its exact invocation state, not a projected map.
  unless priorEquationDeclarations.all otherDeclarations.contains do
    throwError "boundary_matcher_foreign_prior_equation"
  let localEquationBefore := priorEquationDeclarations.foldl addRegistration localBefore
  let localEquationAfter := eqns.eqnNames.foldl addRegistration localEquationBefore
  let finalEquationState := (members ++ otherDeclarations).foldl addRegistration localBefore
  checkEquationState "capture-complete-local" stockLocalEquations
    (equationStateJson finalEquationState)
  let localSparseState := boundarySparseCacheJson before
  checkSparseState "capture-local" (boundarySparseCacheJson stock) localSparseState
  let asyncSparseAfter := boundarySparseCacheJson stock (some eqns.splitterName)
  let mut sparseHelpers := #[]
  let mut available : NameSet := {}
  for name in sparseDeclarations do
    let some (.defnInfo helper) := stock.find? name (skipRealize := true)
      | throwError "boundary_matcher_sparse_helper_expected_definition"
    checkCapturedMatcherConstants before available helper.type
    checkCapturedMatcherConstants before available helper.value
    checkSparseState "capture-sparse-member" (boundarySparseCacheJson stock (some name)) asyncSparseAfter
    let source ← encodeBoundarySparseCases before name eqns.splitterName
    sparseHelpers := sparseHelpers.push (name, source)
    available := available.insert name
  let asyncSparseBefore ← boundarySparseCacheWithout stock eqns.splitterName (sparseHelpers.map (·.2))
  let mut equations := #[]
  for name in eqns.eqnNames do
    checkSparseState "capture-equation-member" (boundarySparseCacheJson stock (some name)) asyncSparseAfter
    checkState "capture-member" (matcherStateAt stock name) snapshotAfter
    checkEquationState "capture-member" (equationStateAt stock name)
      (equationStateJson asyncEquationAfter)
    let some (.thmInfo thm) := stock.find? name (skipRealize := true)
      | throwError "boundary_matcher_expected_theorem"
    checkCapturedMatcherConstants before available thm.type
    checkCapturedMatcherConstants before available thm.value
    equations := equations.push {
      name, source := ← encodeBoundaryTheorem thm,
      defeqTag := defeqAttr.hasTag stock name, backwardTag := backwardDefeqAttr.hasTag stock name,
      asyncRegistration := asyncEquationAfter.mapInv.find? name,
      localRegistration := (eqnsExt.getState stock).mapInv.find? name }
    available := available.insert name
  let some (.defnInfo splitter) := stock.find? eqns.splitterName (skipRealize := true)
    | throwError "boundary_matcher_expected_definition"
  checkCapturedMatcherConstants before available splitter.type
  checkCapturedMatcherConstants before available splitter.value
  let some anchorInfo := Match.Extension.getMatcherInfo? before anchor
    | throwError "boundary_matcher_unknown_capture_anchor"
  let bundle : CapturedMatcher := {
    anchor, anchorInfo, eqns, splitterSource := ← encodeBoundaryDefinition splitter,
    splitterInline := Compiler.getInlineAttribute? stock eqns.splitterName,
    splitterInfo := (Match.Extension.extension.getState stock
      (asyncDecl := eqns.splitterName)).map.find? eqns.splitterName,
    equations, snapshotBefore, snapshotAfter, localState,
    asyncEquationBefore := equationStateJson asyncEquationBefore,
    asyncEquationAfter := equationStateJson asyncEquationAfter,
    localEquationBefore := equationStateJson localEquationBefore,
    localEquationAfter := equationStateJson localEquationAfter,
    sparseHelpers, asyncSparseBefore, asyncSparseAfter, localSparseState }
  validateBundle bundle
  return (matcherJson bundle).compress

/-- The action identifies its existing anchor; these are its added declarations.
    Validation deliberately does not classify that anchor as a new declaration. -/
def boundaryMatcherDeclarationNames (anchor : Name) (source : String) : MetaM (Array Name) := do
  let bundle ← match parseMatcher source with
    | .ok result => pure result
    | .error error => throwError "boundary_matcher_decode_error:{error}"
  unless bundle.anchor == anchor do throwError "boundary_matcher_foreign_anchor"
  validateBundle bundle
  return bundle.sparseHelpers.map (·.1) ++ bundle.eqns.eqnNames.push bundle.eqns.splitterName

private def realizeCapturedMatcher (bundle : CapturedMatcher) : MetaM Unit := do
  checkState "realization-before" (matchEqnsExt.getState (← getEnv)) bundle.snapshotBefore
  checkEquationState "realization-before" (eqnsExt.getState (← getEnv)) bundle.asyncEquationBefore
  checkSparseState "realization-before" (boundarySparseCacheJson (← getEnv)) bundle.asyncSparseBefore
  for (name, source) in bundle.sparseHelpers do
    executeBoundarySparseCases name source
  checkSparseState "realization-after-helpers" (boundarySparseCacheJson (← getEnv)) bundle.asyncSparseAfter
  -- Captured helpers precede equation proofs; each decoder preflights constants.
  for eqn in bundle.equations do
    executeBoundaryTheorem eqn.name eqn.source
    if eqn.defeqTag then defeqAttr.setTag eqn.name
    if eqn.backwardTag then backwardDefeqAttr.setTag eqn.name
    insertCapturedEquation eqn.name eqn.asyncRegistration
  executeBoundaryDefinition bundle.eqns.splitterName bundle.splitterSource
  if let some kind := bundle.splitterInline then
    match Compiler.setInlineAttribute (← getEnv) bundle.eqns.splitterName kind with
    | .ok env => setEnv env
    | .error error => throwError "boundary_matcher_inline_error:{error}"
  let some (.defnInfo splitter) := (← getEnv).find? bundle.eqns.splitterName (skipRealize := true)
    | throwError "boundary_matcher_missing_definition"
  compileDecl (logErrors := false) (.defnDecl splitter)
  registerMatchEqns bundle.anchor bundle.eqns
  checkState "realization-after" (matchEqnsExt.getState (← getEnv)) bundle.snapshotAfter
  checkEquationState "realization-after" (eqnsExt.getState (← getEnv)) bundle.asyncEquationAfter
  checkSparseState "realization-after" (boundarySparseCacheJson (← getEnv)) bundle.asyncSparseAfter

def executeBoundaryMatcher (expectedAnchor : Name) (source : String) : MetaM Unit := do
  let bundle ← match parseMatcher source with
    | .ok result => pure result
    | .error error => throwError "boundary_matcher_decode_error:{error}"
  unless bundle.anchor == expectedAnchor do throwError "boundary_matcher_foreign_anchor"
  validateBundle bundle
  checkState "caller-before" (matchEqnsExt.getState (← getEnv)) bundle.localState
  checkEquationState "caller-before" (eqnsExt.getState (← getEnv)) bundle.localEquationBefore
  checkSparseState "caller-before" (boundarySparseCacheJson (← getEnv)) bundle.localSparseState
  realizeConst bundle.anchor bundle.eqns.splitterName (realizeCapturedMatcher bundle)
  for (name, source) in bundle.sparseHelpers do
    checkBoundarySparseCases name source
  -- Cached realizations skip the closure, so independently revalidate every
  -- declaration and its exact attached metadata before changing caller state.
  for eqn in bundle.equations do
    executeBoundaryTheorem eqn.name eqn.source
    let env ← getEnv
    unless defeqAttr.hasTag env eqn.name == eqn.defeqTag &&
        backwardDefeqAttr.hasTag env eqn.name == eqn.backwardTag do
      throwError "boundary_matcher_equation_tag_conflict"
  executeBoundaryDefinition bundle.eqns.splitterName bundle.splitterSource
  let env ← getEnv
  unless Compiler.getInlineAttribute? env bundle.eqns.splitterName == bundle.splitterInline do
    throwError "boundary_matcher_inline_conflict"
  let actualInfo := (Match.Extension.extension.getState env
    (asyncDecl := bundle.eqns.splitterName)).map.find? bundle.eqns.splitterName
  unless actualInfo.map boundaryMatcherInfoJson == bundle.splitterInfo.map boundaryMatcherInfoJson do
    throwError "boundary_matcher_splitter_metadata_conflict"
  for name in bundle.sparseHelpers.map (·.1) ++ bundle.eqns.eqnNames.push bundle.eqns.splitterName do
    checkSparseState "realized-member" (boundarySparseCacheJson env (some name)) bundle.asyncSparseAfter
    unless env.containsOnBranch name do throwError "boundary_matcher_missing_member"
    checkState "realized-member" (matcherStateAt env name) bundle.snapshotAfter
    checkEquationState "realized-member" (equationStateAt env name) bundle.asyncEquationAfter
  for eqn in bundle.equations do
    insertCapturedEquation eqn.name eqn.localRegistration
  checkSparseState "caller-after" (boundarySparseCacheJson (← getEnv)) bundle.localSparseState
  checkState "caller-after" (matchEqnsExt.getState (← getEnv)) bundle.localState
  checkEquationState "caller-after" (eqnsExt.getState (← getEnv)) bundle.localEquationAfter

end ExplicitLean.SimpEngine.Boundary
