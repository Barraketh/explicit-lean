/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
SPDX-License-Identifier: Apache-2.0
License: https://www.apache.org/licenses/LICENSE-2.0
Authors of upstream code: Leonardo de Moura, Kim Morrison

Adapted from the pinned Lean 4.32.2 library-suggestion and Environment export
computations. The adaptations retain their data policy while avoiding the
process-global suggestion caches in the substituted export callbacks.
-/
module
prelude

public meta import Lean.Meta.Basic
meta import all Lean.Meta.FunInfo
public meta import ExplicitLean.SimpEngine.Boundary.NoSynthesis
meta import all Lean.Environment
meta import all Lean.DocString.Extension
meta import all Lean.OriginalConstKind
meta import all Lean.Linter.Deprecated

public meta section
open Lean Meta
namespace ExplicitLean.SimpEngine.Boundary

private unsafe def runExportMeta (env : Environment) (action : MetaM α) : IO α :=
  ((withoutBoundaryPendingSynthesis (withoutExporting action)).run' {} {}).toIO'
    { fileName := "symbolFrequency", fileMap := default, maxHeartbeats := 0 } { env }

/- The following is the pinned foldRelevantConstants implementation. It is
   kept local because importing its public wrapper also imports Grind. -/
private unsafe structure BoundaryFoldState where
  visited       : PtrSet Expr := mkPtrSet
  visitedConsts : NameHashSet := {}

private unsafe abbrev BoundaryFoldM := StateT BoundaryFoldState MetaM

private unsafe def boundaryFold {α : Type} (f : Name → α → MetaM α) (e : Expr) (acc : α) :
    BoundaryFoldM α :=
  let rec visit (e : Expr) (acc : α) : BoundaryFoldM α := do
    if (← get).visited.contains e then
      return acc
    modify fun s => { s with visited := s.visited.insert e }
    if ← isProof e then
      return acc
    match e with
    | .forallE n d b bi =>
      let r ← visit d acc
      withLocalDecl n bi d fun x =>
        visit (b.instantiate1 x) r
    | .lam n d b bi =>
      let r ← visit d acc
      withLocalDecl n bi d fun x =>
        visit (b.instantiate1 x) r
    | .mdata _ b => visit b acc
    | .letE n t v b nondep =>
      let r₁ ← visit t acc
      let r₂ ← visit v r₁
      withLetDecl n t v (nondep := nondep) fun x =>
        visit (b.instantiate1 x) r₂
    | .app f a =>
      let fi ← getFunInfo f (some 1)
      if fi.paramInfo[0]!.isInstImplicit then
        visit f acc
      else
        visit a (← visit f acc)
    | .proj _ _ b => visit b acc
    | .const c _ =>
      if (← get).visitedConsts.contains c then
        return acc
      else
        modify fun s => { s with visitedConsts := s.visitedConsts.insert c }
        if ← isImplicitReducible c then
          return acc
        else
          f c acc
    | _ => return acc
  visit e acc

private unsafe def boundaryRelevantConstants (e : Expr) : MetaM (Array Name) :=
  (boundaryFold (fun n ns => return ns.push n) e #[]).run' {}

/- Persistent environment extension descriptors are intentionally type-erased
   in Environment.persistentEnvExtensionsRef. Exact names, uniqueness, the
   pinned registration index, and the main-only mode are all checked before a
   state is cast. In particular, a suffix or a lookalike extension is never
   accepted as one of these descriptors. -/
private structure BoundaryExtensionIdentity where
  name : Name
  idx : Nat

private unsafe def findBoundaryExtension (identity : BoundaryExtensionIdentity) :
    IO (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState) := do
  let extensions ← persistentEnvExtensionsRef.get
  let found := extensions.filter fun extension => extension.name == identity.name
  unless found.size == 1 do
    throw <| IO.userError s!
      "boundary extension identity is not unique: {identity.name} ({found.size} matches)"
  let extension := found[0]!
  let mainOnly := match extension.toEnvExtension.asyncMode with
    | .mainOnly => true
    | _ => false
  unless extension.name == identity.name &&
      extension.toEnvExtension.idx == identity.idx && mainOnly do
    throw <| IO.userError s!"boundary extension identity mismatch: {identity.name}"
  pure extension

private def moduleDenyListIdentity : BoundaryExtensionIdentity :=
  { name := `Lean.LibrarySuggestions.moduleDenyListExt, idx := 163 }

private def nameDenyListIdentity : BoundaryExtensionIdentity :=
  { name := `Lean.LibrarySuggestions.nameDenyListExt, idx := 164 }

private def typePrefixDenyListIdentity : BoundaryExtensionIdentity :=
  { name := `Lean.LibrarySuggestions.typePrefixDenyListExt, idx := 165 }

private def symbolFrequencyIdentity : BoundaryExtensionIdentity :=
  { name := `symbolFrequency, idx := 212 }

private def triggerDenyListIdentity : BoundaryExtensionIdentity :=
  { name :=
      "_private.Lean.LibrarySuggestions.SineQuaNon.0.Lean.LibrarySuggestions.SineQuaNon.triggerDenyListExt".toName,
    idx := 213 }

private def sineQuaNonIdentity : BoundaryExtensionIdentity :=
  { name := `sineQueNon, idx := 214 }

private abbrev BoundaryModuleDenyListExtension :=
  PersistentEnvExtension String String (List String × List String)

private abbrev BoundaryNameDenyListExtension :=
  PersistentEnvExtension String String (List String × List String)

private abbrev BoundaryTypePrefixDenyListExtension :=
  PersistentEnvExtension Name Name (List Name × List Name)

private abbrev BoundaryTriggerDenyListExtension :=
  PersistentEnvExtension Name Name (List Name × NameSet)

private abbrev BoundarySymbolFrequencyExtension :=
  PersistentEnvExtension (NameMap Nat) Empty (Array (Array (NameMap Nat)))

private structure BoundaryDenyLists where
  modules : List String
  names : List String
  typePrefixes : List Name

private unsafe def boundaryDenyLists (env : Environment) : IO BoundaryDenyLists := do
  let moduleExtension : BoundaryModuleDenyListExtension ←
    unsafeCast <$> findBoundaryExtension moduleDenyListIdentity
  let nameExtension : BoundaryNameDenyListExtension ←
    unsafeCast <$> findBoundaryExtension nameDenyListIdentity
  let typePrefixExtension : BoundaryTypePrefixDenyListExtension ←
    unsafeCast <$> findBoundaryExtension typePrefixDenyListIdentity
  pure {
    modules := (moduleExtension.getState env).2
    names := (nameExtension.getState env).2
    typePrefixes := (typePrefixExtension.getState env).2 }

private def boundaryIsDeniedModule (denyLists : BoundaryDenyLists) (moduleName : Name) : Bool :=
  denyLists.modules.any fun p => moduleName.anyS (· == p)

private def boundaryIsDeniedPremise (env : Environment) (denyLists : BoundaryDenyLists)
    (name : Name) (allowPrivate : Bool := false) : Bool := Id.run do
  if name == ``sorryAx then return true
  if name.isInternalDetail && !(allowPrivate && isPrivateName name) then return true
  if isImplicitReducibleCore env name then return true
  if Lean.Linter.isDeprecated env name then return true
  if denyLists.names.any (fun p => name.anyS (· == p)) then return true
  if let some moduleIdx := env.getModuleIdxFor? name then
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    if boundaryIsDeniedModule denyLists moduleName then
      return true
  let some ci := env.find? name | return true
  if let .const fnName _ := ci.type.getForallBody.getAppFn then
    if denyLists.typePrefixes.any (fun p => p.isPrefixOf fnName) then
      return true
  return false

private unsafe def importedFrequencyFromEnvironment (env : Environment) : IO (NameMap Nat) := do
  let extension : BoundarySymbolFrequencyExtension ←
    unsafeCast <$> findBoundaryExtension symbolFrequencyIdentity
  let mapss := extension.getState env
  pure <| mapss.foldl (init := {}) fun acc maps =>
    maps.foldl (init := acc) fun acc map =>
      map.foldl (init := acc) fun acc name count =>
        acc.insert name (acc.getD name 0 + count)

private unsafe def boundaryTriggerDenyList (env : Environment) : IO NameSet := do
  let extension : BoundaryTriggerDenyListExtension ←
    unsafeCast <$> findBoundaryExtension triggerDenyListIdentity
  pure (extension.getState env).2

private unsafe def localFrequencyExcludingWith
    (excluded : NameSet) (denyLists : BoundaryDenyLists) : MetaM (NameMap Nat) := do
  let env ← getEnv
  env.constants.map₂.foldlM (init := {}) fun acc name info => do
    if excluded.contains name || boundaryIsDeniedPremise env denyLists name ||
        !wasOriginallyTheorem env name then
      pure acc
    else
      let constants ← boundaryRelevantConstants info.type
      pure <| constants.foldl (init := acc) fun acc constant =>
        acc.alter constant fun count? => some (count?.getD 0 + 1)

private def boundaryOrderedInsert (r : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: boundaryOrderedInsert r a l

private def boundaryInsertTrigger (map : NameMap (List (Name × Float)))
    (trigger decl : Name) (tolerance : Float) : NameMap (List (Name × Float)) :=
  map.insert trigger
    (boundaryOrderedInsert (fun x y => x.2 ≤ y.2) (decl, tolerance) (map.getD trigger []))

private unsafe def prepareTriggersWith
    (localMap importedMap : NameMap Nat) (denyLists : BoundaryDenyLists)
    (triggerDenyList : NameSet) (excluded : NameSet := {}) :
    MetaM (NameMap (List (Name × Float))) := do
  let env ← getEnv
  let names := env.constants.map₂.toArray.map (·.1) |>.filter fun name =>
    !excluded.contains name && !boundaryIsDeniedPremise env denyLists name &&
      wasOriginallyTheorem env name
  let mut map := {}
  for name in names do
    let ci ← getConstInfo name
    let constants ← boundaryRelevantConstants ci.type
    let frequencies := constants.filterMap fun constant => do
      if triggerDenyList.contains constant then none else
        let frequency := importedMap.getD constant 0 + localMap.getD constant 0
        if frequency == 0 then none else some (constant, frequency.toFloat)
    unless frequencies.isEmpty do
      let minimum := frequencies.foldl (fun acc (_, f) => min acc f) frequencies[0]!.2
      let triggers := frequencies.filterMap fun (constant, frequency) =>
        if frequency ≤ minimum * 3.0 then some (constant, frequency / minimum) else none
      for (trigger, tolerance) in triggers do
        map := boundaryInsertTrigger map trigger name tolerance
  return map

public structure SuggestionMetadataObservation where
  symbolFrequency : NameMap Nat
  sineQuaNon : NameMap (List (Name × Float))

/- Recompute the derived metadata in a fresh MetaM state. The only imported
   contribution is read from the authenticated persistent extension state; no
   process-global frequency or trigger reference is consulted or updated. -/
private unsafe def observeSuggestionMetadataExcludingWithImportsImpl
    (env importedEnv : Environment) (excluded : NameSet) : IO SuggestionMetadataObservation := do
  let _ ← findBoundaryExtension symbolFrequencyIdentity
  let _ ← findBoundaryExtension sineQuaNonIdentity
  let denyLists ← boundaryDenyLists env
  let triggerDenyList ← boundaryTriggerDenyList env
  let localMap ← runExportMeta env (localFrequencyExcludingWith excluded denyLists)
  let importedMap ← importedFrequencyFromEnvironment importedEnv
  let triggers ← runExportMeta env
    (prepareTriggersWith localMap importedMap denyLists triggerDenyList excluded)
  return { symbolFrequency := localMap, sineQuaNon := triggers }

@[implemented_by observeSuggestionMetadataExcludingWithImportsImpl]
public opaque observeSuggestionMetadataExcludingWithImports
    (env importedEnv : Environment) (excluded : NameSet) :
    IO SuggestionMetadataObservation

private unsafe def observeSuggestionMetadataExcludingImpl (env : Environment)
    (excluded : NameSet) : IO SuggestionMetadataObservation :=
  observeSuggestionMetadataExcludingWithImportsImpl env env excluded

@[implemented_by observeSuggestionMetadataExcludingImpl]
public opaque observeSuggestionMetadataExcluding (env : Environment)
    (excluded : NameSet) : IO SuggestionMetadataObservation

private def moduleDocExtensionName : Name :=
  "_private.Lean.DocString.Extension.0.Lean.moduleDocExt".toName

/-- The declaration oracle compares module documents by exact count, order and
    text, while DeclarationRange follows source layout. Opt-in cached-congruence
    certificates use that same typed policy. -/
private unsafe def canonicalModuleDocEntries
    (extension : PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)
    (entries : OLeanEntries (Array EnvExtensionEntry)) : IO (OLeanEntries (Array EnvExtensionEntry)) := do
  if extension.name != moduleDocExtensionName then return entries
  unless extension.toEnvExtension.idx == moduleDocExt.toEnvExtension.idx &&
      moduleDocExt.name == moduleDocExtensionName do
    throw <| IO.userError "observed_module_doc_extension_identity"
  let canonical (values : Array EnvExtensionEntry) := values.map fun value =>
    let doc : ModuleDoc := unsafeCast value
    unsafeCast ({ doc with declarationRange := default } : ModuleDoc)
  return ⟨canonical entries.exported, canonical entries.server, canonical entries.private⟩

private unsafe def observePrivateModuleDataImpl (env : Environment)
    (canonicalModuleDocs := false) : IO ModuleData := do
  let env := env.setExporting false
  let extensions ← persistentEnvExtensionsRef.get
  let symbolMatches := extensions.filter fun extension =>
    extension.name == symbolFrequencyIdentity.name
  let sineMatches := extensions.filter fun extension =>
    extension.name == sineQuaNonIdentity.name
  unless symbolMatches.size == 1 && sineMatches.size == 1 do
    throw <| IO.userError "observed_derived_extension_identity_missing_or_not_unique"
  let mut localMap? : Option (NameMap Nat) := none
  let mut denyLists? : Option BoundaryDenyLists := none
  let mut triggerDenyList? : Option NameSet := none
  let mut importedMap? : Option (NameMap Nat) := none
  let mut allEntries := #[]
  for extension in extensions do
    let asyncMode := match extension.toEnvExtension.asyncMode with
      | .async _ => .sync
      | mode => mode
    let state := extension.getState (asyncMode := asyncMode) env
    let entries ← if extension.name == symbolFrequencyIdentity.name then do
      let mainOnly := match extension.toEnvExtension.asyncMode with
        | .mainOnly => true
        | _ => false
      unless extension.toEnvExtension.idx == symbolFrequencyIdentity.idx &&
          mainOnly do
        throw <| IO.userError "observed_symbol_frequency_extension_identity"
      let denyLists ← match denyLists? with
        | some lists => pure lists
        | none => do
          let lists ← boundaryDenyLists env
          denyLists? := some lists
          pure lists
      let localMap ← match localMap? with
        | some map => pure map
        | none => do
          let map ← runExportMeta env (localFrequencyExcludingWith {} denyLists)
          localMap? := some map
          pure map
      pure <| OLeanEntries.uniform #[unsafeCast localMap]
    else if extension.name == sineQuaNonIdentity.name then do
      let mainOnly := match extension.toEnvExtension.asyncMode with
        | .mainOnly => true
        | _ => false
      unless extension.toEnvExtension.idx == sineQuaNonIdentity.idx &&
          mainOnly do
        throw <| IO.userError "observed_sine_qua_non_extension_identity"
      let denyLists ← match denyLists? with
        | some lists => pure lists
        | none => do
          let lists ← boundaryDenyLists env
          denyLists? := some lists
          pure lists
      let localMap ← match localMap? with
        | some map => pure map
        | none => do
          let map ← runExportMeta env (localFrequencyExcludingWith {} denyLists)
          localMap? := some map
          pure map
      let importedMap ← match importedMap? with
        | some map => pure map
        | none => do
          let map ← importedFrequencyFromEnvironment env
          importedMap? := some map
          pure map
      let triggerDenyList ← match triggerDenyList? with
        | some denyList => pure denyList
        | none => do
          let denyList ← boundaryTriggerDenyList env
          triggerDenyList? := some denyList
          pure denyList
      let triggers ← runExportMeta env
        (prepareTriggersWith localMap importedMap denyLists triggerDenyList)
      pure <| OLeanEntries.uniform #[unsafeCast triggers]
    else do
      let entries := extension.exportEntriesFn env state
      if canonicalModuleDocs then canonicalModuleDocEntries extension entries else pure entries
    allEntries := allEntries.push (extension.name, entries)
  let filterNonEmpty (level : OLeanLevel) :=
    allEntries.filterMap fun (name, entries) => do
      let values := entries.get level
      guard !values.isEmpty
      pure (name, values)
  let entries := {
    exported := filterNonEmpty .exported
    server := filterNonEmpty .server
    «private» := filterNonEmpty .private }
  mkModuleData env .private (some entries)

/-- Private export data with the pinned frequency/trigger computations
    performed without mutable suggestion caches. All other extension callbacks
    and the optional ModuleDoc canonicalization retain their prior behavior. -/
@[implemented_by observePrivateModuleDataImpl]
opaque observePrivateModuleData (env : Environment) (canonicalModuleDocs := false) : IO ModuleData

end ExplicitLean.SimpEngine.Boundary
