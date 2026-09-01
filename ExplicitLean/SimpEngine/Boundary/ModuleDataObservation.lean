/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
SPDX-License-Identifier: Apache-2.0
License: https://www.apache.org/licenses/LICENSE-2.0
Authors of upstream code: Leonardo de Moura, Kim Morrison

Adapted from the pinned Lean 4.32.2 LibrarySuggestions/SymbolFrequency.lean,
LibrarySuggestions/SineQuaNon.lean, and Environment.lean export computations.
The adaptations retain their data policy while avoiding the two frequency-cache
writes in the substituted LibrarySuggestions export callbacks.
-/
module
prelude

public meta import Lean.Meta.Basic
public meta import ExplicitLean.SimpEngine.Boundary.NoSynthesis
meta import all Lean.Environment
meta import all Lean.DocString.Extension
meta import all Lean.LibrarySuggestions.SymbolFrequency
meta import all Lean.LibrarySuggestions.SineQuaNon

public meta section
open Lean Meta
namespace ExplicitLean.SimpEngine.Boundary

private def runExportMeta (env : Environment) (action : MetaM α) : IO α :=
  ((withoutBoundaryPendingSynthesis (withoutExporting action)).run' {} {}).toIO'
    { fileName := "symbolFrequency", fileMap := default, maxHeartbeats := 0 } { env }

private def importedFrequency (env : Environment) : IO (NameMap Nat) := do
  if let some map ← LibrarySuggestions.symbolFrequencyMapRef.get then return map
  let mapss := LibrarySuggestions.symbolFrequencyExt.getState env
  return mapss.foldl (init := {}) fun acc maps =>
    maps.foldl (init := acc) fun acc map =>
      map.foldl (init := acc) fun acc name count =>
        acc.insert name (acc.getD name 0 + count)

private def importedFrequencyFromEnvironment (env : Environment) : NameMap Nat :=
  let mapss := LibrarySuggestions.symbolFrequencyExt.getState env
  mapss.foldl (init := {}) fun acc maps =>
    maps.foldl (init := acc) fun acc map =>
      map.foldl (init := acc) fun acc name count =>
        acc.insert name (acc.getD name 0 + count)

private def prepareTriggers (localMap importedMap : NameMap Nat) (excluded : NameSet := {}) :
    MetaM (NameMap (List (Name × Float))) := do
  let env ← getEnv
  let denyList := LibrarySuggestions.SineQuaNon.triggerDenyListExt.getState env
  let names := env.constants.map₂.toArray.map (·.1) |>.filter fun name =>
    !excluded.contains name && !LibrarySuggestions.isDeniedPremise env name &&
      wasOriginallyTheorem env name
  let mut map := {}
  for name in names do
    let ci ← getConstInfo name
    let constants ← ci.type.relevantConstants
    let frequencies := constants.filterMap fun name => do
      if denyList.contains name then none else
        let frequency := importedMap.getD name 0 + localMap.getD name 0
        if frequency == 0 then none else some (name, frequency.toFloat)
    unless frequencies.isEmpty do
      let minimum := frequencies.foldl (fun acc (_, f) => min acc f) frequencies[0]!.2
      let triggers := frequencies.filterMap fun (name, f) =>
        if f ≤ minimum * 3.0 then some (name, f / minimum) else none
      for (trigger, tolerance) in triggers do
        map := LibrarySuggestions.SineQuaNon.insertTrigger map trigger name tolerance
  return map

public structure SuggestionMetadataObservation where
  symbolFrequency : NameMap Nat
  sineQuaNon : NameMap (List (Name × Float))

private def localFrequencyExcluding (excluded : NameSet) : MetaM (NameMap Nat) := do
  let env ← getEnv
  env.constants.map₂.foldlM (init := {}) fun acc name info => do
    if excluded.contains name || LibrarySuggestions.isDeniedPremise env name ||
        !wasOriginallyTheorem env name then
      pure acc
    else
      info.type.foldRelevantConstants (init := acc) fun constant acc =>
        pure <| acc.alter constant fun count? => some (count?.getD 0 + 1)

/-- Recompute the two derived LibrarySuggestions export maps from one
    environment while omitting an authenticated set of proof auxiliaries.
    This never reads or writes the process-global frequency caches. -/
private unsafe def observeSuggestionMetadataExcludingImpl (env : Environment)
    (excluded : NameSet) : IO SuggestionMetadataObservation := do
  let extensions ← persistentEnvExtensionsRef.get
  let some symbolExtension := extensions.find? (·.name == `symbolFrequency)
    | throw <| IO.userError "observed_symbol_frequency_extension_missing"
  unless symbolExtension.toEnvExtension.idx ==
      LibrarySuggestions.symbolFrequencyExt.toEnvExtension.idx do
    throw <| IO.userError "observed_symbol_frequency_extension_identity"
  let some sineExtension := extensions.find? (·.name == `sineQueNon)
    | throw <| IO.userError "observed_sine_qua_non_extension_missing"
  unless sineExtension.toEnvExtension.idx ==
      LibrarySuggestions.SineQuaNon.sineQuaNonExt.toEnvExtension.idx do
    throw <| IO.userError "observed_sine_qua_non_extension_identity"
  let localMap ← runExportMeta env (localFrequencyExcluding excluded)
  let importedMap := importedFrequencyFromEnvironment env
  let triggers ← runExportMeta env (prepareTriggers localMap importedMap excluded)
  return { symbolFrequency := localMap, sineQuaNon := triggers }

@[implemented_by observeSuggestionMetadataExcludingImpl]
public opaque observeSuggestionMetadataExcluding (env : Environment)
    (excluded : NameSet) : IO SuggestionMetadataObservation

private def moduleDocExtensionName : Name :=
  "_private.Lean.DocString.Extension.0.Lean.moduleDocExt".toName

/-- The completed source/cold declaration oracle compares module documents by
    exact count, order and text, while DeclarationRange follows source layout.
    Opt-in cached-congruence certificates use that same typed policy. The
    registered extension identity guards the pinned ModuleDoc cast; suffix
    lookalikes retain their original bytes. No environment state is changed. -/
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
  let mut localMap? : Option (NameMap Nat) := none
  let mut allEntries := #[]
  for extension in extensions do
    let asyncMode := match extension.toEnvExtension.asyncMode with
      | .async _ => .sync
      | mode => mode
    let state := extension.getState (asyncMode := asyncMode) env
    let entries ← if extension.name == `symbolFrequency || extension.name == `sineQueNon then do
      let localMap ← match localMap? with
        | some map => pure map
        | none => do
          let map ← match ← LibrarySuggestions.localSymbolFrequencyMapRef.get with
            | some map => pure map
            | none => runExportMeta env LibrarySuggestions.localSymbolFrequencyMap
          localMap? := some map
          pure map
      if extension.name == `symbolFrequency then
        unless extension.toEnvExtension.idx == LibrarySuggestions.symbolFrequencyExt.toEnvExtension.idx do
          throw <| IO.userError "observed_symbol_frequency_extension_identity"
        pure <| OLeanEntries.uniform #[unsafeCast localMap]
      else
        unless extension.toEnvExtension.idx == LibrarySuggestions.SineQuaNon.sineQuaNonExt.toEnvExtension.idx do
          throw <| IO.userError "observed_sine_qua_non_extension_identity"
        let importedMap ← importedFrequency env
        let triggers ← runExportMeta env (prepareTriggers localMap importedMap)
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

/-- Private export data with the pinned LibrarySuggestions frequency/trigger export
computations performed without writing their global caches. All other extension
callbacks are retained unchanged and may write these or other caches; this does
not assert their observational purity. ModuleDoc ranges are canonicalized only
when explicitly requested; default observations retain their raw entries. -/
@[implemented_by observePrivateModuleDataImpl]
opaque observePrivateModuleData (env : Environment) (canonicalModuleDocs := false) : IO ModuleData

end ExplicitLean.SimpEngine.Boundary
