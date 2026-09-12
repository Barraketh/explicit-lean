/-
Full-Boundary-only differential probe. This file intentionally imports the
pinned suggestion implementation so that a fresh process can compare its
derived maps with the search-free Boundary observer. It is not part of the
Tactic import closure.
-/
module
prelude

public import ExplicitLean.SimpEngine.Boundary
public import Lean.Elab.Command
public import Lean.Parser.Command
public meta import Lean.LibrarySuggestions.SymbolFrequency
public import Lean.LibrarySuggestions.SineQuaNon
meta import all Lean.LibrarySuggestions.SineQuaNon

open Lean Meta

private meta def runMeta (env : Environment) (action : MetaM α) : IO α :=
  ((withoutExporting action).run' {} {}).toIO'
    { fileName := "metadata-differential", fileMap := default, maxHeartbeats := 0 } { env }

private meta def withExtensions (extensions :
    Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState))
    (action : IO α) : IO α := do
  let original ← persistentEnvExtensionsRef.get
  persistentEnvExtensionsRef.set extensions
  try
    let result ← action
    persistentEnvExtensionsRef.set original
    pure result
  catch error =>
    persistentEnvExtensionsRef.set original
    throw error

private meta def duplicateExtensionRejected (env : Environment) : IO Bool := do
  let extensions ← persistentEnvExtensionsRef.get
  let some extension := extensions.find? (·.name == `symbolFrequency)
    | throw <| IO.userError "metadata_differential_probe: symbol extension missing"
  withExtensions (extensions.push extension) do
    try
      let _ ← ExplicitLean.SimpEngine.Boundary.observePrivateModuleData env
      pure false
    catch _ => pure true

private meta def missingExtensionsRejected (env : Environment) : IO Bool := do
  let extensions ← persistentEnvExtensionsRef.get
  let filtered := extensions.filter fun extension =>
    extension.name != `symbolFrequency && extension.name != `sineQueNon
  withExtensions filtered do
    try
      let _ ← ExplicitLean.SimpEngine.Boundary.observePrivateModuleData env
      pure false
    catch _ => pure true

elab "metadata_differential_probe" : command => do
  let env ← getEnv
  unless (← Lean.LibrarySuggestions.localSymbolFrequencyMapRef.get).isNone &&
      (← Lean.LibrarySuggestions.symbolFrequencyMapRef.get).isNone &&
      (← Lean.LibrarySuggestions.SineQuaNon.sineQuaNonTriggersRef.get).isNone do
    throwError "metadata_differential_probe: suggestion cache was populated before observation"
  let observed ← ExplicitLean.SimpEngine.Boundary.observeSuggestionMetadataExcluding env {}
  let directLocal ← runMeta env Lean.LibrarySuggestions.localSymbolFrequencyMap
  let directTriggers ← runMeta env do
    Lean.LibrarySuggestions.SineQuaNon.prepareTriggers (env.constants.map₂.toArray.map (·.1))
  unless observed.symbolFrequency.toList == directLocal.toList do
    throwError "metadata_differential_probe: symbol-frequency mismatch"
  unless observed.sineQuaNon.toList == directTriggers.toList do
    throwError "metadata_differential_probe: trigger mismatch"
  let _ ← ExplicitLean.SimpEngine.Boundary.observePrivateModuleData env
  let missingRejected ← missingExtensionsRejected env
  unless missingRejected do
    throwError "metadata_differential_probe: missing extensions were accepted"
  let duplicateRejected ← duplicateExtensionRejected env
  unless duplicateRejected do
    throwError "metadata_differential_probe: duplicate extension was accepted"
  unless (← Lean.LibrarySuggestions.localSymbolFrequencyMapRef.get).isNone &&
      (← Lean.LibrarySuggestions.symbolFrequencyMapRef.get).isNone &&
      (← Lean.LibrarySuggestions.SineQuaNon.sineQuaNonTriggersRef.get).isNone do
    throwError "metadata_differential_probe: suggestion cache was populated by observation"
  logInfo "BOUNDARY_METADATA_DIFFERENTIAL symbolFrequency=true sineQuaNon=true fullObserver=true missingRejected=true duplicateRejected=true cachePure=true"

theorem metadataDifferentialIdentity (n : Nat) : n = n := rfl

theorem metadataDifferentialFunction (p : Nat → Prop) (h : ∀ n, p n) : p 0 := h 0

metadata_differential_probe
