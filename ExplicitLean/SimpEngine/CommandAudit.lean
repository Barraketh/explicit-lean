module

public meta import Lean.Elab.Frontend
public meta import Lean.DeclarationRange
public meta import ExplicitLean.SimpEngine.Inventory

public meta section

open Lean

namespace ExplicitLean.SimpEngine.CommandAudit

def marker : String := "SIMP_ENGINE_COMMAND_AUDIT "
def nonceVariable : String := "SIMP_ENGINE_BOUNDARY_RUN_NONCE"
def enabledVariable : String := "SIMP_ENGINE_COMMAND_AUDIT"

structure Captured where
  private mk ::
  environment : Environment
  commands : Array Syntax
  source : String
  file : String

private initialize collectorSerial : IO.Ref Nat ← IO.mkRef 0

private def registerCollector (file : String) (moduleName : Name)
    (captured : IO.Ref (Array (Array Syntax))) : IO Name := do
  let mut serial ← collectorSerial.get
  let existing ← Elab.Command.moduleLintersRef.get
  while existing.any (·.name == .num `_explicitLeanCommandAuditCollector serial) do
    serial := serial + 1
  collectorSerial.set (serial + 1)
  let name := Name.num `_explicitLeanCommandAuditCollector serial
  Elab.Command.addModuleLinter {
    name
    run := fun commands => do
      if (← read).fileName == file && (← getEnv).mainModule == moduleName then
        captured.modify (·.push commands)
  }
  return name

private def unregisterCollector (name : Name) : IO Unit := do
  let linters ← Elab.Command.moduleLintersRef.get
  let matching := linters.filter (·.name == name)
  -- Names are fresh within this process. Do not reset the registry to its old
  -- value: target imports may have registered unrelated linters in the meantime.
  Elab.Command.moduleLintersRef.set (linters.filter (·.name != name))
  unless matching.size == 1 do
    throw <| IO.userError "command_audit_collector_registration_changed"

/-- A scoped, read-only observer of the unchanged ordinary frontend. The final
    module linter receives the complete parsed command array even when ordinary
    command-line snapshots discard individual command syntax. `runFrontend`
    waits for linter tasks and performs its normal error handling/postprocessing.
    Calls in one process must be sequential, as with the underlying frontend. -/
unsafe def capture (source : String) (options : Options) (file : String)
    (moduleName : Name) (oleanFileName? : Option System.FilePath := none) : IO Captured := do
  enableInitializersExecution
  let captured ← IO.mkRef (#[] : Array (Array Syntax))
  let collector ← registerCollector file moduleName captured
  try
    let some environment ← Elab.runFrontend source options file moduleName (oleanFileName? := oleanFileName?)
      | throw <| IO.userError "command_audit_frontend_failed"
    unless environment.mainModule == moduleName do
      throw <| IO.userError "command_audit_module_identity_mismatch"
    let collections ← captured.get
    unless collections.size == 1 do
      throw <| IO.userError s!"command_audit_callback_count:{collections.size}"
    return { environment, commands := collections[0]!, source, file }
  finally
    unregisterCollector collector

private structure Occurrence where
  module : String
  startByte : Nat
  endByte : Nat
  line : Nat
  column : Nat
  kind : String
  source : String
  ancestors : Array String
  commandKind : Option String
  commandStartByte : Option Nat
  commandEndByte : Option Nat
  deriving ToJson

private structure CommandAncestor where
  kind : String
  startByte : Nat
  endByte : Nat

private def commandAncestor? (stx : Syntax) : Option CommandAncestor := do
  let range ← stx.getRange?
  let kind := stx.getKind.toString
  guard (kind.startsWith "Lean.Parser.Command.")
  guard (![".declValSimple", ".declValEqns", ".declSig", ".declId", ".macroTail", ".macroRhs"].any
    (fun suffix => kind.endsWith suffix))
  return { kind, startByte := range.start.byteIdx, endByte := range.stop.byteIdx }

private partial def collect (module : String) (fileMap : FileMap)
    (stx : Syntax) (ancestors : Array String := #[])
    (command? : Option CommandAncestor := none)
    (entries : Array Occurrence := #[]) : Array Occurrence := Id.run do
  let ancestors := ancestors.push stx.getKind.toString
  let command? := (commandAncestor? stx).orElse (fun _ => command?)
  let mut entries := entries
  if stx.isOfKind ``Lean.Parser.Tactic.simp then
    if let some range := stx.getRange? then
      let position := fileMap.toPosition range.start
      entries := entries.push {
        module, startByte := range.start.byteIdx, endByte := range.stop.byteIdx
        line := position.line, column := position.column
        kind := if stx[3].isNone then "simp" else "simp_only"
        source := String.Pos.Raw.extract fileMap.source range.start range.stop
        ancestors
        commandKind := command?.map (·.kind)
        commandStartByte := command?.map (·.startByte)
        commandEndByte := command?.map (·.endByte)
      }
  for arg in stx.getArgs do
    entries := collect module fileMap arg ancestors command? entries
  return entries

private unsafe def declarations (env : Environment) (source : String) : IO (Array Json) := do
  let mut result := #[]
  -- Match mkModuleData's private checked declaration order without running
  -- persistent export hooks, which may mutate process-global caches.
  let constants := env.toKernelEnv.constants.foldStage2 (fun cs _ info => cs.push info) #[]
  let fileMap := FileMap.ofString source
  for info in constants do
    if env.isImportedConst info.name then continue
    let some ranges := declRangeExt.find? (level := .exported) env info.name <|>
        declRangeExt.find? (level := .server) env info.name | continue
    let isProof ← PPContext.runMetaM {
      env, opts := {}, currNamespace := .anonymous, openDecls := [] } (Meta.isProp info.type)
    result := result.push <| Json.mkObj [
      ("module", toJson env.mainModule.toString), ("name", toJson info.name.toString),
      ("startByte", toJson (fileMap.ofPosition ranges.range.pos).byteIdx),
      ("endByte", toJson (fileMap.ofPosition ranges.range.endPos).byteIdx),
      ("isProof", toJson isProof)]
  return result

/-- Exact source text binds the audit to the bytes read by this frontend; the
    Python consumer verifies it against its immutable input and hashes it. -/
unsafe def reportJson (captured : Captured) (label : String) : IO Json := do
  unless ["standalone", "stock", "applied"].contains label do
    throw <| IO.userError "command_audit_invalid_label"
  let env := captured.environment
  let source := captured.source
  let file := captured.file
  let fileMap := FileMap.ofString source
  let entries := captured.commands.foldl
    (fun entries command => collect env.mainModule.toString fileMap command #[] none entries) #[]
  let rawCount := captured.commands.foldl
    (fun count command => count + (Inventory.collect file fileMap command).size) 0
  unless rawCount == entries.size do
    throw <| IO.userError "command_audit_occurrence_count_mismatch"
  return Json.mkObj [
    ("kind", .str "simp_engine_command_audit"), ("schema", toJson (1 : Nat)),
    ("label", .str label), ("module", toJson env.mainModule.toString),
    ("isModule", toJson env.header.isModule), ("sourcePath", .str file), ("source", .str source),
    ("callbackCount", toJson (1 : Nat)), ("commandCount", toJson captured.commands.size),
    ("rawCount", toJson rawCount), ("occurrences", toJson entries),
    ("declarations", toJson (← declarations env source))]

def runNonce : IO String := do
  let some nonce ← IO.getEnv nonceVariable
    | throw <| IO.userError "command_audit_missing_run_nonce"
  unless !nonce.isEmpty && !nonce.toList.any Char.isWhitespace do
    throw <| IO.userError "command_audit_invalid_run_nonce"
  return nonce

unsafe def emit (captured : Captured) (label nonce : String) : IO Unit := do
  let report ← reportJson captured label
  IO.println s!"\n{marker}{nonce} {report.compress}"

end ExplicitLean.SimpEngine.CommandAudit
