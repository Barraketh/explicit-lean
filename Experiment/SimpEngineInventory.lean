import Mathlib.Tactic.ScopedNS
import ExplicitLean.SimpEngine.FrontendOptions
import ExplicitLean.SimpEngine.Inventory
import Lean.Elab.Frontend
import Lean.Elab.Import
import Lean.Parser.Module
import Lean.Util.Path

open Lean Parser

private def affectsParserContext (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Command.«namespace» ||
  stx.isOfKind ``Lean.Parser.Command.«section» ||
  stx.isOfKind ``Lean.Parser.Command.«end» ||
  stx.isOfKind ``Lean.Parser.Command.«open»

private def definesNotation (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Command.syntax ||
  stx.isOfKind ``Lean.Parser.Command.«notation» ||
  stx.isOfKind ``Lean.Parser.Command.«mixfix» ||
  stx.isOfKind `Mathlib.Tactic.scopedNS

private def elabNotationForParser (command : Syntax) : Lean.Elab.Frontend.FrontendM Unit := do
  let before ← Lean.Elab.Frontend.getCommandState
  let scope :: scopes := before.scopes
    | throw <| IO.Error.userError "inventory frontend has no command scope"
  let savedOptions := scope.opts
  let options := Lean.Elab.Term.Quotation.quotPrecheck.set savedOptions false
  Lean.Elab.Frontend.setCommandState {
    before with scopes := { scope with opts := options } :: scopes
  }
  Lean.Elab.Frontend.elabCommandAtFrontend command
  let after ← Lean.Elab.Frontend.getCommandState
  let scope :: scopes := after.scopes
    | throw <| IO.Error.userError "inventory notation removed its command scope"
  Lean.Elab.Frontend.setCommandState {
    after with scopes := { scope with opts := savedOptions } :: scopes
  }

private def processInventoryCommand : Lean.Elab.Frontend.FrontendM (Bool × Bool) := do
  Lean.Elab.Frontend.updateCmdPos
  let commandState ← Lean.Elab.Frontend.getCommandState
  let inputCtx ← Lean.Elab.Frontend.getInputContext
  let parserState ← Lean.Elab.Frontend.getParserState
  let scope := commandState.scopes.head!
  let parserContext : ParserModuleContext := {
    env := commandState.env
    options := scope.opts
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls
  }
  let (command, nextParserState, messages) :=
    Parser.parseCommand inputCtx parserContext parserState commandState.messages
  modify fun state => { state with commands := state.commands.push command }
  Lean.Elab.Frontend.setParserState nextParserState
  Lean.Elab.Frontend.setMessages messages
  let parserHadErrors := messages.hasErrors
  if definesNotation command then
    elabNotationForParser command
  else if affectsParserContext command then
    Lean.Elab.Frontend.elabCommandAtFrontend command
  return (Parser.isTerminalCommand command, parserHadErrors)

private partial def processInventoryCommands : Lean.Elab.Frontend.FrontendM Bool := do
  let (terminal, parserHadErrors) ← processInventoryCommand
  if terminal then
    return parserHadErrors
  let laterHadErrors ← processInventoryCommands
  return parserHadErrors || laterHadErrors

private def parseModuleIncrementally (env : Environment) (path : System.FilePath)
    (source : String) : IO (Syntax × MessageLog × Bool) := do
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let initialState : Lean.Elab.Frontend.State := {
    commandState := Lean.Elab.Command.mkState env messages
      ExplicitLean.SimpEngine.mathlibIncrementalParserOptions
    parserState
    cmdPos := parserState.pos
  }
  let (parserHadErrors, state) ← (processInventoryCommands.run { inputCtx }).run initialState
  let moduleSyntax := mkNode `Lean.Parser.Module.module #[header.raw, mkListNode state.commands]
  return (moduleSyntax, state.commandState.messages, parserHadErrors)

private unsafe def parseModuleFully (path : System.FilePath)
    (source : String) : IO (Syntax × MessageLog) := do
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  Lean.enableInitializersExecution
  let (env, messages) ← Lean.Elab.processHeader header
    ExplicitLean.SimpEngine.mathlibParserOptions messages inputCtx
    (mainModule := `ExplicitLean.SimpEngine.InventoryFallback)
  let state ← Lean.Elab.IO.processCommands inputCtx parserState
    (Lean.Elab.Command.mkState env messages ExplicitLean.SimpEngine.mathlibParserOptions)
  let moduleSyntax := mkNode `Lean.Parser.Module.module #[header.raw, mkListNode state.commands]
  return (moduleSyntax, state.commandState.messages)

private unsafe def inventoryFile (aggregateEnv? : Option Environment) (path : System.FilePath)
    (allowElaborationErrors deferFullFallback fullFallbackOnly : Bool) : IO UInt32 := do
  let source ← IO.FS.readFile path
  let fileMap := FileMap.ofString source
  try
    let finish (stx : Syntax) (messages : MessageLog) : IO UInt32 := do
      if messages.hasErrors && !allowElaborationErrors then
        IO.eprintln s!"simp engine inventory could not parse {path} without recovery"
        for message in messages.toArray do
          if message.severity == .error then
            IO.eprintln s!"{message.pos.line}:{message.pos.column}: {← message.data.toString}"
        return 1
      if messages.hasErrors then
        IO.println s!"SIMP_ENGINE_INVENTORY_ELABORATION_ERRORS_ALLOWED file={path}"
      for entry in ExplicitLean.SimpEngine.Inventory.collect path.toString fileMap stx do
        IO.println (toJson entry).compress
      return 0
    if fullFallbackOnly then
      IO.println s!"SIMP_ENGINE_INVENTORY_FULL_FALLBACK file={path}"
      let (stx, messages) ← parseModuleFully path source
      return ← finish stx messages
    -- Rewritten sources import replay syntax absent from aggregate Mathlib.
    -- Parsing with the wrong environment can silently consume a later branch,
    -- even without a recovery error. Remaining-call audits use actual imports.
    let env ← match aggregateEnv? with
      | some env => pure env
      | none =>
        let (header, _, _) ← Parser.parseHeader (Parser.mkInputContext source path.toString)
        Lean.importModules (Lean.Elab.HeaderSyntax.imports header) {} (loadExts := true)
    let (fastSyntax, fastMessages, fastParserHadErrors) ←
      parseModuleIncrementally env path source
    if fastParserHadErrors || fastMessages.hasErrors then
      if deferFullFallback then
        IO.println s!"SIMP_ENGINE_INVENTORY_DEFERRED_FALLBACK file={path}"
        return 0
      IO.println s!"SIMP_ENGINE_INVENTORY_FULL_FALLBACK file={path}"
      let (stx, messages) ← parseModuleFully path source
      return ← finish stx messages
    else
      return ← finish fastSyntax fastMessages
  catch error =>
    IO.eprintln s!"simp engine inventory failed for {path}: {error}"
    return 1

unsafe def main (args : List String) : IO UInt32 := do
  let allowElaborationErrors := args.contains "--allow-elaboration-errors"
  let headerImports := args.contains "--header-imports"
  let deferFullFallback := args.contains "--defer-full-fallback"
  let fullFallbackOnly := args.contains "--full-fallback-only"
  if deferFullFallback && fullFallbackOnly then
    IO.eprintln "inventory fallback modes are mutually exclusive"
    return 2
  let paths := args.filter fun arg =>
    arg != "--allow-elaboration-errors" && arg != "--header-imports" &&
      arg != "--defer-full-fallback" && arg != "--full-fallback-only"
  if paths.isEmpty then
    IO.eprintln "usage: SimpEngineInventory.lean [--allow-elaboration-errors] [--header-imports] [--defer-full-fallback | --full-fallback-only] <Lean source file>..."
    return 2
  if fullFallbackOnly && paths.length != 1 then
    IO.eprintln "inventory full fallback mode requires exactly one source"
    return 2
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env : Option Environment ← if headerImports || fullFallbackOnly then pure none else do
    let aggregate ← Lean.importModules #[{ module := `Mathlib }] {} (loadExts := true)
    pure (some aggregate)
  let mut status := 0
  for pathString in paths do
    let code ← inventoryFile env (System.FilePath.mk pathString) allowElaborationErrors
      deferFullFallback fullFallbackOnly
    if code != 0 then
      status := code
  return status
