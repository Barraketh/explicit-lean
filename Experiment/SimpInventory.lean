import Mathlib
import ExplicitLean.SimpInventory
import Lean.Data.Json
import Lean.Elab.Frontend
import Lean.Parser.Module
import Lean.Util.Path

open Lean Parser

private def affectsParserContext (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Command.«namespace» ||
  stx.isOfKind ``Lean.Parser.Command.«section» ||
  stx.isOfKind ``Lean.Parser.Command.«end» ||
  stx.isOfKind ``Lean.Parser.Command.«open»

private def processInventoryCommand : Lean.Elab.Frontend.FrontendM Bool := do
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
  if affectsParserContext command then
    Lean.Elab.Frontend.elabCommandAtFrontend command
  return Parser.isTerminalCommand command

private partial def processInventoryCommands : Lean.Elab.Frontend.FrontendM Unit := do
  unless ← processInventoryCommand do
    processInventoryCommands

private def parseModuleIncrementally (env : Environment) (path : System.FilePath)
    (source : String) : IO (Syntax × Bool) := do
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let initialState : Lean.Elab.Frontend.State := {
    commandState := Lean.Elab.Command.mkState env messages
    parserState
    cmdPos := parserState.pos
  }
  let (_, state) ← (processInventoryCommands.run { inputCtx }).run initialState
  let moduleSyntax := mkNode `Lean.Parser.Module.module #[header.raw, mkListNode state.commands]
  return (moduleSyntax, state.commandState.messages.hasErrors)

private unsafe def inventoryFile (env : Environment) (path : System.FilePath) : IO UInt32 := do
  let source ← IO.FS.readFile path
  let fileMap := FileMap.ofString source
  try
    let (stx, hasErrors) ← parseModuleIncrementally env path source
    for entry in ExplicitLean.SimpInventory.collect path.toString fileMap stx do
      IO.println (toJson entry).compress
    if hasErrors then
      let payload := Json.mkObj [("file", toJson path.toString),
        ("error", toJson "incremental syntax parser recovered")]
      IO.println s!"EXPLICIT_LEAN_INVENTORY_PARSE_FAILURE {payload.compress}"
    return 0
  catch error =>
    let payload := Json.mkObj [("file", toJson path.toString), ("error", toJson (toString error))]
    IO.println s!"EXPLICIT_LEAN_INVENTORY_PARSE_FAILURE {payload.compress}"
    return 0

unsafe def main (args : List String) : IO UInt32 := do
  let paths ← match args with
    | ["--files-from", manifest] =>
        pure ((← IO.FS.readFile manifest).splitOn "\n" |>.filter (!·.isEmpty))
    | paths => pure paths
  if paths.isEmpty then
    IO.eprintln "usage: SimpInventory.lean [--files-from manifest | <Mathlib source file>...]"
    return 2
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Mathlib }] {} (loadExts := true)
  let mut status := 0
  for pathString in paths do
    let path := System.FilePath.mk pathString
    let code ← inventoryFile env path
    if code != 0 then
      status := code
  return status
