import Mathlib.Tactic.ScopedNS
import ExplicitLean.SimpEngine.FrontendOptions
import Lean.Elab.Frontend
import Lean.Elab.Import
import Lean.Parser.Module

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
  stx.isOfKind `Lean.Parser.Command.mixfix ||
  stx.isOfKind `Mathlib.Tactic.scopedNS

private def elabNotationForParser (command : Syntax) :
    Lean.Elab.Frontend.FrontendM Unit := do
  let before ← Lean.Elab.Frontend.getCommandState
  let scope :: scopes := before.scopes
    | throw <| IO.Error.userError "source-command extractor has no command scope"
  let savedOptions := scope.opts
  let options := Lean.Elab.Term.Quotation.quotPrecheck.set savedOptions false
  Lean.Elab.Frontend.setCommandState {
    before with scopes := { scope with opts := options } :: scopes
  }
  Lean.Elab.Frontend.elabCommandAtFrontend command
  let after ← Lean.Elab.Frontend.getCommandState
  let scope :: scopes := after.scopes
    | throw <| IO.Error.userError "source-command extractor lost its command scope"
  Lean.Elab.Frontend.setCommandState {
    after with scopes := { scope with opts := savedOptions } :: scopes
  }

private def processCommand : Lean.Elab.Frontend.FrontendM Syntax := do
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
  Lean.Elab.Frontend.setParserState nextParserState
  Lean.Elab.Frontend.setMessages messages
  if !messages.hasErrors then
    if definesNotation command then
      elabNotationForParser command
    else if affectsParserContext command then
      Lean.Elab.Frontend.elabCommandAtFrontend command
  return command

private partial def processCommands (commands : Array Syntax := #[]) :
    Lean.Elab.Frontend.FrontendM (Array Syntax) := do
  let command ← processCommand
  if command.isOfKind ``Lean.Parser.Command.eoi then
    return commands
  let commands := commands.push command
  if Parser.isTerminalCommand command then
    return commands
  processCommands commands

private unsafe def parseFileFully (path : System.FilePath) (source : String)
    (header : Lean.Elab.HeaderSyntax) (parserState : Parser.ModuleParserState)
    (headerMessages : MessageLog) : IO (Array Syntax × MessageLog) := do
  let inputCtx := Parser.mkInputContext source path.toString
  Lean.enableInitializersExecution
  let (env, messages) ← Lean.Elab.processHeader header
    ExplicitLean.SimpEngine.mathlibParserOptions headerMessages inputCtx
    (mainModule := `SourceCommandExtractorFallback)
  let state ← Lean.Elab.IO.processCommands inputCtx parserState
    (Lean.Elab.Command.mkState env messages ExplicitLean.SimpEngine.mathlibParserOptions)
  if state.commandState.messages.hasErrors then
    for message in state.commandState.messages.toArray do
      if message.severity == .error then
        IO.eprintln s!"{message.pos.line}:{message.pos.column}: {← message.data.toString}"
    throw <| IO.Error.userError "exact-import frontend reported an error or recovery"
  let commands := state.commands.filter fun command =>
    !command.isOfKind ``Lean.Parser.Command.eoi
  return (commands, state.commandState.messages)

private unsafe def parseFile (path : System.FilePath) (source : String) :
    IO (Array Syntax × MessageLog × Array Lean.Import) := do
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  if headerMessages.hasErrors then
    throw <| IO.Error.userError "Lean header parser reported an error"
  -- Preserve every header modifier for the frontend environment.  The
  -- database projects these imports to names later, but Lean's parser needs
  -- `isMeta`, `importAll`, and `isExported` to match the source header.
  let imports := Lean.Elab.HeaderSyntax.imports header false
  if parserState.pos.byteIdx >= inputCtx.endPos.byteIdx then
    return (#[], headerMessages, imports)
  Lean.enableInitializersExecution
  -- The fast pass keeps the exact parser context used by the source.  A
  -- source-local notation can refer to a declaration made earlier in that
  -- same file; its bounded exact-import frontend fallback handles that case.
  let env ← Lean.importModules imports ExplicitLean.SimpEngine.mathlibParserOptions
    (loadExts := true)
  let initialState : Lean.Elab.Frontend.State := {
    commandState := Lean.Elab.Command.mkState env headerMessages
      ExplicitLean.SimpEngine.mathlibIncrementalParserOptions
    parserState
    cmdPos := parserState.pos
  }
  try
    let (commands, state) ←
      (processCommands.run { inputCtx }).run initialState
    if state.commandState.messages.hasErrors then
      throw <| IO.Error.userError "incremental parser reported an error or recovery"
    return (commands, state.commandState.messages, imports)
  catch _ =>
    let (commands, messages) ← parseFileFully path source header parserState headerMessages
    return (commands, messages, imports)

private def sourceRange (command : Syntax) : IO (String.Pos.Raw × String.Pos.Raw) := do
  let some start := command.getPos? (canonicalOnly := true)
    | throw <| IO.Error.userError "command has no canonical start position"
  let some stop := command.getTailPos? (canonicalOnly := true)
    | throw <| IO.Error.userError "command has no canonical end position"
  if start.byteIdx >= stop.byteIdx then
    throw <| IO.Error.userError "command has an empty or reversed source range"
  return (start, stop)

private def commandJson (ordinal : Nat) (command : Syntax) : IO Json := do
  let (start, stop) ← sourceRange command
  return Json.mkObj [
    ("ordinal", toJson ordinal),
    ("startByte", toJson start.byteIdx),
    ("endByte", toJson stop.byteIdx),
    ("kind", toJson command.getKind.toString)]

private def uniqueImports (imports : Array Lean.Import) : Array Lean.Import :=
  imports.foldl (init := #[]) fun result imported =>
    if result.any (fun prior => prior.module == imported.module) then
      result
    else
      result.push imported

private unsafe def emitFile (path : System.FilePath) : IO UInt32 := do
  let source ← IO.FS.readFile path
  try
    let (commands, _messages, imports) ← parseFile path source
    let commandJsons ← commands.mapIdxM (fun ordinal command => commandJson ordinal command)
    let importJsons := (uniqueImports imports).map fun imported =>
      Json.mkObj [("name", toJson imported.module.toString)]
    let result := Json.mkObj [
      ("path", toJson path.toString),
      ("imports", Json.arr importJsons),
      ("commands", Json.arr commandJsons)]
    IO.println result.compress
    return 0
  catch error =>
    IO.eprintln s!"source-command extractor could not parse {path}: {error}"
    return 1

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: sourceCommandExtractor <Lean source file>..."
    return 2
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let mut status := 0
  for pathString in args do
    let code ← emitFile (System.FilePath.mk pathString)
    if code != 0 then
      status := code
  return status
