import Mathlib.Tactic.ScopedNS
import ExplicitLean.SimpEngine.FrontendOptions
import Lean.DeclarationRange
import Lean.Elab.Frontend
import Lean.Elab.Import
import Lean.Parser.Module
import Lean.Util.Path

open Lean Parser

namespace ExplicitLean.SimpEngine.BoundaryScope

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

private def elabNotationForParser
    (command : Syntax) : Lean.Elab.Frontend.FrontendM Unit := do
  let before ← Lean.Elab.Frontend.getCommandState
  let scope :: scopes := before.scopes
    | throw <| IO.Error.userError "scope classifier frontend has no command scope"
  let savedOptions := scope.opts
  let options := Lean.Elab.Term.Quotation.quotPrecheck.set savedOptions false
  Lean.Elab.Frontend.setCommandState {
    before with scopes := { scope with opts := options } :: scopes
  }
  Lean.Elab.Frontend.elabCommandAtFrontend command
  let after ← Lean.Elab.Frontend.getCommandState
  let scope :: scopes := after.scopes
    | throw <| IO.Error.userError "scope classifier notation removed its command scope"
  Lean.Elab.Frontend.setCommandState {
    after with scopes := { scope with opts := savedOptions } :: scopes
  }

private def processCommand : Lean.Elab.Frontend.FrontendM (Bool × Bool) := do
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

private partial def processCommands : Lean.Elab.Frontend.FrontendM Bool := do
  let (terminal, parserHadErrors) ← processCommand
  if terminal then
    return parserHadErrors
  let laterHadErrors ← processCommands
  return parserHadErrors || laterHadErrors

private unsafe def parseSource (env : Environment) (path : System.FilePath)
    (source : String) : IO (Syntax × MessageLog × Bool) := do
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let initialState : Lean.Elab.Frontend.State := {
    commandState := Lean.Elab.Command.mkState env messages
      ExplicitLean.SimpEngine.mathlibIncrementalParserOptions
    parserState
    cmdPos := parserState.pos
  }
  let (parserHadErrors, state) ← (processCommands.run { inputCtx }).run initialState
  let moduleSyntax := mkNode `Lean.Parser.Module.module #[header.raw, mkListNode state.commands]
  return (moduleSyntax, state.commandState.messages, parserHadErrors)

private unsafe def parseSourceFully (module : Name) (path : System.FilePath)
    (source : String) : IO (Syntax × MessageLog × Environment) := do
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  Lean.enableInitializersExecution
  let env ← Lean.importModules (Lean.Elab.HeaderSyntax.imports header) {}
    (loadExts := true)
  let env := env.setMainModule module
  let state ← Lean.Elab.IO.processCommands inputCtx parserState
    (Lean.Elab.Command.mkState env messages ExplicitLean.SimpEngine.mathlibParserOptions)
  let moduleSyntax := mkNode `Lean.Parser.Module.module #[header.raw, mkListNode state.commands]
  return (moduleSyntax, state.commandState.messages, state.commandState.env)

private structure ScopeOccurrence where
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

private structure ScopeDeclaration where
  module : String
  name : String
  startByte : Nat
  endByte : Nat
  selectionStartByte : Nat
  selectionEndByte : Nat
  isProof : Bool
  deriving ToJson

private structure CommandAncestor where
  kind : String
  startByte : Nat
  endByte : Nat

private def isGenericCommandKind (kind : String) : Bool :=
  kind.endsWith ".declValSimple" ||
  kind.endsWith ".declValEqns" ||
  kind.endsWith ".declSig" ||
  kind.endsWith ".declId" ||
  kind.endsWith ".macroTail" ||
  kind.endsWith ".macroRhs"

private def commandAncestor? (stx : Syntax) : Option CommandAncestor := do
  let range ← stx.getRange?
  let kind := stx.getKind.toString
  guard (kind.startsWith "Lean.Parser.Command.")
  guard !isGenericCommandKind kind
  return {
    kind
    startByte := range.start.byteIdx
    endByte := range.stop.byteIdx
  }

private partial def collectOccurrences (file module : String) (fileMap : FileMap)
    (stx : Syntax) (ancestors : Array String := #[])
    (command? : Option CommandAncestor := none)
    (entries : Array ScopeOccurrence := #[]) : Array ScopeOccurrence := Id.run do
  let ancestors := ancestors.push stx.getKind.toString
  let command? := commandAncestor? stx |>.orElse (fun _ => command?)
  let mut entries := entries
  if stx.isOfKind ``Lean.Parser.Tactic.simp then
    if let some range := stx.getRange? then
      let position := fileMap.toPosition range.start
      let commandKind := command?.map (·.kind)
      let commandStartByte := command?.map (·.startByte)
      let commandEndByte := command?.map (·.endByte)
      entries := entries.push {
        module := module
        startByte := range.start.byteIdx
        endByte := range.stop.byteIdx
        line := position.line
        column := position.column
        kind := if stx[3].isNone then "simp" else "simp_only"
        source := String.Pos.Raw.extract fileMap.source range.start range.stop
        ancestors
        commandKind
        commandStartByte
        commandEndByte
      }
  for arg in stx.getArgs do
    entries := collectOccurrences file module fileMap arg ancestors command? entries
  return entries

private def declarationByteRange (fileMap : FileMap) (range : DeclarationRange) :
    (Nat × Nat) :=
  ((fileMap.ofPosition range.pos).byteIdx, (fileMap.ofPosition range.endPos).byteIdx)

private unsafe def declarationRecords (env : Environment) (module : Name)
    (fileMap : FileMap) : IO (Array ScopeDeclaration) := do
  let mut result : Array ScopeDeclaration := #[]
  let entries := if let some moduleIndex := env.getModuleIdx? module then
      let serverEntries := declRangeExt.toPersistentEnvExtension.getModuleEntries env
        moduleIndex (level := .server)
      if serverEntries.isEmpty then
        declRangeExt.toPersistentEnvExtension.getModuleEntries env moduleIndex
          (level := .exported)
      else
        serverEntries
    else
      -- A full fallback elaborates the requested source as the current module,
      -- so its declaration ranges live in the extension's local state rather
      -- than in an imported module slot.
      declRangeExt.toPersistentEnvExtension.getState (asyncMode := .local) env |>.toArray
  for (name, ranges) in entries do
    let some info := env.find? name
      | continue
    let (startByte, endByte) := declarationByteRange fileMap ranges.range
    let (selectionStartByte, selectionEndByte) :=
      declarationByteRange fileMap ranges.selectionRange
    let isProof ← PPContext.runMetaM {
      env := env
      opts := {}
      currNamespace := Name.anonymous
      openDecls := []
    } (Meta.isProp info.type)
    result := result.push {
      module := module.toString
      name := name.toString
      startByte
      endByte
      selectionStartByte
      selectionEndByte
      isProof
    }
  return result

private unsafe def emitFile (env? : Option Environment) (module : Name)
    (path : System.FilePath) (deferFullFallback fullFallbackOnly : Bool) : IO UInt32 := do
  let source ← IO.FS.readFile path
  let fileMap := FileMap.ofString source
  try
    let finish (env : Environment) (moduleSyntax : Syntax) (messages : MessageLog) : IO UInt32 := do
      if messages.hasErrors then
        IO.eprintln s!"scope classifier parser errors in {path}"
        for message in messages.toArray do
          if message.severity == .error then
            IO.eprintln s!"{message.pos.line}:{message.pos.column}: {← message.data.toString}"
        return 1
      let occurrences := collectOccurrences path.toString module.toString fileMap moduleSyntax
      for occurrence in occurrences do
        IO.println s!"SIMP_ENGINE_SCOPE_OCCURRENCE {(toJson occurrence).compress}"
      let declarations ← declarationRecords env module fileMap
      for declaration in declarations do
        IO.println s!"SIMP_ENGINE_SCOPE_DECLARATION {(toJson declaration).compress}"
      return 0
    if fullFallbackOnly then
      IO.println s!"SIMP_ENGINE_SCOPE_FULL_FALLBACK module={module} file={path}"
      let (moduleSyntax, messages, env) ← parseSourceFully module path source
      return ← finish env moduleSyntax messages
    let some env := env?
      | throw <| IO.Error.userError "scope fast parser is missing its aggregate environment"
    let (fastSyntax, fastMessages, fastParserHadErrors) ← parseSource env path source
    if fastParserHadErrors || fastMessages.hasErrors then
      if deferFullFallback then
        IO.println s!"SIMP_ENGINE_SCOPE_DEFERRED_FALLBACK module={module} file={path}"
        return 0
      IO.println s!"SIMP_ENGINE_SCOPE_FULL_FALLBACK module={module} file={path}"
      let (moduleSyntax, messages, fullEnv) ← parseSourceFully module path source
      return ← finish fullEnv moduleSyntax messages
    else
      return ← finish env fastSyntax fastMessages
  catch error =>
    IO.eprintln s!"scope classifier failed for {module} ({path}): {error}"
    return 1

private def parsePairs : List String → Except String (Array (Name × System.FilePath))
  | [] => .ok #[]
  | module :: path :: rest => do
      if module.isEmpty || path.isEmpty then
        throw "scope classifier module and source path must be nonempty"
      let pairs ← parsePairs rest
      return pairs.push (module.toName, System.FilePath.mk path)
  | _ => throw "scope classifier expects <module-name> <source-path> pairs"

unsafe def scopeMain (args : List String) : IO UInt32 := do
  let deferFullFallback := args.contains "--defer-full-fallback"
  let fullFallbackOnly := args.contains "--full-fallback-only"
  if deferFullFallback && fullFallbackOnly then
    IO.eprintln "scope fallback modes are mutually exclusive"
    return 2
  let pairArgs := args.filter fun arg =>
    arg != "--defer-full-fallback" && arg != "--full-fallback-only"
  let pairs ← match parsePairs pairArgs with
    | .ok pairs =>
      if pairs.isEmpty then
        IO.eprintln "usage: SimpEngineBoundaryScope.lean [--defer-full-fallback | --full-fallback-only] <module-name> <source-path> ..."
        return 2
      pure pairs
    | .error message =>
      IO.eprintln message
      return 2
  if fullFallbackOnly && pairs.size != 1 then
    IO.eprintln "scope full fallback mode requires exactly one module/source pair"
    return 2
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  -- Match the syntax inventory's parser environment exactly for Mathlib
  -- sources. The controlled fixture defines a custom tactic token, so parse it
  -- in a separate environment instead of adding that grammar to Mathlib files.
  let mathlibEnv? ← if fullFallbackOnly then
      pure none
    else
      some <$> Lean.importModules #[{ module := `Mathlib }] {} (loadExts := true)
  let fixtureModule := `ExplicitLean.SimpEngine.Boundary.ScopeFixture
  let fixtureEnv? ← if !fullFallbackOnly && pairs.any (fun pair => pair.1 == fixtureModule) then
      Lean.enableInitializersExecution
      some <$> Lean.importModules #[
        { module := `Mathlib },
        { module := fixtureModule }
      ] {} (loadExts := true)
    else
      pure none
  let mut status := 0
  for (module, path) in pairs do
    let env? := if module == fixtureModule then fixtureEnv? else mathlibEnv?
    let moduleExists ← if fullFallbackOnly then
        try
          let _ ← Lean.findOLean module
          pure true
        catch _ => pure false
      else
        pure <| env?.any fun env => (env.getModuleIdx? module).isSome
    if !moduleExists then
      IO.eprintln s!"scope classifier module is not present in the pinned environment: {module}"
      status := 1
    else
      let code ← emitFile env? module path deferFullFallback fullFallbackOnly
      if code != 0 then
        status := code
  return status

end ExplicitLean.SimpEngine.BoundaryScope

unsafe def main (args : List String) : IO UInt32 :=
  ExplicitLean.SimpEngine.BoundaryScope.scopeMain args
