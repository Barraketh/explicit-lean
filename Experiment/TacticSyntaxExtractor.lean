import Mathlib.Tactic.ScopedNS
import ExplicitLean.SimpEngine.FrontendOptions
import Lean.Elab.Frontend
import Lean.Elab.Import
import Lean.Parser.Module

open Lean Parser

namespace Experiment.TacticSyntaxExtractor

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
    | throw <| IO.Error.userError "syntax extractor has no command scope"
  let savedOptions := scope.opts
  let options := Lean.Elab.Term.Quotation.quotPrecheck.set savedOptions false
  Lean.Elab.Frontend.setCommandState {
    before with scopes := { scope with opts := options } :: scopes
  }
  Lean.Elab.Frontend.elabCommandAtFrontend command
  let after ← Lean.Elab.Frontend.getCommandState
  let scope :: scopes := after.scopes
    | throw <| IO.Error.userError "syntax extractor lost its command scope"
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

private unsafe def parseModule (path : System.FilePath) (source : String) :
    IO (Array Syntax × MessageLog) := do
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  if headerMessages.hasErrors then
    throw <| IO.Error.userError "Lean module header parser reported an error"
  Lean.enableInitializersExecution
  let (env, messages) ← Lean.Elab.processHeader header
    ExplicitLean.SimpEngine.mathlibParserOptions headerMessages inputCtx
    (mainModule := `TacticSyntaxExtractorFallback)
  let initialState : Lean.Elab.Frontend.State := {
    commandState := Lean.Elab.Command.mkState env messages
      ExplicitLean.SimpEngine.mathlibIncrementalParserOptions
    parserState
    cmdPos := parserState.pos
  }
  let (commands, state) ← (processCommands.run { inputCtx }).run initialState
  if state.commandState.messages.hasErrors then
    throw <| IO.Error.userError "Lean module parser reported an error or recovery"
  return (commands, state.commandState.messages)

private def rangeOf (stx : Syntax) : Option (Nat × Nat) := do
  let start ← stx.getPos? (canonicalOnly := true)
  let stop ← stx.getTailPos? (canonicalOnly := true)
  if start.byteIdx >= stop.byteIdx then none else some (start.byteIdx, stop.byteIdx)

private def kindString (stx : Syntax) : String := stx.getKind.toString

private def jsonRange (stx : Syntax) : Json := Id.run do
  match rangeOf stx with
  | some (start, stop) => return Json.mkObj [
      ("startByte", toJson start), ("endByte", toJson stop),
      ("kind", toJson (kindString stx))]
  | none => return Json.mkObj [("kind", toJson (kindString stx))]

private def isTacticNode (stx : Syntax) : Bool :=
  (kindString stx).startsWith "Lean.Parser.Tactic."

private def isSimpSiteNode (stx : Syntax) : Bool :=
  kindString stx == "Lean.Parser.Tactic.simp"

private def isSeqNode (stx : Syntax) : Bool :=
  kindString stx == "Lean.Parser.Tactic.«tactic_<;>_»"

private partial def findEnclosing (stx : Syntax) (targetStart targetEnd : Nat)
    (ancestors : Array Syntax := #[]) : Array (Array Syntax) := Id.run do
  let some (start, stop) := rangeOf stx | return #[]
  if start > targetStart || stop < targetEnd then return #[]
  let next := if isTacticNode stx then ancestors.push stx else ancestors
  let mut results := #[]
  if start == targetStart && stop == targetEnd && isSimpSiteNode stx then
    results := results.push next
  for child in stx.getArgs do
    results := results ++ findEnclosing child targetStart targetEnd next
  return results

private def rawChildren (stx : Syntax) : Json := Id.run do
  let children := stx.getArgs.map fun child =>
    match child with
    | .node .. => jsonRange child
    | .atom .. => jsonRange child
    | .ident .. => jsonRange child
    | .missing => Json.mkObj [("kind", toJson "missing")]
  return Json.arr children

private def tacticAncestryJson (ancestry : Array Syntax)
    (targetStart targetEnd : Nat) : Json := Id.run do
  let nodes := ancestry.map fun stx =>
    let fields := match rangeOf stx with
      | some (start, stop) => [
          ("kind", toJson (kindString stx)),
          ("startByte", toJson start), ("endByte", toJson stop)]
      | none => [("kind", toJson (kindString stx))]
    let seqFields := if isSeqNode stx then
      let tacticChildren := stx.getArgs.filter fun child =>
        match child with
        | .node .. => true
        | .ident .. => true
        | .atom .. | .missing => false
      let labeled := tacticChildren.mapIdx fun index child =>
        let childContainsTarget := match rangeOf child with
          | some (start, stop) => start <= targetStart && stop >= targetEnd
          | none => false
        let role := if index == 0 then "left"
          else if index == 1 && childContainsTarget then "right"
          else "continuation"
        Json.mkObj [
          ("role", toJson role),
          ("startByte", toJson ((rangeOf child).map Prod.fst |>.getD 0)),
          ("endByte", toJson ((rangeOf child).map Prod.snd |>.getD 0)),
          ("kind", toJson (kindString child))]
      [("children", rawChildren stx), ("branchChildren", Json.arr labeled)]
      else []
    Json.mkObj <| fields ++ seqFields
  return Json.arr nodes

private partial def findSyntax (stx : Syntax) (targetStart targetEnd : Nat) :
    Array (Array Syntax) :=
  findEnclosing stx targetStart targetEnd

private def extractRange (moduleName : String) (commands : Array Syntax)
    (targetStart targetEnd : Nat) : Json := Id.run do
  let mut candidates := #[]
  for command in commands do
    candidates := candidates ++ findSyntax command targetStart targetEnd
  if candidates.size != 1 then
    return Json.mkObj [
      ("module", toJson moduleName),
      ("status", toJson "refused"),
      ("reason", toJson (if candidates.isEmpty then "non_tactic_or_unmatched_range" else "ambiguous_range")),
      ("matchCount", toJson candidates.size)]
  let ancestry := candidates[0]!
  let some target := ancestry.back? | return Json.mkObj [("status", toJson "refused"), ("reason", toJson "empty_tactic_ancestry")]
  return Json.mkObj [
    ("module", toJson moduleName),
    ("status", toJson "ok"),
    ("target", jsonRange target),
    ("ancestry", tacticAncestryJson ancestry targetStart targetEnd),
    ("targetStartByte", toJson targetStart),
    ("targetEndByte", toJson targetEnd)]

unsafe def runArgs (args : List String) : IO UInt32 := do
  match args with
  | moduleName :: path :: rangeArgs =>
    if rangeArgs.isEmpty || rangeArgs.length % 2 != 0 then return 2
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let path := System.FilePath.mk path
    let source ← IO.FS.readFile path
    try
      let (commands, _) ← parseModule path source
      let mut results := #[]
      let mut remaining := rangeArgs
      while !remaining.isEmpty do
        let some start := remaining[0]!.toNat? | return 2
        let some stop := remaining[1]!.toNat? | return 2
        results := results.push <| extractRange moduleName commands start stop
        remaining := remaining.drop 2
      IO.println (Json.arr results |>.compress)
      return 0
    catch error =>
      IO.eprintln s!"Lean syntax extraction failed for {moduleName}: {error}"
      return 1
  | _ =>
    IO.eprintln "usage: tacticSyntaxExtractor <module-name> <source-path> <start-byte> <end-byte> [<start-byte> <end-byte> ...]"
    return 2

end Experiment.TacticSyntaxExtractor

unsafe def main (args : List String) : IO UInt32 :=
  Experiment.TacticSyntaxExtractor.runArgs args
