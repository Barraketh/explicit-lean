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
    let mut details := #[]
    for message in state.commandState.messages.toList do
      if message.severity == .error then
        let text ← message.data.toString
        details := details.push <|
          s!"{message.fileName}:{message.pos.line}:{message.pos.column}: {text}"
    throw <| IO.Error.userError <| "Lean module parser reported an error or recovery" ++
      (if details.isEmpty then "" else ":\n" ++ String.intercalate "\n" details.toList)
  return (commands, state.commandState.messages)

private def rangeOf (stx : Syntax) : Option (Nat × Nat) := do
  let start ← stx.getPos? (canonicalOnly := true)
  let stop ← stx.getTailPos? (canonicalOnly := true)
  if start.byteIdx >= stop.byteIdx then none else some (start.byteIdx, stop.byteIdx)

private def kindString (stx : Syntax) : String := stx.getKind.toString

private partial def hasIdentifier (stx : Syntax) (name : String) : Bool :=
  match stx with
  | .ident _ value _ _ => value.toString == name
  | _ => stx.getArgs.any (fun child => hasIdentifier child name)

private def directCategoryAfterColon (stx : Syntax) : Option String := Id.run do
  let args := stx.getArgs
  for index in [:args.size] do
    let isColon := match args[index]! with
      | .atom _ value => value == ":"
      | _ => false
    if isColon then
      if let some next := args[index + 1]? then
        if let .ident _ value _ _ := next then return some value.toString
  return none

private partial def hasTermCategoryAfterColon (stx : Syntax) : Bool := Id.run do
  if directCategoryAfterColon stx == some "term" then return true
  for child in stx.getArgs do
    if hasTermCategoryAfterColon child then return true
  return false

private def termElaborationRisk (command : Syntax) : Option String := Id.run do
  let kind := kindString command
  -- These are command AST nodes, not source-text matches.  The category
  -- identifier is part of the parsed declaration (or, for macro_rules, the
  -- quoted term pattern).  Refuse rather than trying to execute/elaborate a
  -- source-local extension while recording another term.
  if kind == "Lean.Parser.Command.syntax" then
    if hasTermCategoryAfterColon command then return some "source_term_syntax"
  -- Notation/mixfix declarations introduce ordinary term syntax through
  -- elaborator extensions; their AST category is not always explicit in the
  -- declaration (e.g. inferred term notation), so fail closed on the parsed
  -- command kind rather than infer it from source spelling.
  if command.isOfKind ``Lean.Parser.Command.«notation» ||
      command.isOfKind ``Lean.Parser.Command.«mixfix» ||
      command.isOfKind `Lean.Parser.Command.mixfix then
    return some "source_term_notation"
  if kind == "Lean.Parser.Command.macro" || kind == "Lean.Parser.Command.elab" ||
      kind == "Lean.Parser.Command.elab_rules" then
    if hasTermCategoryAfterColon command then
      return some "source_term_macro_or_elaborator"
  if kind == "Lean.Parser.Command.macro_rules" && hasIdentifier command "term" then
    return some "source_term_macro_rules"
  -- A declaration tagged [term_elab ...] can run arbitrary MetaM during
  -- ordinary term elaboration, including Lean.Meta.Simp.  This structural
  -- attribute check intentionally fails closed even if the declaration body
  -- is opaque to this inventory.
  if (kind == "Lean.Parser.Command.declaration" ||
      kind == "Lean.Parser.Command.attribute") && hasIdentifier command "term_elab" then
    return some "source_term_elab_attribute"
  -- Initializers and run_cmd can register term elaborators through APIs
  -- instead of the surface `elab`/attribute commands.  Their bodies are code,
  -- not a declarative syntax tree that this parser-only gate can safely
  -- evaluate, so neither is executed; both fail closed as extension-capable.
  if kind == "Lean.Parser.Command.initialize" ||
      kind == "Lean.Parser.Command.builtin_initialize" ||
      kind == "Lean.Parser.Command.runCmd" || kind == "Lean.runCmd" then
    return some "source_command_can_register_term_extension"
  return none

private partial def inventoryTermElaborationRisks (stx : Syntax) : Array Json := Id.run do
  let mut risks := #[]
  if let some reason := termElaborationRisk stx then
    let rangeFields := match rangeOf stx with
      | some (start, stop) => [
          ("startByte", toJson start), ("endByte", toJson stop)]
      | none => []
    risks := risks.push <| Json.mkObj <| [
      ("kind", toJson (kindString stx)), ("reason", toJson reason)] ++ rangeFields
  for child in stx.getArgs do
    risks := risks ++ inventoryTermElaborationRisks child
  return risks

private def termElaborationInventoryJson (moduleName : String)
    (commands : Array Syntax) : Json := Id.run do
  let mut risks := #[]
  for command in commands do
    risks := risks ++ inventoryTermElaborationRisks command
  return Json.mkObj [
    ("module", toJson moduleName),
    ("status", toJson (if risks.isEmpty then "ok" else "refused")),
    ("reason", toJson (if risks.isEmpty then "no_source_term_extensions" else "source_local_term_extension")),
    ("risks", Json.arr risks)]

private partial def executableProofHoleTokens (stx : Syntax) : Array Json := Id.run do
  let proofHole := stx.isOfKind ``Lean.Parser.Term.sorry ||
    (match stx with
     | .ident _ value _ _ => value.toString == "admit"
     | _ => false)
  let mut found := #[]
  if proofHole then
    let token := match stx with
      | .ident _ value _ _ => value.toString
      | _ => "sorry"
    let rangeFields := match rangeOf stx with
      | some (start, stop) => [
          ("startByte", toJson start), ("endByte", toJson stop)]
      | none => []
    found := found.push <| Json.mkObj <| [
      ("token", toJson token), ("kind", toJson (kindString stx))] ++ rangeFields
  for child in stx.getArgs do
    found := found ++ executableProofHoleTokens child
  return found

private def proofHoleAuditJson (moduleName : String) (commands : Array Syntax) : Json := Id.run do
  let mut holes := #[]
  for command in commands do
    holes := holes ++ executableProofHoleTokens command
  return Json.mkObj [
    ("module", toJson moduleName),
    ("status", toJson (if holes.isEmpty then "ok" else "refused")),
    ("reason", toJson (if holes.isEmpty then "no_executable_proof_holes" else "executable_proof_hole_token")),
    ("proofHoles", Json.arr holes)]

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

private partial def debugSyntax (stx : Syntax) : Json := Id.run do
  let mut fields := [("kind", toJson (kindString stx))]
  match stx with
  | .atom _ value => fields := fields ++ [("token", toJson value)]
  | .ident _ value _ _ => fields := fields ++ [("token", toJson value.toString)]
  | _ => pure ()
  if !stx.getArgs.isEmpty then
    fields := fields ++ [("args", Json.arr (stx.getArgs.map debugSyntax))]
  return Json.mkObj fields

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

private partial def collectSimpSites (stx : Syntax) : Array Syntax := Id.run do
  let mut sites := if isSimpSiteNode stx then #[stx] else #[]
  for child in stx.getArgs do
    sites := sites ++ collectSimpSites child
  return sites

private def simpSyntaxInventoryJson (moduleName : String)
    (commands : Array Syntax) : Json := Id.run do
  let mut entries := #[]
  let mut refused := #[]
  for commandIndex in [:commands.size] do
    let command := commands[commandIndex]!
    let commandRange := rangeOf command
    let mut sites := #[]
    for site in collectSimpSites command do
      match rangeOf site, commandRange with
      | some (start, stop), some (commandStart, commandStop) =>
        if commandStart <= start && stop <= commandStop then
          sites := sites.push <| jsonRange site
        else
          refused := refused.push <| Json.mkObj [
            ("commandOrdinal", toJson commandIndex),
            ("reason", toJson "simp_site_outside_command_range"),
            ("site", jsonRange site),
            ("command", jsonRange command)]
      | _, _ =>
        refused := refused.push <| Json.mkObj [
          ("commandOrdinal", toJson commandIndex),
          ("reason", toJson "simp_site_or_command_without_source_range"),
          ("site", jsonRange site),
          ("command", jsonRange command)]
    let fields := match commandRange with
      | some (start, stop) => [
          ("startByte", toJson start), ("endByte", toJson stop)]
      | none => []
    entries := entries.push <| Json.mkObj <| [
      ("commandOrdinal", toJson commandIndex),
      ("kind", toJson (kindString command)),
      ("simpSites", Json.arr sites)] ++ fields
  return Json.mkObj [
    ("module", toJson moduleName),
    ("status", toJson (if refused.isEmpty then "ok" else "refused")),
    ("reason", toJson (if refused.isEmpty then "complete_simp_syntax_inventory" else "incomplete_simp_syntax_inventory")),
    ("refusals", Json.arr refused),
    ("commands", Json.arr entries)]

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
  | moduleName :: path :: "--dump" :: [] => do
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let path := System.FilePath.mk path
    let source ← IO.FS.readFile path
    try
      let (commands, _) ← parseModule path source
      IO.println (Json.arr (commands.map debugSyntax) |>.compress)
      return 0
    catch error =>
      IO.eprintln s!"Lean syntax dump failed for {moduleName}: {error}"
      return 1
  | moduleName :: path :: "--term-elab-gate" :: [] => do
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let path := System.FilePath.mk path
    let source ← IO.FS.readFile path
    try
      let (commands, _) ← parseModule path source
      IO.println (termElaborationInventoryJson moduleName commands |>.compress)
      return 0
    catch error =>
      IO.eprintln s!"Lean term-elaboration gate failed closed for {moduleName}: {error}"
      return 1
  | moduleName :: path :: "--proof-hole-audit" :: [] => do
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let path := System.FilePath.mk path
    let source ← IO.FS.readFile path
    try
      let (commands, _) ← parseModule path source
      IO.println (proofHoleAuditJson moduleName commands |>.compress)
      return 0
    catch error =>
      IO.eprintln s!"Lean proof-hole audit failed closed for {moduleName}: {error}"
      return 1
  | moduleName :: path :: "--simp-inventory" :: [] => do
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let path := System.FilePath.mk path
    let source ← IO.FS.readFile path
    try
      let (commands, _) ← parseModule path source
      IO.println (simpSyntaxInventoryJson moduleName commands |>.compress)
      return 0
    catch error =>
      IO.eprintln s!"Lean simp syntax inventory failed closed for {moduleName}: {error}"
      return 1
  | "--simp-inventory-batch" :: inputArgs => do
    if inputArgs.length % 2 != 0 then
      IO.eprintln "Lean simp syntax inventory batch requires module/path pairs"
      return 1
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let inputs := inputArgs.toArray
    let mut results := #[]
    for pairIndex in [:inputs.size / 2] do
      let moduleName := inputs[pairIndex * 2]!
      let path := System.FilePath.mk inputs[pairIndex * 2 + 1]!
      try
        let source ← IO.FS.readFile path
        let (commands, _) ← parseModule path source
        results := results.push <| simpSyntaxInventoryJson moduleName commands
      catch error =>
        results := results.push <| Json.mkObj [
          ("module", toJson moduleName),
          ("status", toJson "failed"),
          ("reason", toJson error.toString)]
    IO.println (Json.arr results |>.compress)
    return 0
  | moduleName :: path :: rangeArgs => do
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
