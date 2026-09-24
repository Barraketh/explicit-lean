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
    IO (Array Syntax × MessageLog × Environment) := do
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
  return (commands, state.commandState.messages, state.commandState.env)

private def rangeOf (stx : Syntax) : Option (Nat × Nat) := do
  let start ← stx.getPos? (canonicalOnly := true)
  let stop ← stx.getTailPos? (canonicalOnly := true)
  if start.byteIdx >= stop.byteIdx then none else some (start.byteIdx, stop.byteIdx)

private def kindString (stx : Syntax) : String := stx.getKind.toString

private partial def hasIdentifier (stx : Syntax) (name : String) : Bool :=
  match stx with
  | .ident _ value _ _ =>
    let value := value.toString
    value == name || value.endsWith ("." ++ name)
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

private partial def categoryAfterColon? (stx : Syntax) : Option String := Id.run do
  if let some category := directCategoryAfterColon stx then return some category
  for child in stx.getArgs do
    if let some category := categoryAfterColon? child then return some category
  return none

private partial def hasTermCategoryAfterColon (stx : Syntax) : Bool := Id.run do
  if directCategoryAfterColon stx == some "term" then return true
  for child in stx.getArgs do
    if hasTermCategoryAfterColon child then return true
  return false

private def sourceAttributeName? (stx : Syntax) : Option Name := Id.run do
  -- `macro` has a dedicated attribute parser; other extension-point
  -- attributes use `Attr.simple` and carry their resolved name as the first
  -- identifier. Do not search arbitrary identifiers in declaration bodies.
  if kindString stx == "Lean.Parser.Attr.macro" then return some `macro
  if kindString stx != "Lean.Parser.Attr.simple" then return none
  let first : Option Syntax := stx.getArgs[0]?
  match first with
  | some ident =>
    match ident with
    | Syntax.ident _ _ value _ => return some value
    | _ => return none
  | _ => return none

private def sourceExtensionAttributeReason? (env : Environment) (name : Name) :
    Option String := Id.run do
  match Lean.getAttributeImpl env name with
  | .error _ => return none
  | .ok attributeImpl =>
    let descr := attributeImpl.descr
    -- Some built-in elaboration attributes are registered by specialized
    -- tables rather than through `mkElabAttribute`, so classify their parsed
    -- names only after confirming this exact root attribute is registered.
    -- Aliases are recognized by the implementation description below; do
    -- not confuse a namespaced user attribute with the same leaf name.
    match name with
    | `term_elab => return some "source_term_elab_attribute"
    | `builtin_term_elab => return some "source_term_elab_attribute"
    | `command_elab => return some "source_command_elab_attribute"
    | `builtin_command_elab => return some "source_command_elab_attribute"
    | `tactic => return some "source_tactic_elab_attribute"
    | `builtin_tactic => return some "source_tactic_elab_attribute"
    | `macro => return some "source_macro_attribute"
    | `builtin_macro => return some "source_macro_attribute"
    | `doElem_elab => return some "source_do_elab_attribute"
    | `builtin_doElem_elab => return some "source_do_elab_attribute"
    | `inductive_elab => return some "source_inductive_elab_attribute"
    | `builtin_inductive_elab => return some "source_inductive_elab_attribute"
    | `grind_tactic => return some "source_grind_tactic_attribute"
    | `builtin_grind_tactic => return some "source_grind_tactic_attribute"
    | `try_tactic => return some "source_try_tactic_attribute"
    | `builtin_try_tactic => return some "source_try_tactic_attribute"
    | `sym_simproc => return some "source_sym_simproc_attribute"
    | `builtin_sym_simproc => return some "source_sym_simproc_attribute"
    | `sym_discharger => return some "source_sym_discharger_attribute"
    | `builtin_sym_discharger => return some "source_sym_discharger_attribute"
    | `sym_dsimproc => return some "source_sym_dsimproc_attribute"
    | `builtin_sym_dsimproc => return some "source_sym_dsimproc_attribute"
    | `doElem_control_info => return some "source_do_control_info_attribute"
    | `builtin_doElem_control_info => return some "source_do_control_info_attribute"
    | `quot_precheck => return some "source_quotation_precheck_attribute"
    | `builtin_quot_precheck => return some "source_quotation_precheck_attribute"
    | `try_suggestion => return some "source_try_suggestion_attribute"
    | _ => pure ()
    -- Attribute descriptions are supplied by Lean's registered extension
    -- implementation. They catch fully-qualified spellings and aliases of
    -- the built-in keyed elaborator attributes without relying on suffixes in
    -- source identifiers.
    if descr == "parser" || descr == "Builtin parser" then
      return some "source_parser_attribute"
    if descr.contains "parser attributes" && descr.contains "hooks" then
      return some "source_parser_attribute_hook"
    if descr.endsWith " elaborator" || descr.startsWith "Register an elaborator for " then
      return some "source_elaborator_attribute"
    if descr.contains "control info inference" then return some "source_do_control_info_attribute"
    if descr.contains "quotation pre-check" then return some "source_quotation_precheck_attribute"
    if descr.contains "tactic suggestion generator" then return some "source_try_suggestion_attribute"
  return none

private partial def findSourceExtensionAttribute? (env : Environment) (stx : Syntax) :
    Option (String × String) := Id.run do
  -- Quoted attributes are data, not active extension registrations. The
  -- generated AST for a syntax quotation contains Attr.simple nodes, so stop
  -- at the quote boundary instead of misclassifying examples or stored ASTs.
  if kindString stx == "Lean.Parser.Term.dynamicQuot" then return none
  if let some name := sourceAttributeName? stx then
    if let some reason := sourceExtensionAttributeReason? env name then
      return some (name.toString, reason)
  for child in stx.getArgs do
    if let some result := findSourceExtensionAttribute? env child then return some result
  return none

private def sourceExtensionAttribute? (env : Environment) (command : Syntax) :
    Option (String × String) := Id.run do
  if kindString command != "Lean.Parser.Command.declaration" &&
      kindString command != "Lean.Parser.Command.attribute" then
    return none
  findSourceExtensionAttribute? env command

private def termElaborationRisk (env : Environment) (command : Syntax) : Option String := Id.run do
  let kind := kindString command
  -- These are command AST nodes, not source-text matches.  Refuse rather than
  -- executing or recompiling source-local extension code while recording a
  -- replacement.  A command macro/elaborator may run Meta.Simp even though the
  -- target proof itself contains no term-level extension.
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
    -- `command`, `tactic`, and other categories are executable extension
    -- points too.  Their callbacks run when a candidate module is fully
    -- recompiled, so category-independent refusal is required here.
    match categoryAfterColon? command with
    | some category => return some s!"source_{category}_macro_or_elaborator"
    | none => return some "source_macro_or_elaborator_unknown_category"
  if kind == "Lean.Parser.Command.macro_rules" then
    -- A macro rule's category is encoded in quoted syntax patterns and can
    -- be any imported or user-defined category.  Keep the old term-specific
    -- diagnostic label where applicable; every category is refused.
    if hasIdentifier command "term" then return some "source_term_macro_rules"
    return some "source_macro_rules_any_category"
  if let some (_, reason) := sourceExtensionAttribute? env command then
    return some reason
  -- Initializers and run_cmd can register executable parser/elaboration
  -- callbacks through APIs instead of the surface `elab`/attribute commands.
  -- Their bodies are code, not a declarative syntax tree that this parser-only
  -- gate can safely evaluate, so neither is executed; both fail closed.
  if kind == "Lean.Parser.Command.initialize" ||
      kind == "Lean.Parser.Command.builtin_initialize" ||
      kind == "Lean.Parser.Command.runCmd" || kind == "Lean.runCmd" then
    return some "source_command_can_register_term_extension"
  return none

private partial def inventoryTermElaborationRisks (env : Environment) (stx : Syntax) : Array Json := Id.run do
  if kindString stx == "Lean.Parser.Term.dynamicQuot" then return #[]
  let mut risks := #[]
  if let some reason := termElaborationRisk env stx then
    let rangeFields := match rangeOf stx with
      | some (start, stop) => [
          ("startByte", toJson start), ("endByte", toJson stop)]
      | none => []
    let categoryBearingKind := kindString stx == "Lean.Parser.Command.syntax" ||
      kindString stx == "Lean.Parser.Command.macro" ||
      kindString stx == "Lean.Parser.Command.elab" ||
      kindString stx == "Lean.Parser.Command.elab_rules"
    let categoryFields := if categoryBearingKind then
      match categoryAfterColon? stx with
      | some category => [("category", toJson category)]
      | none => []
    else []
    let attributeFields := match sourceExtensionAttribute? env stx with
      | some (attributeName, _) => [("attribute", toJson attributeName)]
      | none => []
    risks := risks.push <| Json.mkObj <| [
      ("kind", toJson (kindString stx)), ("reason", toJson reason)] ++
      categoryFields ++ attributeFields ++ rangeFields
  for child in stx.getArgs do
    risks := risks ++ inventoryTermElaborationRisks env child
  return risks

private def termElaborationInventoryJson (moduleName : String) (env : Environment)
    (commands : Array Syntax) : Json := Id.run do
  let mut risks := #[]
  for command in commands do
    risks := risks ++ inventoryTermElaborationRisks env command
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

private def declValBody? (parent : Syntax) : Option (Syntax × String) := Id.run do
  for child in parent.getArgs do
    if kindString child == "Lean.Parser.Command.declValSimple" then
      if let some body := child.getArgs[1]? then return some (body, "term")
    if kindString child == "Lean.Parser.Command.whereStructInst" then
      return some (child, "whereStructInst")
  return none

private def theoremBody? (command : Syntax) : Option (Syntax × String) := Id.run do
  -- A parsed theorem/lemma declaration has a direct `Command.theorem` child;
  -- its `declValSimple` child owns the exact proof term after the declaration
  -- separator.  Restrict the lookup to these direct parser nodes so `:=` in a
  -- declaration type, named argument, quotation, or proof-local `have` can
  -- never be mistaken for the declaration body.
  -- Mathlib's `lemma` command is a command macro whose parsed root kind is
  -- literally `lemma`; its direct `group` child has the same declId/declSig/
  -- declValSimple layout as Lean's built-in theorem command.
  if kindString command == "lemma" then
    for child in command.getArgs do
      if kindString child == "group" then
        if let some body := declValBody? child then return some body
    return none
  let mut theorem? : Option Syntax := none
  for child in command.getArgs do
    if kindString child == "Lean.Parser.Command.theorem" then
      theorem? := some child
  let some theoremStx := theorem? | return none
  return declValBody? theoremStx

private def simpSyntaxInventoryJson (moduleName requestId : String)
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
    let theoremBodyFields := match theoremBody? command with
      | some (body, form) => [
          ("theoremBody", jsonRange body), ("theoremBodyForm", toJson form)]
      | none => []
    entries := entries.push <| Json.mkObj <| [
      ("commandOrdinal", toJson commandIndex),
      ("kind", toJson (kindString command)),
      ("simpSites", Json.arr sites)] ++ fields ++ theoremBodyFields
  return Json.mkObj [
    ("module", toJson moduleName),
    ("requestId", toJson requestId),
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
      let (commands, _, _) ← parseModule path source
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
      let (commands, _, env) ← parseModule path source
      IO.println (termElaborationInventoryJson moduleName env commands |>.compress)
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
      let (commands, _, _) ← parseModule path source
      IO.println (proofHoleAuditJson moduleName commands |>.compress)
      return 0
    catch error =>
      IO.eprintln s!"Lean proof-hole audit failed closed for {moduleName}: {error}"
      return 1
  | moduleName :: path :: requestId :: "--simp-inventory" :: [] => do
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let path := System.FilePath.mk path
    let source ← IO.FS.readFile path
    try
      let (commands, _, _) ← parseModule path source
      IO.println (simpSyntaxInventoryJson moduleName requestId commands |>.compress)
      return 0
    catch error =>
      IO.eprintln s!"Lean simp syntax inventory failed closed for {moduleName}: {error}"
      return 1
  | "--simp-inventory-batch" :: inputArgs => do
    if inputArgs.length % 3 != 0 then
      IO.eprintln "Lean simp syntax inventory batch requires module/path/requestId triples"
      return 1
    Lean.initSearchPath (← Lean.findSysroot)
    Lean.enableInitializersExecution
    let inputs := inputArgs.toArray
    let mut results := #[]
    for pairIndex in [:inputs.size / 3] do
      let moduleName := inputs[pairIndex * 3]!
      let path := System.FilePath.mk inputs[pairIndex * 3 + 1]!
      let requestId := inputs[pairIndex * 3 + 2]!
      try
        let source ← IO.FS.readFile path
        let (commands, _, _) ← parseModule path source
        results := results.push <| simpSyntaxInventoryJson moduleName requestId commands
      catch error =>
        results := results.push <| Json.mkObj [
          ("module", toJson moduleName),
          ("requestId", toJson requestId),
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
      let (commands, _, _) ← parseModule path source
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
