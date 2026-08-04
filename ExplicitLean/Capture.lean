import Lean
import ExplicitLean.Json
import ExplicitLean.Diagnostic
import ExplicitLean.Paths

/-!
# Stock capture

Observes one source elaboration through the pinned stock frontend, per
[CAPTURE.md](../CAPTURE.md).

Architecture version 1 processes one source module per process (C1). The
frontend parses, macro-expands, and elaborates the source exactly once;
capture never reruns a macro, elaborator, tactic, or search to recover missing
information. Asynchronous elaboration is disabled and every frontend task is
awaited before extraction (C8).

This module owns only the observation. The internal representation it produces
is implementer-owned (C3) and deliberately holds Lean values such as `Syntax`,
`Environment`, and `Expr` rather than a serialized projection; stabilization
into manifest identities happens later.
-/

open Lean

namespace ExplicitLean

/-- The capture architecture version implemented here, recorded in the manifest
header as `captureArchitecture`. -/
def captureArchitecture : Nat := 1

/-- One captured top-level command.

The environment fields bracket the command so that a command-local delta can be
computed by comparing them (C2). The pre-command environment of the first
command is the imported baseline. -/
structure CapturedCommand where
  /-- Zero-based position of this command in source order. -/
  ordinal : Nat
  /-- The parsed command syntax. -/
  stx : Syntax
  /-- Half-open byte range of the command in the exact source bytes, when it has
  a meaningful range. -/
  range : Option (Nat × Nat)
  /-- Environment immediately before the command. -/
  envBefore : Environment
  /-- Environment immediately after the command. -/
  envAfter : Environment
  /-- Command state immediately after the command, carrying scopes, options,
  namespace, and open declarations. -/
  stateAfter : Elab.Command.State
  /-- The command's complete information tree, when one was produced. -/
  infoTree : Option Elab.InfoTree
  /-- Messages produced by the command. -/
  messages : MessageLog
  /-- Names of constants present after this command and absent before it,
  sorted by name.

  The traversal order of the underlying map is not a stable identity (C3), so
  this is sorted into a canonical order rather than left in encounter order.
  Source-relevant ordering is recovered later from syntax and dependencies,
  which is what the L2 declaration-order algorithm consumes. -/
  newConstants : Array Name

/-- Everything observed from one source module. -/
structure CapturedModule where
  /-- The source module's name. -/
  module : ModuleName
  /-- Exact source bytes as elaborated. -/
  source : String
  /-- Slash-separated package-relative path of the source file. -/
  path : String
  /-- The environment produced by the header alone: the imported baseline
  against which the module delta is computed (C2). -/
  baseline : Environment
  /-- Header syntax, carrying the module's imports. -/
  header : Syntax
  /-- Top-level commands in source order. -/
  commands : Array CapturedCommand
  /-- Final environment after the last command. -/
  finalEnv : Environment

/-- Half-open byte range of `stx` in the source, when it has one.

Lean's `String.Pos` offsets are already UTF-8 byte offsets into the source, which
is what M2 spans require. -/
def syntaxRange (stx : Syntax) : Option (Nat × Nat) :=
  match stx.getPos? true, stx.getTailPos? true with
  | some s, some e => some (s.byteIdx, e.byteIdx)
  | _, _ => none

private def diagnosticAt (phase : Phase) (code message : String)
    (range : Option (Nat × Nat) := none) (file : String := "") : Diagnostic :=
  { code, message, phase
    span := match range with
      | some (s, e) => some { file, startByte := s, endByte := e }
      | none => none }

/-- A failure of the source itself to parse or elaborate. This is exit status
`3`, distinct from a failure of capture to observe a successful elaboration. -/
private def sourceError (code message : String) (range : Option (Nat × Nat) := none)
    (file : String := "") : Diagnostic :=
  diagnosticAt .source code message range file

/-- A failure to observe or extract from an elaboration that itself succeeded. -/
private def captureError (code message : String) (range : Option (Nat × Nat) := none)
    (file : String := "") : Diagnostic :=
  diagnosticAt .capture code message range file

/-- Options forced for capture.

`Elab.async` is disabled so that commands elaborate in source order and every
result is available without racing (C1, C8). `internal.cmdlineSnapshots` must
stay off: it discards the per-command snapshot metadata that capture exists to
read.

Only the `cmdlineSnapshots` setting is covered by a test that fails when it
changes. Enabling `Elab.async` does not by itself make the fixtures fail, since
the whole point of the setting is to remove a scheduling-dependent failure that
would otherwise appear only intermittently. It is set here because C1 and C8
require it, not because a test would notice its absence. -/
def captureOptions : Options :=
  let opts : Options := {}
  let opts := Elab.async.set opts false
  let opts := Lean.internal.cmdlineSnapshots.set opts false
  opts

/-- Compare two names for a canonical sort.

Names are compared by their component strings from root to leaf, matching the
ordering M2 specifies for serialized names. -/
def nameLt (a b : Name) : Bool :=
  go a.componentsRev.reverse b.componentsRev.reverse
where
  go : List Name → List Name → Bool
    | [], [] => false
    -- A proper prefix sorts before the longer name.
    | [], _ :: _ => true
    | _ :: _, [] => false
    | x :: xs, y :: ys =>
      match x, y with
      | .str _ sx, .str _ sy =>
        if sx == sy then go xs ys else CJson.utf8Lt sx sy
      | .num _ nx, .num _ ny =>
        if nx == ny then go xs ys else nx < ny
      -- A string component sorts before a numeric one, so that mixed names have
      -- a total order that does not depend on the traversal that produced them.
      | .str _ _, .num _ _ => true
      | .num _ _, .str _ _ => false
      | _, _ => false

/-- Constants present in `after` and absent from `before`, sorted by name.

Only the local layer (`map₂`) is examined: imported constants live in the
imported layer and cannot be added by a command. -/
def newConstantsBetween (before after : Environment) : Array Name :=
  let news : Array Name := after.constants.map₂.foldl (init := #[]) fun acc n _ =>
    if before.constants.map₂.contains n then acc else acc.push n
  news.qsort nameLt

/-- Walk the command chain in source order, pairing each command with the
environment before and after it.

Every snapshot task is forced with `.get`, so this returns only after all
frontend work for the module is finished (C8). -/
private partial def collectCommands
    (snap : Language.Lean.CommandParsedSnapshot) (envBefore : Environment) (ordinal : Nat)
    (acc : Array CapturedCommand) : Array CapturedCommand :=
  let stateAfter := snap.elabSnap.resultSnap.get.cmdState
  let envAfter := stateAfter.env
  -- Forcing `infoTreeSnap` is what guarantees the tree is complete rather than
  -- the partial one visible while elaboration is still running.
  let _ := snap.elabSnap.infoTreeSnap.get
  let cmd : CapturedCommand := {
    ordinal
    stx := snap.stx
    range := syntaxRange snap.stx
    envBefore
    envAfter
    stateAfter
    -- `Command.State` is per command rather than cumulative, so a command
    -- contributes at most one tree.
    infoTree := stateAfter.infoState.trees.toArray[0]?
    messages := stateAfter.messages
    newConstants := newConstantsBetween envBefore envAfter
  }
  let acc := acc.push cmd
  match snap.nextCmdSnap? with
  | some next => collectCommands next.get envAfter (ordinal + 1) acc
  | none => acc

/-- Collect every error message a frontend run produced, as capture
diagnostics.

A frontend error terminates capture for the module (C2): partial information
never authorizes partial generated output.

`Message` carries line and column positions, so the `FileMap` converts them back
into the exact UTF-8 byte offsets M2 spans require. -/
private def frontendErrors (path : String) (fileMap : FileMap) (messages : List Message) :
    IO (Array Diagnostic) := do
  let mut ds : Array Diagnostic := #[]
  for msg in messages do
    if msg.severity == .error then
      let text ← msg.data.toString
      let startByte := (fileMap.ofPosition msg.pos).byteIdx
      let endByte := match msg.endPos with
        | some e => (fileMap.ofPosition e).byteIdx
        | none => startByte
      ds := ds.push (sourceError "SOURCE-ELABORATION-FAILED"
        text.trimAscii.toString (some (startByte, endByte)) path)
  return ds

/-- A completed declaration read back from a post-command environment.

The final `ConstantInfo` is the semantic authority for a declaration's kind,
universe parameters, type, and value (C4); information-tree expressions explain
how source regions contributed to it but do not override it. -/
structure CapturedDeclaration where
  name : Name
  info : ConstantInfo
  /-- Ordinal of the command that introduced this constant. -/
  commandOrdinal : Nat

namespace CapturedDeclaration

/-- The declaration's value, including the proof term of a theorem and the body
of an `opaque`.

`ConstantInfo.value?` hides both by default, but v0 lowers proof terms and
`opaque` bodies, so capture must see them. -/
def value? (d : CapturedDeclaration) : Option Expr :=
  d.info.value? (allowOpaque := true)

end CapturedDeclaration

/-- Every constant introduced by the module, in command order and sorted by name
within a command, together with any constant that could not be read back.

This is the module delta of C2: the union of the command-local deltas after the
imported baseline, with command ordinals preserved.

A name that the delta reports as new but that cannot be read back from the
post-command environment is a contradiction in what capture observed, so it is
returned rather than skipped: a declaration that cannot be inventoried is a
capture failure (C9), not something to leave out of the delta silently. -/
def moduleDeltaWithFailures (m : CapturedModule) :
    Array CapturedDeclaration × Array Name := Id.run do
  let mut acc : Array CapturedDeclaration := #[]
  let mut missing : Array Name := #[]
  for cmd in m.commands do
    for n in cmd.newConstants do
      match cmd.envAfter.find? n with
      | some info => acc := acc.push { name := n, info, commandOrdinal := cmd.ordinal }
      | none => missing := missing.push n
  return (acc, missing)

/-- The module delta, dropping the unreadable-constant report.

Callers that must diagnose an uninventoriable declaration use
`moduleDeltaWithFailures` and `checkDelta`. -/
def moduleDelta (m : CapturedModule) : Array CapturedDeclaration :=
  (moduleDeltaWithFailures m).1

/-- Diagnose any constant reported as new that could not be read back. -/
def checkDelta (path : String) (missing : Array Name) : Array Diagnostic :=
  missing.map fun n =>
    captureError "CAPTURE-DECLARATION-NOT-INVENTORIED"
      s!"constant '{n}' is new in the environment delta but cannot be read back"
      none path

/-- Check that every completed declaration is free of metavariables.

An elaborated expression retaining an unresolved metavariable is a capture
failure (C4, C9), not a hole to print or solve later. The completed
`ConstantInfo` read back from the post-command environment has already had its
metavariables instantiated by the frontend, so this is a check that the
invariant holds rather than a step that establishes it. -/
def checkCompleted (path : String) (decls : Array CapturedDeclaration) :
    Array Diagnostic := Id.run do
  let mut ds : Array Diagnostic := #[]
  for d in decls do
    if d.info.type.hasMVar then
      ds := ds.push (captureError "CAPTURE-UNRESOLVED-METAVARIABLE"
        s!"declaration '{d.name}' has an unresolved metavariable in its type"
        none path)
    if let some v := d.value? then
      if v.hasMVar then
        ds := ds.push (captureError "CAPTURE-UNRESOLVED-METAVARIABLE"
          s!"declaration '{d.name}' has an unresolved metavariable in its value"
          none path)
  return ds

/-- Elaborate one source module through the pinned stock frontend and collect
everything the later stages need.

`file` is the resolved absolute path the source bytes are read from. `path` is
the slash-separated package-relative path, and it is what Lean is told the file
is called, so that messages forwarded from the frontend already carry a
package-relative path and no absolute path can reach a diagnostic.

The caller must have initialized the search path and enabled initializer
execution; this runs inside an environment already prepared by `lake env`, as
the v0 interface requires. -/
def captureModule (module : ModuleName) (file : System.FilePath) (path : String) :
    IO (Except (Array Diagnostic) CapturedModule) := do
  let source ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext source path
  let opts := captureOptions
  let mainModuleName := module.foldl (init := Name.anonymous) fun n c => Name.mkStr n c

  let setup stx : Language.ProcessingT IO _ := return .ok {
    imports := stx.imports
    isModule := stx.isModule
    mainModuleName, opts
    trustLevel := 0
    plugins := #[]
  }

  let snap ← Language.Lean.process setup none { inputCtx with }
  -- Await every frontend task before extraction (C8). `getAll` walks the
  -- complete snapshot tree, which forces all of them.
  let tree := Language.toSnapshotTree snap
  let allSnaps := tree.getAll
  let messages := allSnaps.toList.flatMap (·.diagnostics.msgLog.toList)

  let errors ← frontendErrors path inputCtx.fileMap messages
  if !errors.isEmpty then
    return .error errors

  let some headerResult := snap.result?
    | return .error #[sourceError "SOURCE-HEADER-FAILED"
        "the module header could not be parsed" none path]
  let some processed := headerResult.processedSnap.get.result?
    | return .error #[sourceError "SOURCE-IMPORTS-FAILED"
        "the module's imports could not be processed" none path]

  let baseline := processed.cmdState.env
  let commands := collectCommands processed.firstCmdSnap.get baseline 0 #[]
  let finalEnv := match commands.back? with
    | some c => c.envAfter
    | none => baseline

  return .ok {
    module, source, path, baseline
    header := snap.stx
    commands, finalEnv
  }

end ExplicitLean
