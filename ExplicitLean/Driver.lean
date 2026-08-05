import ExplicitLean.Cli
import ExplicitLean.ExitStatus
import ExplicitLean.Publish
import ExplicitLean.Toolchain
import ExplicitLean.CaptureDebug
import ExplicitLean.Admission

/-!
# Compile driver

Resolves and validates the paths and environment, then runs the compilation
stages. Artifacts are published only after every stage succeeds.

The capture, admission, lowering, grammar checking, audit, verification, and
manifest stages arrive in later work packages; the skeleton runs the stages that
exist and publishes their output.
-/

namespace ExplicitLean

/-- Paths resolved against the filesystem and checked against the v0 layout
contract. -/
structure ResolvedInputs where
  /-- Resolved absolute package root. -/
  packageRoot : System.FilePath
  /-- Resolved absolute source file. -/
  source : System.FilePath
  /-- Slash-separated source path relative to the package root. This is the
  stable path used in diagnostics and manifest records. -/
  sourceRelPath : String
  /-- Resolved absolute output root. -/
  outputRoot : System.FilePath
  module : ModuleName
  deriving Inhabited

private def pathError (code message : String) : Diagnostic :=
  { code, message, phase := .cli }

/-- Resolve and validate the package root, source file, and output root.

The output root is created when absent: it is this command's own artifact
directory, unlike the package root and source file which must already exist. -/
def resolveInputs (opts : CompileOptions) : IO (Except (Array Diagnostic) ResolvedInputs) := do
  let packageRoot ← match ← resolveExisting opts.packageRoot with
    | .error _ => return .error #[pathError "PATH-PACKAGE-ROOT" "--package-root does not exist"]
    | .ok p => pure p
  if !(← packageRoot.isDir) then
    return .error #[pathError "PATH-PACKAGE-ROOT" "--package-root is not a directory"]

  let source ← match ← resolveExisting opts.source with
    | .error _ => return .error #[pathError "PATH-SOURCE" "--source does not exist"]
    | .ok p => pure p
  if ← source.isDir then
    return .error #[pathError "PATH-SOURCE" "--source is a directory, not a file"]

  let some rel := relativeTo packageRoot source
    | return .error #[pathError "PATH-SOURCE-ESCAPES-ROOT"
        "--source does not resolve beneath --package-root"]

  -- v0 has no source-directory remapping: the relative path must be exactly the
  -- module's components followed by `.lean`.
  let expected := opts.module.sourceRelPath
  if rel != expected then
    return .error #[pathError "PATH-MODULE-MISMATCH"
      s!"module '{opts.module}' must be read from '{expected}', got '{rel}'"]

  -- The output root is this command's own artifact directory, so unlike the
  -- package root and source file it is created when absent. A failure to create
  -- it is a path error, not an internal error, so it must not escape as an
  -- exception.
  try
    IO.FS.createDirAll opts.outputRoot
  catch _ =>
    return .error #[pathError "PATH-OUTPUT-ROOT" "--output-root could not be created"]
  let outputRoot ← match ← resolveExisting opts.outputRoot with
    | .error _ => return .error #[pathError "PATH-OUTPUT-ROOT" "--output-root could not be created"]
    | .ok p => pure p
  if !(← outputRoot.isDir) then
    return .error #[pathError "PATH-OUTPUT-ROOT" "--output-root is not a directory"]

  return .ok {
    packageRoot, source, outputRoot
    sourceRelPath := rel
    module := opts.module
  }

/-- Prepare this process to elaborate source with the pinned toolchain.

`lake env` has already put the imported artifacts on the search path; this
resolves that path and enables the initializer execution `importModules`
requires. -/
def initializeElaboration : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution

/-- A captured module together with its checked declaration delta. -/
structure Captured where
  module : CapturedModule
  delta : Array CapturedDeclaration

/-- Capture one module and check what capture itself must guarantee.

A declaration that cannot be inventoried, or an expression retaining an
unresolved metavariable, is a capture failure rather than something to pass on
to later stages (C4, C9). -/
def captureChecked (inputs : ResolvedInputs) :
    IO (Except (Array Diagnostic) Captured) := do
  initializeElaboration
  match ← captureModule inputs.module inputs.source inputs.sourceRelPath with
  | .error ds => return .error ds
  | .ok module =>
    let (delta, missing) := moduleDeltaWithFailures module
    let failures :=
      checkDelta inputs.sourceRelPath missing
        ++ checkCompleted inputs.sourceRelPath delta
    if !failures.isEmpty then
      return .error failures
    return .ok { module, delta }

/-- Capture one module and return its stable projection.

This is the coverage-probe entry point required by
[C10](../CAPTURE.md#c10-coverage-probes-and-acceptance). It observes the source
elaboration and reports what capture recovered, without admitting or lowering
anything, so a module outside the v0 feature set still yields a projection. -/
def captureDebug (inputs : ResolvedInputs) : IO (Except (Array Diagnostic) String) := do
  match ← captureChecked inputs with
  | .error ds => return .error ds
  | .ok c => return .ok (projectModule c.module)

/-- Capture and admit one module, reporting whether it is inside the v0 source
feature set. -/
def admitOnly (inputs : ResolvedInputs) : IO (Array Diagnostic) := do
  match ← captureChecked inputs with
  | .error ds => return ds
  | .ok c => return admitModule inputs.sourceRelPath c.module c.delta

/-- Run the compilation stages for validated inputs.

Capture and admission are implemented. Lowering, grammar checking, the output
elaboration audit, quotation verification, and manifest generation arrive in
later work packages, so an admitted module is still reported as not yet
compilable rather than published without those checks. -/
def runStages (inputs : ResolvedInputs) : IO (Except (Array Diagnostic) Artifacts) := do
  match ← captureChecked inputs with
  | .error ds => return .error ds
  | .ok c =>
    let rejected := admitModule inputs.sourceRelPath c.module c.delta
    if !rejected.isEmpty then
      return .error rejected
    return .error #[{
      code := "UNSUPPORTED-NOT-IMPLEMENTED"
      message :=
        s!"'{inputs.module}' is inside the v0 source feature set, but lowering \
is not implemented yet"
      phase := .lowering
      span := some { file := inputs.sourceRelPath, startByte := 0, endByte := 0 }
    }]

/-- A failure path that produced no diagnostic would exit `0` and claim a
success that never happened, so report it as an internal error instead. -/
private def failureDiagnostics (ds : Array Diagnostic) : Array Diagnostic :=
  if ds.isEmpty then
    #[{ code := "INTERNAL-NO-DIAGNOSTIC"
        message := "compilation failed without producing a diagnostic"
        phase := .internal }]
  else ds

/-- Run one `compile` invocation and return its diagnostics.

Paths are resolved before the environment is validated: the environment checks
read files beneath the package root, so reporting them against a root that does
not exist would describe the wrong problem. -/
def compile (opts : CompileOptions) : IO (Array Diagnostic) := do
  match ← resolveInputs opts with
  | .error ds => return failureDiagnostics ds
  | .ok inputs =>
    let envDiags ← validateEnvironment inputs.packageRoot
    if !envDiags.isEmpty then
      return envDiags
    match opts.command with
    | .captureDebug =>
      match ← captureDebug inputs with
      | .error ds => return failureDiagnostics ds
      | .ok projection =>
        IO.print projection
        return #[]
    | .admit =>
      return ← admitOnly inputs
    | .compile =>
      match ← runStages inputs with
      | .error ds => return failureDiagnostics ds
      | .ok artifacts =>
        publish inputs.outputRoot inputs.module artifacts
        return #[]

/-- Entry point shared by the executable and the tests. -/
def main (args : List String) : IO UInt32 := do
  let fmt := peekDiagnosticFormat args
  match parseArgs args with
  | .error ds =>
    let ds := failureDiagnostics ds
    emitDiagnostics fmt ds
    return (exitStatus ds)
  | .ok opts =>
    try
      let ds ← compile opts
      emitDiagnostics opts.diagnosticFormat ds
      return (exitStatus ds)
    catch e =>
      let d : Diagnostic := {
        code := "INTERNAL-UNCAUGHT"
        message := "internal compiler error"
        phase := .internal
      }
      emitDiagnostics opts.diagnosticFormat #[d] (trace := some (toString e))
      return (exitStatus #[d])

end ExplicitLean
