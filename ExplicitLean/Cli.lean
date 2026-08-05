import ExplicitLean.Diagnostic
import ExplicitLean.Paths

/-!
# Command-line interface

The v0 interface has one command:

```text
explicit-lean compile \
  --package-root ROOT \
  --module MODULE \
  --source FILE \
  --output-root OUT \
  [--diagnostic-format human|json]
```

All four path or identity options are required.

Options accept both the `--opt value` and `--opt=value` spellings. A value that
itself begins with `--` must use the `=` spelling, since in the space spelling an
argument beginning with `--` is read as the next option rather than as a value.
-/

namespace ExplicitLean

/-- Which command was requested. -/
inductive Command where
  /-- The v0 command: capture, check, and publish artifacts. -/
  | compile
  /-- Capture only, printing the stable capture projection to standard output.

  This is the coverage-probe entry point required by
  [C10](../CAPTURE.md#c10-coverage-probes-and-acceptance). It publishes nothing,
  so `--output-root` is unused but still required, keeping one option shape for
  both commands. -/
  | captureDebug
  /-- Capture and admit only, reporting whether the module is inside the v0
  source feature set. Publishes nothing. -/
  | admit
  deriving Inhabited, Repr, BEq, DecidableEq

/-- Parsed and validated options. Paths here are exactly as given on the command
line; resolution against the filesystem happens in `Driver`. -/
structure CompileOptions where
  command : Command
  packageRoot : System.FilePath
  module : ModuleName
  source : System.FilePath
  outputRoot : System.FilePath
  diagnosticFormat : DiagnosticFormat
  deriving Inhabited

/-- The usage text, printed on a command-line error. -/
def usage : String :=
  "usage: explicit-lean compile|capture-debug|admit \
--package-root ROOT --module MODULE --source FILE --output-root OUT \
[--diagnostic-format human|json]"

private def cliError (code message : String) : Diagnostic :=
  { code, message, phase := .cli }

/-- Raw option values collected during parsing, before the required-option
check. -/
private structure Partial where
  packageRoot : Option System.FilePath := none
  module : Option String := none
  source : Option System.FilePath := none
  outputRoot : Option System.FilePath := none
  diagnosticFormat : Option DiagnosticFormat := none

/-- Parse the diagnostic format early and independently of the rest of parsing,
so that later command-line errors are reported in the requested format.

An invalid or missing value falls back to `human`; the error itself is raised by
the main parse. -/
def peekDiagnosticFormat (args : List String) : DiagnosticFormat :=
  match args with
  | "--diagnostic-format" :: "json" :: _ => .json
  | "--diagnostic-format=json" :: _ => .json
  | _ :: rest => peekDiagnosticFormat rest
  | [] => .human

/-- Parse command-line arguments. Returns diagnostics on failure. -/
def parseArgs (args : List String) : Except (Array Diagnostic) CompileOptions := do
  match args with
  | [] =>
    .error #[cliError "CLI-NO-COMMAND" s!"missing command. {usage}"]
  | cmd :: rest =>
    let command ←
      match cmd with
      | "compile" => pure Command.compile
      | "capture-debug" => pure Command.captureDebug
      | "admit" => pure Command.admit
      | _ => .error #[cliError "CLI-UNKNOWN-COMMAND" s!"unknown command '{cmd}'. {usage}"]
    let p ← go rest {}
    finish command p
where
  /-- Accept the `--opt=value` spelling. Only an argument that starts with `--`
  is an option, so a bare argument containing `=` is not split into a bogus
  option name. Everything after the first `=` is the value, so values may
  themselves contain `=`. -/
  splitEq (s : String) : Option (String × String) :=
    if !s.startsWith "--" then none
    else
      match s.splitOn "=" with
      | key :: rest@(_ :: _) => some (key, String.intercalate "=" rest)
      | _ => none

  go (args : List String) (p : Partial) : Except (Array Diagnostic) Partial := do
    match args with
    | [] => .ok p
    | arg :: rest =>
      if !arg.startsWith "--" then
        .error #[cliError "CLI-UNEXPECTED-ARGUMENT" s!"unexpected argument '{arg}'"]
      else
        match splitEq arg with
        | some (key, value) => assign key value rest p
        | none =>
          match rest with
          | value :: rest' =>
            -- An option immediately followed by another option is a missing
            -- value rather than a silent consumption of that next option.
            if value.startsWith "--" then
              .error #[cliError "CLI-MISSING-VALUE" s!"option '{arg}' requires a value"]
            else
              assign arg value rest' p
          | [] =>
            .error #[cliError "CLI-MISSING-VALUE" s!"option '{arg}' requires a value"]

  assign (key value : String) (rest : List String) (p : Partial) :
      Except (Array Diagnostic) Partial := do
    match key with
    | "--package-root" =>
      if p.packageRoot.isSome then duplicate key
      else go rest { p with packageRoot := some ⟨value⟩ }
    | "--module" =>
      if p.module.isSome then duplicate key
      else go rest { p with module := some value }
    | "--source" =>
      if p.source.isSome then duplicate key
      else go rest { p with source := some ⟨value⟩ }
    | "--output-root" =>
      if p.outputRoot.isSome then duplicate key
      else go rest { p with outputRoot := some ⟨value⟩ }
    | "--diagnostic-format" =>
      if p.diagnosticFormat.isSome then duplicate key
      else
        match value with
        | "human" => go rest { p with diagnosticFormat := some .human }
        | "json" => go rest { p with diagnosticFormat := some .json }
        | _ =>
          .error #[cliError "CLI-BAD-DIAGNOSTIC-FORMAT"
            s!"--diagnostic-format must be 'human' or 'json', got '{value}'"]
    | _ =>
      .error #[cliError "CLI-UNKNOWN-OPTION" s!"unknown option '{key}'"]

  duplicate (key : String) : Except (Array Diagnostic) Partial :=
    .error #[cliError "CLI-DUPLICATE-OPTION" s!"option '{key}' given more than once"]

  missingOption (name : String) : Diagnostic :=
    cliError "CLI-MISSING-OPTION" s!"missing required option '{name}'"

  /-- Check the required options and parse the module name.

  Destructuring every option in one pattern match reports all four missing
  options together and reaches the module-name check only when a value is
  present, so no branch can return an empty diagnostic array — which would
  otherwise be reported as a silent success. -/
  finish (command : Command) (p : Partial) : Except (Array Diagnostic) CompileOptions :=
    match p.packageRoot, p.module, p.source, p.outputRoot with
    | some packageRoot, some moduleText, some source, some outputRoot =>
      match ModuleName.parse moduleText with
      | some module =>
        .ok {
          command, packageRoot, module, source, outputRoot
          diagnosticFormat := p.diagnosticFormat.getD .human
        }
      | none =>
        .error #[cliError "CLI-BAD-MODULE-NAME"
          s!"--module must be a nonanonymous dotted Lean module name, got '{moduleText}'"]
    | _, _, _, _ =>
      -- At least one option is absent, so this array is never empty.
      .error <| #[
        (p.packageRoot.isNone, "--package-root"),
        (p.module.isNone, "--module"),
        (p.source.isNone, "--source"),
        (p.outputRoot.isNone, "--output-root")
      ].filterMap fun (absent, name) =>
        if absent then some (missingOption name) else none

end ExplicitLean
