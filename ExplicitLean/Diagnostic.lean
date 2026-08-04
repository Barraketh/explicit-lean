import ExplicitLean.Json

/-!
# Diagnostics

Structured diagnostics with stable codes, phases, and optional
[M2](../MANIFEST.md#source-spans) source spans, rendered either as concise human
text or as one canonical JSON object per line.

Diagnostics carry package-relative paths and no stack addresses, timestamps,
process IDs, or absolute paths.
-/

namespace ExplicitLean

/-- Compilation phase a diagnostic belongs to. The constructor order is the
phase order used when sorting diagnostics. -/
inductive Phase where
  | cli | source | capture | admission | lowering
  | grammar | audit | verification | manifest | internal
  deriving Inhabited, Repr, BEq, DecidableEq

namespace Phase

def toString : Phase → String
  | .cli => "cli"
  | .source => "source"
  | .capture => "capture"
  | .admission => "admission"
  | .lowering => "lowering"
  | .grammar => "grammar"
  | .audit => "audit"
  | .verification => "verification"
  | .manifest => "manifest"
  | .internal => "internal"

/-- Rank in the documented phase order, used as a sort key. -/
def order : Phase → Nat
  | .cli => 0
  | .source => 1
  | .capture => 2
  | .admission => 3
  | .lowering => 4
  | .grammar => 5
  | .audit => 6
  | .verification => 7
  | .manifest => 8
  | .internal => 9

instance : ToString Phase := ⟨toString⟩

end Phase

/-- Diagnostic severity. v0 emits only `error`. -/
inductive Severity where
  | error
  deriving Inhabited, Repr, BEq, DecidableEq

def Severity.toString : Severity → String
  | .error => "error"

instance : ToString Severity := ⟨Severity.toString⟩

/-- An [M2](../MANIFEST.md#source-spans) source span: a half-open byte interval
into the exact UTF-8 source bytes, with a slash-separated package-relative
path. -/
structure Span where
  /-- Slash-separated path relative to the package root. Never absolute and
  never containing `..`. -/
  file : String
  /-- Zero-based, inclusive start byte offset. -/
  startByte : Nat
  /-- Zero-based, exclusive end byte offset. -/
  endByte : Nat
  deriving Inhabited, Repr, BEq

def Span.toCJson (s : Span) : CJson :=
  .obj #[
    ("endByte", .num s.endByte),
    ("file", .str s.file),
    ("startByte", .num s.startByte)
  ]

/-- A structured diagnostic. `code` is a stable uppercase identifier matching
`[A-Z][A-Z0-9-]*`. -/
structure Diagnostic where
  code : String
  message : String
  phase : Phase
  severity : Severity := .error
  span : Option Span := none
  deriving Inhabited, Repr

namespace Diagnostic

def toCJson (d : Diagnostic) : CJson :=
  let base : Array (String × CJson) := #[
    ("code", .str d.code),
    ("message", .str d.message),
    ("phase", .str d.phase.toString),
    ("severity", .str d.severity.toString)
  ]
  .obj (match d.span with
    | some s => base.push ("span", s.toCJson)
    | none => base)

/-- Concise human-readable rendering. -/
def toHuman (d : Diagnostic) : String :=
  let loc := match d.span with
    | some s => s!"{s.file}:{s.startByte}-{s.endByte}: "
    | none => ""
  s!"{loc}{d.severity}[{d.code}] ({d.phase}) {d.message}"

/-- Is `a` ordered strictly before `b`?

The documented order is: ranged before unranged, then source file, start byte,
end byte, phase order, code, then message UTF-8 bytes. -/
def lt (a b : Diagnostic) : Bool :=
  match a.span, b.span with
  | some _, none => true
  | none, some _ => false
  | some x, some y =>
    if x.file != y.file then CJson.utf8Lt x.file y.file
    else if x.startByte != y.startByte then x.startByte < y.startByte
    else if x.endByte != y.endByte then x.endByte < y.endByte
    else rest a b
  | none, none => rest a b
where
  /-- Tail of the ordering shared by the ranged and unranged cases. -/
  rest (a b : Diagnostic) : Bool :=
    if a.phase.order != b.phase.order then a.phase.order < b.phase.order
    else if a.code != b.code then CJson.utf8Lt a.code b.code
    else CJson.utf8Lt a.message b.message

/-- Sort diagnostics into the documented canonical order. -/
def sortDiagnostics (ds : Array Diagnostic) : Array Diagnostic :=
  ds.qsort lt

end Diagnostic

/-- How diagnostics are rendered to standard error. -/
inductive DiagnosticFormat where
  | human
  | json
  deriving Inhabited, Repr, BEq, DecidableEq

/-- Render sorted diagnostics to standard error in the requested format.

In `human` mode an internal error may append a noncanonical debugging trace;
`json` mode never does. -/
def emitDiagnostics
    (fmt : DiagnosticFormat) (ds : Array Diagnostic) (trace : Option String := none) :
    IO Unit := do
  let stderr ← IO.getStderr
  for d in Diagnostic.sortDiagnostics ds do
    match fmt with
    | .human => stderr.putStrLn d.toHuman
    | .json => stderr.putStrLn (CJson.render d.toCJson)
  if fmt == .human then
    if let some t := trace then
      stderr.putStrLn t

end ExplicitLean
