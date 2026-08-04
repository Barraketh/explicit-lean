import ExplicitLean

/-!
# Unit tests

Checks on the pure logic that the golden-file case harness cannot reach:
canonical JSON rendering, byte ordering, diagnostic ordering, exit-status
selection, and the module-to-path mapping.

Each check is a `#guard`-style assertion evaluated at run time so a failure
names the specific expectation.
-/

open ExplicitLean

namespace ExplicitLean.Unit

/-- Accumulated failures. -/
abbrev Failures := Array String

def check (name : String) (ok : Bool) : Failures → Failures :=
  fun fs => if ok then fs else fs.push name

def checkEq [BEq α] [ToString α] (name : String) (got want : α) : Failures → Failures :=
  fun fs => if got == want then fs else fs.push s!"{name}: expected '{want}', got '{got}'"

/-! ## Canonical JSON -/

def jsonTests (fs : Failures) : Failures :=
  fs
  -- Object keys are sorted by unescaped UTF-8 bytes, not insertion order.
  |> checkEq "obj key sorting"
      (CJson.render (.obj #[("b", .num 1), ("a", .num 2)]))
      "{\"a\":2,\"b\":1}"
  -- Uppercase sorts before lowercase under byte order.
  |> checkEq "obj key byte order"
      (CJson.render (.obj #[("a", .num 1), ("B", .num 2)]))
      "{\"B\":2,\"a\":1}"
  -- A shorter key that is a prefix of a longer one sorts first.
  |> checkEq "obj key prefix order"
      (CJson.render (.obj #[("ab", .num 1), ("a", .num 2)]))
      "{\"a\":2,\"ab\":1}"
  |> checkEq "empty obj" (CJson.render (.obj #[])) "{}"
  |> checkEq "empty arr" (CJson.render (.arr #[])) "[]"
  -- Arrays preserve order and separate every element.
  |> checkEq "arr order"
      (CJson.render (.arr #[.num 1, .num 2, .num 3]))
      "[1,2,3]"
  -- An element that renders to a short string still gets its separator.
  |> checkEq "arr of empty strings"
      (CJson.render (.arr #[.str "", .str "", .str ""]))
      "[\"\",\"\",\"\"]"
  |> checkEq "arr of empty arrays"
      (CJson.render (.arr #[.arr #[], .arr #[]]))
      "[[],[]]"
  |> checkEq "nested" (CJson.render (.obj #[("k", .arr #[.bool true, .bool false])]))
      "{\"k\":[true,false]}"
  -- Escaping: short escapes preferred, lowercase \u00xx otherwise.
  |> checkEq "escape quote and backslash"
      (CJson.render (.str "a\"b\\c")) "\"a\\\"b\\\\c\""
  |> checkEq "escape short forms"
      (CJson.render (.str "\x08\t\n\x0c\r")) "\"\\b\\t\\n\\f\\r\""
  |> checkEq "escape control as lowercase hex"
      (CJson.render (.str "\x00\x01\x1f")) "\"\\u0000\\u0001\\u001f\""
  -- `/` and non-ASCII scalars are not escaped.
  |> checkEq "no solidus escape" (CJson.render (.str "a/b")) "\"a/b\""
  |> checkEq "no unicode escape" (CJson.render (.str "λ→é")) "\"λ→é\""
  -- Large integers are exact, not floating point.
  |> checkEq "big integer"
      (CJson.render (.num 123456789012345678901234567890))
      "123456789012345678901234567890"
  |> checkEq "zero" (CJson.render (.num 0)) "0"

/-! ## Byte ordering -/

def orderTests (fs : Failures) : Failures :=
  fs
  |> check "utf8Lt empty first" (CJson.utf8Lt "" "a")
  |> check "utf8Lt not reflexive" (!CJson.utf8Lt "a" "a")
  |> check "utf8Lt empty vs empty" (!CJson.utf8Lt "" "")
  |> check "utf8Lt prefix" (CJson.utf8Lt "ab" "abc")
  |> check "utf8Lt prefix reverse" (!CJson.utf8Lt "abc" "ab")
  |> check "utf8Lt uppercase first" (CJson.utf8Lt "B" "a")
  -- Multi-byte scalars compare by bytes; 'é' (C3 A9) sorts after 'z' (7A).
  |> check "utf8Lt multibyte" (CJson.utf8Lt "z" "é")
  |> check "utf8Lt multibyte reverse" (!CJson.utf8Lt "é" "z")

/-! ## Diagnostic ordering -/

private def d (code : String) (phase : Phase) (span : Option Span := none) : Diagnostic :=
  { code, message := "m", phase, span }

private def codes (ds : Array Diagnostic) : String :=
  String.intercalate "," (Diagnostic.sortDiagnostics ds |>.toList.map (·.code))

def diagnosticTests (fs : Failures) : Failures :=
  let sp (f : String) (s e : Nat) : Option Span := some { file := f, startByte := s, endByte := e }
  fs
  -- Ranged diagnostics sort before unranged ones.
  |> checkEq "ranged before unranged"
      (codes #[d "A" .cli, d "B" .cli (sp "f" 0 1)]) "B,A"
  -- Then by file, start byte, end byte.
  |> checkEq "by file"
      (codes #[d "A" .cli (sp "z" 0 1), d "B" .cli (sp "a" 0 1)]) "B,A"
  |> checkEq "by start byte"
      (codes #[d "A" .cli (sp "f" 5 9), d "B" .cli (sp "f" 2 9)]) "B,A"
  |> checkEq "by end byte"
      (codes #[d "A" .cli (sp "f" 2 9), d "B" .cli (sp "f" 2 3)]) "B,A"
  -- Then by phase order, which is the documented phase sequence, not alphabetical.
  |> checkEq "by phase order"
      (codes #[d "A" .manifest, d "B" .source]) "B,A"
  |> checkEq "internal sorts last"
      (codes #[d "A" .internal, d "B" .verification]) "B,A"
  -- Then by code, then message bytes.
  |> checkEq "by code" (codes #[d "ZZ" .cli, d "AA" .cli]) "AA,ZZ"
  |> checkEq "by message"
      (String.intercalate ","
        (Diagnostic.sortDiagnostics
          #[{ code := "A", message := "z", phase := .cli },
            { code := "A", message := "a", phase := .cli }]
          |>.toList.map (·.message)))
      "a,z"
  -- Phase ordering also applies within the unranged group.
  |> checkEq "unranged phase order"
      (codes #[d "A" .cli, d "B" .cli (sp "f" 0 1), d "C" .source]) "B,A,C"

/-! ## Exit statuses -/

def exitTests (fs : Failures) : Failures :=
  fs
  |> checkEq "no diagnostics is success" (exitStatus #[]) 0
  |> checkEq "cli is 2" (exitStatus #[d "A" .cli]) 2
  |> checkEq "source is 3" (exitStatus #[d "A" .source]) 3
  |> checkEq "admission is 4" (exitStatus #[d "A" .admission]) 4
  |> checkEq "lowering is 5" (exitStatus #[d "A" .lowering]) 5
  |> checkEq "grammar is 5" (exitStatus #[d "A" .grammar]) 5
  |> checkEq "audit is 5" (exitStatus #[d "A" .audit]) 5
  |> checkEq "verification is 5" (exitStatus #[d "A" .verification]) 5
  |> checkEq "manifest is 5" (exitStatus #[d "A" .manifest]) 5
  |> checkEq "internal is 70" (exitStatus #[d "A" .internal]) 70
  -- Greatest severity wins, in the order 70, 5, 4, 3, 2.
  |> checkEq "internal beats check" (exitStatus #[d "A" .grammar, d "B" .internal]) 70
  |> checkEq "check beats unsupported" (exitStatus #[d "A" .admission, d "B" .grammar]) 5
  |> checkEq "unsupported beats source" (exitStatus #[d "A" .source, d "B" .admission]) 4
  |> checkEq "source beats cli" (exitStatus #[d "A" .cli, d "B" .source]) 3
  -- Order of the input array does not matter.
  |> checkEq "order independent" (exitStatus #[d "A" .internal, d "B" .cli]) 70

/-! ## Module names and paths -/

def moduleTests (fs : Failures) : Failures :=
  fs
  |> checkEq "single component path"
      ((ModuleName.parse "A").map ModuleName.sourceRelPath |>.getD "?") "A.lean"
  |> checkEq "nested path"
      ((ModuleName.parse "A.B.C").map ModuleName.sourceRelPath |>.getD "?") "A/B/C.lean"
  |> check "empty name rejected" (ModuleName.parse "" |>.isNone)
  |> check "empty component rejected" (ModuleName.parse "A..B" |>.isNone)
  |> check "trailing dot rejected" (ModuleName.parse "A." |>.isNone)
  |> check "leading dot rejected" (ModuleName.parse ".A" |>.isNone)
  |> checkEq "generated module mapping"
      (ModuleName.toString (generatedModuleName #["A", "B"])) "Explicit.A.B"
  -- Relative paths: containment is a component-wise prefix check.
  |> checkEq "relativeTo nested" (relativeTo "/a/b" "/a/b/c/d.lean" |>.getD "?") "c/d.lean"
  |> check "relativeTo escape" (relativeTo "/a/b" "/a/c/d.lean" |>.isNone)
  -- A sibling whose name merely starts with the root's name is not inside it.
  |> check "relativeTo sibling prefix" (relativeTo "/a/b" "/a/bc/d.lean" |>.isNone)
  |> check "relativeTo equal is none" (relativeTo "/a/b" "/a/b" |>.isNone)
  |> check "relativeTo shorter" (relativeTo "/a/b/c" "/a/b" |>.isNone)
  -- Redundant separators do not change containment.
  |> checkEq "relativeTo redundant separators"
      (relativeTo "/a//b/" "/a/b/c.lean" |>.getD "?") "c.lean"

/-! ## CLI parsing -/

private def parseCodes (args : List String) : String :=
  match parseArgs args with
  | .error ds => String.intercalate "," (ds.toList.map (·.code))
  | .ok _ => "ok"

def cliTests (fs : Failures) : Failures :=
  let full := ["compile", "--package-root", "r", "--module", "A.B",
               "--source", "s", "--output-root", "o"]
  fs
  |> checkEq "full command parses" (parseCodes full) "ok"
  -- Both `--opt value` and `--opt=value` spellings are accepted.
  |> checkEq "equals spelling"
      (parseCodes ["compile", "--package-root=r", "--module=A.B",
                   "--source=s", "--output-root=o"]) "ok"
  |> checkEq "mixed spelling"
      (parseCodes ["compile", "--package-root=r", "--module", "A.B",
                   "--source=s", "--output-root", "o"]) "ok"
  -- A value containing `=` survives the `--opt=value` split.
  |> check "value with equals"
      (match parseArgs ["compile", "--package-root=r", "--module=A.B",
                        "--source=a=b", "--output-root=o"] with
       | .ok o => o.source.toString == "a=b"
       | .error _ => false)
  |> check "diagnostic format defaults to human"
      (match parseArgs full with
       | .ok o => o.diagnosticFormat == DiagnosticFormat.human
       | .error _ => false)
  |> checkEq "unknown command" (parseCodes ["build"]) "CLI-UNKNOWN-COMMAND"
  |> checkEq "no command" (parseCodes []) "CLI-NO-COMMAND"
  |> checkEq "duplicate option"
      (parseCodes (full ++ ["--module", "A.C"])) "CLI-DUPLICATE-OPTION"
  |> checkEq "bad module name"
      (parseCodes ["compile", "--package-root=r", "--module=A..B",
                   "--source=s", "--output-root=o"]) "CLI-BAD-MODULE-NAME"
  |> checkEq "bad diagnostic format"
      (parseCodes (full ++ ["--diagnostic-format", "yaml"])) "CLI-BAD-DIAGNOSTIC-FORMAT"
  -- An option immediately followed by another option is a missing value, not a
  -- silent consumption of the next flag.
  |> checkEq "missing value"
      (parseCodes ["compile", "--module", "--source", "s"]) "CLI-MISSING-VALUE"
  |> checkEq "trailing option without value"
      (parseCodes ["compile", "--module"]) "CLI-MISSING-VALUE"
  -- A bare argument is not an option, even when it contains `=`.
  |> checkEq "bare argument" (parseCodes ["compile", "stray"]) "CLI-UNEXPECTED-ARGUMENT"
  |> checkEq "bare argument with equals"
      (parseCodes ["compile", "foo=bar"]) "CLI-UNEXPECTED-ARGUMENT"
  -- A value beginning with `--` is reachable through the `=` spelling.
  |> check "value beginning with dashes"
      (match parseArgs ["compile", "--package-root=r", "--module=A.B",
                        "--source=--odd", "--output-root=o"] with
       | .ok o => o.source.toString == "--odd"
       | .error _ => false)
  -- Every missing required option is reported, not just the first.
  |> checkEq "all missing reported"
      (parseCodes ["compile", "--module", "A.B"])
      "CLI-MISSING-OPTION,CLI-MISSING-OPTION,CLI-MISSING-OPTION"
  -- `peekDiagnosticFormat` finds the format even when parsing later fails.
  |> check "peek json"
      (peekDiagnosticFormat ["compile", "--diagnostic-format", "json"] == .json)
  |> check "peek json equals spelling"
      (peekDiagnosticFormat ["compile", "--diagnostic-format=json"] == .json)
  |> check "peek defaults to human"
      (peekDiagnosticFormat ["compile"] == .human)

/-! ## Artifact publication

No fixture case can reach `publish` until a compilation actually succeeds, so
these checks drive it directly against a temporary output root. -/

/-! ## Toolchain validation

The compiler's own repository must satisfy the environment contract it enforces
on package roots, so an upgrade that changes `lean-toolchain` without rebuilding,
or vice versa, fails here. -/

def toolchainTests : IO Failures := do
  let mut fs : Failures := #[]
  let root ← IO.currentDir
  let ds ← validateEnvironment root
  fs := fs |> checkEq "this repository is a valid package root"
    (String.intercalate "," (ds.toList.map (·.code))) ""
  match ← readToolchainPin root with
  | .error d => fs := fs.push s!"cannot read this repository's pin: {d.code}"
  | .ok pin =>
    fs := fs |> checkEq "pin agrees with the running Lean"
      pin s!"leanprover/lean4:v{pinnedLeanVersion}"
  return fs

def publishTests (scratch : System.FilePath) : IO Failures := do
  let mut fs : Failures := #[]
  let root := scratch / "publish"
  if ← root.pathExists then IO.FS.removeDirAll root
  IO.FS.createDirAll root

  let m : ModuleName := #["A", "B"]
  publish root m { generatedSource := "src\n", manifest := "{}\n" }

  -- Artifacts land at OUT/Explicit/A/B.lean and OUT/Explicit/A/B.manifest.ndjson.
  let srcPath := root / "Explicit" / "A" / "B.lean"
  let manPath := root / "Explicit" / "A" / "B.manifest.ndjson"
  fs := fs |> check "generated module published" (← srcPath.pathExists)
  fs := fs |> check "manifest published" (← manPath.pathExists)
  if ← srcPath.pathExists then
    fs := fs |> checkEq "generated module bytes" (← IO.FS.readFile srcPath) "src\n"
  if ← manPath.pathExists then
    fs := fs |> checkEq "manifest bytes" (← IO.FS.readFile manPath) "{}\n"

  -- No provenance sidecars means no provenance directory.
  fs := fs |> check "no empty provenance directory"
    (!(← (root / "Explicit" / "A" / "B.provenance").pathExists))

  -- The staging directory never survives a run.
  fs := fs |> check "staging removed"
    (!(← (root / ".explicit-lean-staging").pathExists))

  -- Republishing replaces the previous bytes rather than failing or appending.
  publish root m { generatedSource := "src2\n", manifest := "{}\n" }
  fs := fs |> checkEq "republish overwrites" (← IO.FS.readFile srcPath) "src2\n"

  -- Provenance sidecars are published beneath the `.provenance` directory.
  publish root m {
    generatedSource := "src\n", manifest := "{}\n"
    provenance := #[("one.json", "1\n"), ("two.json", "2\n")]
  }
  let provOne := root / "Explicit" / "A" / "B.provenance" / "one.json"
  fs := fs |> check "provenance published" (← provOne.pathExists)
  if ← provOne.pathExists then
    fs := fs |> checkEq "provenance bytes" (← IO.FS.readFile provOne) "1\n"

  -- Publishing without sidecars again removes the stale provenance directory.
  publish root m { generatedSource := "src\n", manifest := "{}\n" }
  fs := fs |> check "stale provenance removed"
    (!(← (root / "Explicit" / "A" / "B.provenance").pathExists))

  -- A single-component module publishes directly under `Explicit`.
  publish root #["Solo"] { generatedSource := "s\n", manifest := "{}\n" }
  fs := fs |> check "single-component module"
    (← (root / "Explicit" / "Solo.lean").pathExists)

  IO.FS.removeDirAll root
  return fs

def run : IO UInt32 := do
  let scratch := (← IO.currentDir) / ".lake" / "test-scratch"
  IO.FS.createDirAll scratch
  let fs := #[] |> jsonTests |> orderTests |> diagnosticTests
              |> exitTests |> moduleTests |> cliTests
  let fs := fs ++ (← toolchainTests) ++ (← publishTests scratch)
  for f in fs do
    IO.println s!"FAIL     {f}"
  if fs.isEmpty then
    IO.println "ok       unit"
    return 0
  else
    IO.println s!"{fs.size} unit assertions failed"
    return 1

end ExplicitLean.Unit
