import ExplicitLean
import ExplicitLeanTest.Unit

/-!
# Test harness

Runs the complete local test suite: the unit checks in `Unit.lean`, then the
fixture cases in `test/cases`, driving the built `explicit-lean` executable as a
subprocess and comparing exit status, standard error bytes, and the published
artifact tree against golden files. See `test/README.md` for the layout.

Positive cases additionally run a second time into a clean output directory and
require byte-identical published artifacts.
-/

open ExplicitLean

namespace ExplicitLean.Test

/-- Where the harness finds things, relative to the repository root. -/
structure Config where
  /-- Repository root, taken from the current working directory. -/
  root : System.FilePath
  /-- The executable under test. -/
  exe : System.FilePath
  /-- Directory holding the case fixtures. -/
  casesDir : System.FilePath
  /-- Scratch directory for per-run output roots. -/
  scratch : System.FilePath
  /-- Rewrite golden files instead of comparing against them. -/
  accept : Bool

/-- One case's outcome. -/
inductive Outcome where
  | pass
  | fail (reasons : Array String)
  | accepted

/-- Read a file as a `String`, or `none` when it does not exist. -/
def readIfExists (p : System.FilePath) : IO (Option String) := do
  if ← p.pathExists then return some (← IO.FS.readFile p) else return none

/-- Parse a `cmd` file: one argument per line, ignoring blank lines and lines
whose first nonspace character is `#`. -/
def parseCmd (contents : String) (pkg out : System.FilePath) : List String :=
  contents.splitOn "\n"
    |>.map (·.trimAscii.toString)
    |>.filter (fun l => !l.isEmpty && !l.startsWith "#")
    |>.map fun l =>
      l.replace "@PKG@" pkg.toString |>.replace "@OUT@" out.toString

/-- Every file beneath `dir`, as (slash-separated relative path, bytes), sorted
by path. Returns an empty array when `dir` does not exist. -/
partial def snapshotTree (dir : System.FilePath) : IO (Array (String × String)) := do
  if !(← dir.pathExists) then return #[]
  let entries ← go dir ""
  return entries.qsort fun a b => CJson.utf8Lt a.1 b.1
where
  go (d : System.FilePath) (prefix_ : String) : IO (Array (String × String)) := do
    let mut acc : Array (String × String) := #[]
    for entry in ← d.readDir do
      let rel := if prefix_.isEmpty then entry.fileName else prefix_ ++ "/" ++ entry.fileName
      if ← entry.path.isDir then
        acc := acc ++ (← go entry.path rel)
      else
        acc := acc.push (rel, ← IO.FS.readFile entry.path)
    return acc

/-- Render a tree snapshot for a failure message.

This is display only. Trees are compared as the structured `(path, contents)`
arrays, because this rendering pads a file that does not end in a newline and so
cannot distinguish every pair of distinct trees. -/
def renderTree (files : Array (String × String)) : String :=
  if files.isEmpty then "(no files)\n"
  else
    files.foldl (init := "") fun acc (path, contents) =>
      acc ++ "=== " ++ path ++ "\n" ++ contents
        ++ (if contents.endsWith "\n" then "" else "\n")

/-- Write a tree snapshot back out as golden files beneath `dir`. -/
def writeTree (dir : System.FilePath) (files : Array (String × String)) : IO Unit := do
  if ← dir.pathExists then IO.FS.removeDirAll dir
  if files.isEmpty then return
  for (rel, contents) in files do
    let target := dir / rel
    if let some parent := target.parent then
      IO.FS.createDirAll parent
    IO.FS.writeBinFile target contents.toUTF8

/-- Run the executable once with `args`, returning exit status and stderr. -/
def runOnce (cfg : Config) (args : List String) : IO (UInt32 × String) := do
  let out ← IO.Process.output {
    cmd := cfg.exe.toString
    args := args.toArray
    cwd := some cfg.root
  }
  return (out.exitCode, out.stderr)

/-- Run one case. -/
def runCase (cfg : Config) (name : String) : IO Outcome := do
  let caseDir := cfg.casesDir / name
  let some cmdText ← readIfExists (caseDir / "cmd")
    | return .fail #[s!"case '{name}' has no 'cmd' file"]

  let pkg := caseDir / "pkg"
  let outDir := cfg.scratch / name / "out1"
  if ← (cfg.scratch / name).pathExists then
    IO.FS.removeDirAll (cfg.scratch / name)
  IO.FS.createDirAll outDir

  let args := parseCmd cmdText pkg outDir
  let (exit, stderr) ← runOnce cfg args
  let published ← snapshotTree outDir

  let expectedDir := caseDir / "expected"

  if cfg.accept then
    IO.FS.createDirAll expectedDir
    IO.FS.writeBinFile (expectedDir / "exit") (toString exit ++ "\n").toUTF8
    IO.FS.writeBinFile (expectedDir / "stderr") stderr.toUTF8
    writeTree (expectedDir / "artifacts") published
    return .accepted

  let mut reasons : Array String := #[]

  -- A case is positive exactly when it is *expected* to succeed. Deriving this
  -- from the expectation rather than the actual exit status means a positive
  -- case that regresses into failing still runs the determinism check and still
  -- reports the artifact mismatch, instead of silently downgrading to a
  -- negative case.
  let expectedExit := (← readIfExists (expectedDir / "exit")).map (·.trimAscii.toString)
  let isPositive := expectedExit == some "0"

  match expectedExit with
  | none => reasons := reasons.push "missing expected/exit"
  | some want =>
    if want != toString exit then
      reasons := reasons.push s!"exit status: expected {want}, got {exit}"

  let wantStderr := (← readIfExists (expectedDir / "stderr")).getD ""
  if wantStderr != stderr then
    reasons := reasons.push
      s!"stderr mismatch:\n--- expected ---\n{wantStderr}--- actual ---\n{stderr}---"

  let wantArtifacts ← snapshotTree (expectedDir / "artifacts")
  if published != wantArtifacts then
    reasons := reasons.push
      s!"artifact mismatch:\n--- expected ---\n{renderTree wantArtifacts}\
--- actual ---\n{renderTree published}---"

  -- A failed run must never publish a manifest or a partially written generated
  -- module. The artifact comparison above would catch this too, but stating it
  -- separately keeps the intent of a negative case explicit and gives a clearer
  -- failure message.
  if !isPositive && !published.isEmpty then
    reasons := reasons.push
      (s!"failed run published {published.size} artifact(s): "
        ++ String.intercalate ", " (published.toList.map (·.1)))

  -- Determinism: a successful run repeated into a clean output directory must
  -- publish byte-identical artifacts.
  if isPositive then
    let outDir2 := cfg.scratch / name / "out2"
    IO.FS.createDirAll outDir2
    let args2 := parseCmd cmdText pkg outDir2
    let (exit2, _) ← runOnce cfg args2
    let published2 ← snapshotTree outDir2
    if exit2 != exit then
      reasons := reasons.push s!"repeat run exit status: expected {exit}, got {exit2}"
    if published2 != published then
      reasons := reasons.push
        s!"repeat run published different bytes:\n--- first ---\n{renderTree published}\
--- second ---\n{renderTree published2}---"

  return if reasons.isEmpty then .pass else .fail reasons

/-- Case directory names in sorted order. -/
def discoverCases (cfg : Config) : IO (Array String) := do
  if !(← cfg.casesDir.pathExists) then return #[]
  let mut names : Array String := #[]
  for entry in ← cfg.casesDir.readDir do
    if ← entry.path.isDir then
      names := names.push entry.fileName
  return names.qsort CJson.utf8Lt

def run (accept : Bool) : IO UInt32 := do
  let root ← IO.currentDir
  let cfg : Config := {
    root
    exe := root / ".lake" / "build" / "bin" / "explicit-lean"
    casesDir := root / "test" / "cases"
    scratch := root / ".lake" / "test-scratch"
    accept
  }

  if !(← cfg.exe.pathExists) then
    IO.eprintln s!"executable not built: {cfg.exe}"
    return 1

  if ← cfg.scratch.pathExists then
    IO.FS.removeDirAll cfg.scratch
  IO.FS.createDirAll cfg.scratch

  -- Unit checks run first: a failure there usually explains any case failures.
  let unitStatus ← ExplicitLean.Unit.run

  let cases ← discoverCases cfg
  let mut failed := if unitStatus == 0 then 0 else 1
  let mut passed := if unitStatus == 0 then 1 else 0
  for name in cases do
    match ← runCase cfg name with
    | .pass =>
      passed := passed + 1
      IO.println s!"ok       {name}"
    | .accepted =>
      passed := passed + 1
      IO.println s!"accepted {name}"
    | .fail reasons =>
      failed := failed + 1
      IO.println s!"FAIL     {name}"
      for r in reasons do
        IO.println (indent r)

  IO.println ""
  if cases.isEmpty then
    IO.println "no cases found"
  -- The unit checks count as one entry alongside the cases.
  IO.println s!"{passed} passed, {failed} failed, {cases.size + 1} total"
  return if failed == 0 then 0 else 1
where
  indent (s : String) : String :=
    String.intercalate "\n" ((s.splitOn "\n").map ("  " ++ ·))

end ExplicitLean.Test

def main (args : List String) : IO UInt32 :=
  ExplicitLean.Test.run (accept := args.contains "--accept")
