import ExplicitLean.Paths

/-!
# Atomic artifact publication

For source module `A.B` the command publishes these
artifact-convention-set-1 paths, and only after every stage succeeds:

```text
OUT/Explicit/A/B.lean
OUT/Explicit/A/B.manifest.ndjson
OUT/Explicit/A/B.provenance/   # only when sidecars exist
```

Temporary files use an implementation-owned directory outside the final artifact
paths and never affect bytes or fingerprints. A failed run leaves any previously
published successful artifacts unchanged.
-/

namespace ExplicitLean

/-- The generated module name for a source module, under
[L2 module mapping](../LOWERING.md#l2-module-mapping): `A.B` maps to
`Explicit.A.B`. -/
def generatedModuleName (m : ModuleName) : ModuleName :=
  #["Explicit"] ++ m

/-- The set of bytes to publish for one run. Paths are relative to the output
root. -/
structure Artifacts where
  /-- Generated module bytes, published at `OUT/Explicit/A/B.lean`. -/
  generatedSource : String
  /-- Manifest bytes, published at `OUT/Explicit/A/B.manifest.ndjson`. -/
  manifest : String
  /-- Provenance sidecars as (name, bytes), published beneath
  `OUT/Explicit/A/B.provenance/`. The directory is created only when this is
  nonempty. -/
  provenance : Array (String × String) := #[]
  deriving Inhabited

/-- The staging directory for a run: implementation-owned, outside the final
artifact paths, and removed when the run ends. -/
private def stagingDir (outputRoot : System.FilePath) : System.FilePath :=
  outputRoot / ".explicit-lean-staging"

/-- The directory holding the published artifacts for `m`, i.e.
`OUT/Explicit/A` for module `A.B`. -/
private def publishDir (outputRoot : System.FilePath) (m : ModuleName) : System.FilePath :=
  Array.foldl (init := outputRoot) (fun acc (c : String) => acc / c) (generatedModuleName m).pop

/-- The base name of the published artifacts, i.e. `B` for module `A.B`.

`generatedModuleName` prepends a component, so the array is nonempty for any
`m` and `back!` cannot fail. -/
private def publishBase (m : ModuleName) : String :=
  (generatedModuleName m).back!

/-- Write `contents` to `path` as exact UTF-8 bytes with no added trailing
newline. -/
private def writeExact (path : System.FilePath) (contents : String) : IO Unit := do
  IO.FS.writeBinFile path contents.toUTF8

/-- Recursively copy a staged directory into place. -/
private partial def copyDir (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for entry in ← src.readDir do
    let target := dst / entry.fileName
    if (← entry.path.isDir) then
      copyDir entry.path target
    else
      IO.FS.writeBinFile target (← IO.FS.readBinFile entry.path)

/-- Publish `artifacts` for source module `m` beneath `outputRoot`.

Every artifact is written into a staging directory first, then moved into its
final path. `IO.FS.rename` within one filesystem is atomic, so a reader sees
either the previous file or the complete new one, never a partial write. The
staging directory is inside `outputRoot` to keep the rename on one filesystem,
and is removed on both the success and failure paths.

This does not by itself make the multi-file publication a single atomic
transaction; the ordering guarantee v0 requires is that nothing is published
until every stage has succeeded, which the caller provides by constructing
`Artifacts` only after all checks pass. -/
def publish (outputRoot : System.FilePath) (m : ModuleName) (artifacts : Artifacts) :
    IO Unit := do
  let staging := stagingDir outputRoot
  -- A staging directory left behind by an interrupted earlier run must not leak
  -- into this one.
  if ← staging.pathExists then
    IO.FS.removeDirAll staging
  IO.FS.createDirAll staging
  tryFinally (publishStaged staging outputRoot m artifacts) do
    if ← staging.pathExists then
      IO.FS.removeDirAll staging
where
  /-- Stage every artifact, then move each into its final path. -/
  publishStaged (staging outputRoot : System.FilePath) (m : ModuleName)
      (artifacts : Artifacts) : IO Unit := do
    let base := publishBase m
    let dir := publishDir outputRoot m
    IO.FS.createDirAll dir

    let stagedSource := staging / (base ++ ".lean")
    let stagedManifest := staging / (base ++ ".manifest.ndjson")
    writeExact stagedSource artifacts.generatedSource
    writeExact stagedManifest artifacts.manifest

    if !artifacts.provenance.isEmpty then
      let stagedProv := staging / (base ++ ".provenance")
      IO.FS.createDirAll stagedProv
      for (name, contents) in artifacts.provenance do
        writeExact (stagedProv / name) contents

    -- Move the staged files into place. Staging every byte first means a
    -- failure while writing leaves previously published artifacts untouched.
    IO.FS.rename stagedSource (dir / (base ++ ".lean"))
    IO.FS.rename stagedManifest (dir / (base ++ ".manifest.ndjson"))
    let finalProv := dir / (base ++ ".provenance")
    if !artifacts.provenance.isEmpty then
      -- `rename` onto an existing nonempty directory fails, so replace it.
      if ← finalProv.pathExists then
        IO.FS.removeDirAll finalProv
      -- Rename first; fall back to a copy when the staging directory and the
      -- publish directory turn out to be on different filesystems.
      try
        IO.FS.rename (staging / (base ++ ".provenance")) finalProv
      catch _ =>
        copyDir (staging / (base ++ ".provenance")) finalProv
    else if ← finalProv.pathExists then
      -- The provenance directory exists only when sidecars do. Leaving one
      -- behind from an earlier run would make the published tree depend on what
      -- was published before it.
      IO.FS.removeDirAll finalProv

end ExplicitLean
