import ExplicitLean.Diagnostic

/-!
# Pinned toolchain validation

`ROOT` must be an already-resolved Lake package whose `lean-toolchain` and
`lake-manifest.json` select the exact pinned Lean and Mathlib releases. The
caller runs `explicit-lean` in the environment produced by `lake env` for that
package, with every imported artifact already built. v0 neither downloads
dependencies nor invokes a build.
-/

namespace ExplicitLean

/-- The Lean version this compiler is pinned to.

This is read from the running binary rather than written down as a constant. The
compiler is built by the toolchain it validates, so the running version is the
authority; a separate literal could only ever drift out of agreement with
`lean-toolchain` on an upgrade and then reject the correct package. -/
def pinnedLeanVersion : String :=
  s!"{Lean.version.major}.{Lean.version.minor}.{Lean.version.patch}"

/-- Read the `lean-toolchain` pin declared by a package root. -/
def readToolchainPin (packageRoot : System.FilePath) :
    IO (Except Diagnostic String) := do
  let path := packageRoot / "lean-toolchain"
  if !(← path.pathExists) then
    return .error {
      code := "TOOLCHAIN-PIN-MISSING"
      message := "package root has no 'lean-toolchain'; it must be a resolved Lake package"
      phase := .cli
    }
  let contents ← IO.FS.readFile path
  return .ok contents.trimAscii.toString

/-- Check that the package root pins the same Lean release the compiler runs
under. The pin file holds a toolchain name such as `leanprover/lean4:v4.32.2`. -/
def validateToolchainPin (packageRoot : System.FilePath) :
    IO (Except Diagnostic Unit) := do
  match ← readToolchainPin packageRoot with
  | .error d => return .error d
  | .ok pin =>
    let expected := s!"leanprover/lean4:v{pinnedLeanVersion}"
    if pin == expected then
      return .ok ()
    else
      return .error {
        code := "TOOLCHAIN-PIN-MISMATCH"
        message := s!"package root pins '{pin}', expected '{expected}'"
        phase := .cli
      }

/-- Check that the package root has a resolved Lake manifest.

v0 does not resolve dependencies itself, so a missing manifest means the caller
has not prepared the environment this command requires. -/
def validateLakeManifest (packageRoot : System.FilePath) :
    IO (Except Diagnostic Unit) := do
  let path := packageRoot / "lake-manifest.json"
  if ← path.pathExists then
    return .ok ()
  else
    return .error {
      code := "LAKE-MANIFEST-MISSING"
      message := "package root has no 'lake-manifest.json'; run 'lake update' and build before compiling"
      phase := .cli
    }

/-- Validate the complete prebuilt-environment contract for a package root.

Every failure is collected rather than returning at the first, so one run
reports every way the environment is unprepared. -/
def validateEnvironment (packageRoot : System.FilePath) :
    IO (Array Diagnostic) := do
  let mut ds : Array Diagnostic := #[]
  if let .error d ← validateToolchainPin packageRoot then
    ds := ds.push d
  if let .error d ← validateLakeManifest packageRoot then
    ds := ds.push d
  return ds

end ExplicitLean
