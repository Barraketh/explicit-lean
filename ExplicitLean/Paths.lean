import ExplicitLean.Diagnostic

/-!
# Path and module-name handling

v0 has no source-directory remapping: the lexical path of the source file
relative to the package root must be the slash-separated components of the
module name followed by `.lean`. Module `A.B` is read from `ROOT/A/B.lean`.

Symlinks are resolved for access, but stable paths are slash-separated lexical
paths relative to their declared root. Inputs that escape a root are rejected.
-/

namespace ExplicitLean

/-- A Lean module name as its components from root to leaf. v0 accepts only
nonanonymous names whose components are all string components. -/
abbrev ModuleName := Array String

namespace ModuleName

/-- Parse a dotted module name. Returns `none` when the name is anonymous or has
an empty component. -/
def parse (s : String) : Option ModuleName :=
  let parts := s.splitOn "."
  if parts.isEmpty || parts.any (·.isEmpty) then none
  else some parts.toArray

def toString (m : ModuleName) : String :=
  String.intercalate "." m.toList

/-- The lexical path of the source file for this module, relative to the package
root, as slash-separated components. -/
def sourceRelPath (m : ModuleName) : String :=
  String.intercalate "/" m.toList ++ ".lean"

instance : ToString ModuleName := ⟨toString⟩

end ModuleName

/-- Split a filesystem path into components, discarding `.` and empty segments
produced by redundant or trailing separators. -/
private def pathComponents (p : System.FilePath) : Array String :=
  (p.toString.splitOn "/").toArray.filter fun c => !c.isEmpty && c != "."

/-- Resolve a path for access, following symlinks.

`IO.FS.realPath` requires the path to exist, which is what we want for the roots
and the source file: a nonexistent input is a path error.

The error carries no path text. Diagnostics must contain no absolute paths, and
at this point the input has not yet been shown to lie beneath any root, so there
is no package-relative path to report. The caller's diagnostic names the failing
option, which identifies the input unambiguously. -/
def resolveExisting (p : System.FilePath) : IO (Except Unit System.FilePath) := do
  if ← p.pathExists then
    return .ok (← IO.FS.realPath p)
  else
    return .error ()

/-- The slash-separated lexical path of `path` relative to `root`, or `none` when
`path` is not beneath `root`.

Both arguments must already be resolved absolute paths, so this is a pure prefix
check on components: symlink resolution has removed the ways a lexical prefix
could lie about containment. -/
def relativeTo (root path : System.FilePath) : Option String :=
  let rootParts := pathComponents root
  let pathParts := pathComponents path
  if pathParts.size < rootParts.size then none
  else if rootParts.toList != (pathParts.toList.take rootParts.size) then none
  else
    let rest := pathParts.toList.drop rootParts.size
    if rest.isEmpty then none else some (String.intercalate "/" rest)

end ExplicitLean
