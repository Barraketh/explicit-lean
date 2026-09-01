import Lean.Elab.Frontend

open Lean

namespace ExplicitLean.SimpEngine

/-- The effective `leanOptions` from the pinned Mathlib package.

Keep this list synchronized with `mathlibLeanOptions` in Mathlib's
`lakefile.lean`.  Inventory and scope parsing use exactly these options when
they elaborate commands only to recover parser context. -/
def mathlibPackageOptions : Options :=
  ({} : Options)
    |>.set `pp.unicode.fun true
    |>.set `autoImplicit false
    |>.set `maxSynthPendingDepth (3 : Nat)
    |>.set `weak.linter.mathlibStandardSet true
    |>.set `weak.linter.style.header true
    |>.set `weak.linter.checkInitImports true
    |>.set `weak.linter.allScriptsDocumented true
    |>.set `weak.linter.pythonStyle true
    |>.set `weak.linter.style.longFile (1500 : Nat)

/-- Mathlib's package options with the command-line frontend's async default.

Lean's command-line driver also enables `internal.cmdlineSnapshots`, a metadata
compaction mode that deliberately discards the command syntax these parsers
must collect.  Inventory and scope therefore retain its API default `false`;
this changes snapshot storage, not command elaboration. -/
def mathlibParserOptions : Options :=
  Elab.async.set mathlibPackageOptions true

/-- Mathlib package options plus the controls used while compiling temporary
oracle and command-audit sources.  These additions deliberately enable async
elaboration, remove the heartbeat limit, and suppress diagnostics introduced
by source overlays.  Inventory and scope parsing must use
`mathlibParserOptions` instead. -/
def verificationFrontendOptions : Options :=
  mathlibParserOptions
    |>.set `weak.linter.unusedVariables false
    |>.set `weak.linter.unusedSimpArgs false
    |>.set `weak.linter.unreachableTactic false
    |>.set `maxHeartbeats (0 : Nat)

end ExplicitLean.SimpEngine
