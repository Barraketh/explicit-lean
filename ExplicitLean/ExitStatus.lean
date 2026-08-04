import ExplicitLean.Diagnostic

/-!
# Exit statuses

`0` success, `2` command-line or path errors, `3` source parsing or elaboration
failure, `4` a diagnosed unsupported feature, `5` lowering/grammar/audit/
verification/manifest failure, `70` internal compiler error.

When several diagnostics exist, the status with greatest severity in the order
`70`, `5`, `4`, `3`, `2` wins.
-/

namespace ExplicitLean

/-- A failure classification. v0 never needs to represent success here; a run
with no diagnostics exits `0`. -/
inductive Failure where
  | cli
  | source
  | unsupported
  | check
  | internal
  deriving Inhabited, Repr, BEq, DecidableEq

namespace Failure

def code : Failure → UInt32
  | .cli => 2
  | .source => 3
  | .unsupported => 4
  | .check => 5
  | .internal => 70

/-- Rank in the documented severity order; greater wins. -/
def severityRank : Failure → Nat
  | .cli => 0
  | .source => 1
  | .unsupported => 2
  | .check => 3
  | .internal => 4

/-- The failure a diagnostic in this phase represents.

`admission` is the phase that diagnoses an unsupported feature (`4`).
`lowering`, `grammar`, `audit`, `verification`, and `manifest` are the check
phases (`5`). `capture` reports failures observing a source elaboration that
itself succeeded, which is a compiler-side condition rather than a source error,
so it is classified as internal. -/
def ofPhase : Phase → Failure
  | .cli => .cli
  | .source => .source
  | .capture => .internal
  | .admission => .unsupported
  | .lowering | .grammar | .audit | .verification | .manifest => .check
  | .internal => .internal

end Failure

/-- The exit status for a completed run: `0` when there are no diagnostics,
otherwise the greatest-severity failure among them. -/
def exitStatus (ds : Array Diagnostic) : UInt32 :=
  match ds.foldl (init := none) fun acc d =>
      let f := Failure.ofPhase d.phase
      match acc with
      | none => some f
      | some g => some (if f.severityRank > g.severityRank then f else g) with
  | none => 0
  | some f => f.code

end ExplicitLean
