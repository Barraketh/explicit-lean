module
prelude

public import Init.Prelude
public import ExplicitLean.SimpEngine.IR
public import ExplicitLean.SimpEngine.Fingerprint

public section

namespace Lean.Meta.Simp.Engine

inductive RuntimeMode where
  | reference
  | record
  | replay
  deriving Inhabited, Repr, BEq

structure RecorderState where
  program : Program := {}
  path : ExecutionPath := {}
  phase : Phase := .pre
  deferred : Option DeferredReason := none
  lastPremiseTerminal : Option PremiseTerminal := none
  simprocs : Array SimprocObservation := #[]
  simpCachePaths : Std.HashMap String ExecutionPath := {}
  dsimpCachePaths : Std.HashMap String ExecutionPath := {}
  pendingMonadSimpPaths : Array PathStep := #[]
  coveredBranches : Array String := #[]
  deriving Inhabited

structure Runtime where
  mode : RuntimeMode
  state : IO.Ref RecorderState

def Runtime.reference : MetaM Runtime := do
  return { mode := .reference, state := ← IO.mkRef {} }

def Runtime.record (initialFingerprint : String) : MetaM Runtime := do
  let state : RecorderState := { program.initialFingerprint := initialFingerprint }
  return { mode := .record, state := ← IO.mkRef state }

def Runtime.replay (program : Program) : MetaM Runtime := do
  return { mode := .replay, state := ← IO.mkRef { program } }

end Lean.Meta.Simp.Engine
