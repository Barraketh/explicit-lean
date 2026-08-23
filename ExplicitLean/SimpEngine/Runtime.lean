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
  eventCursor : Nat := 0
  structuralCursor : Nat := 0
  path : ExecutionPath := {}
  phase : Phase := .pre
  phaseInvocationOrdinal : Nat := 0
  currentPhaseInvocationOrdinal : Nat := 0
  deferred : Option DeferredReason := none
  lastPremiseTerminal : Option PremiseTerminal := none
  simprocs : Array SimprocObservation := #[]
  /-- Provenance for Lean's staged `Simp.Cache`; it must switch and restore with the cache. -/
  simpCacheSources : SExprMap (ExecutionPath × Nat) := {}
  /-- Provenance for the `State.dsimpCache` value outside the active dsimp traversal. -/
  dsimpStateCacheSources : ExprStructMap (ExecutionPath × Nat) := {}
  /-- Provenance for the cache threaded locally through the active dsimp traversal. -/
  dsimpCacheSources : ExprStructMap (ExecutionPath × Nat) := {}
  /-- Append-only registries used to resolve exact producer ordinals during replay. -/
  simpReplayCache : Array (ExecutionPath × String × Simp.Result) := #[]
  dsimpReplayCache : Array (ExecutionPath × String × Expr) := #[]
  congruenceInvocationOrdinal : Nat := 0
  simpInvocationOrdinal : Nat := 0
  dsimpInvocationOrdinal : Nat := 0
  simpStepOrdinal : Nat := 0
  pendingMonadSimpPaths : Array PathStep := #[]
  expectedPremiseTerminal : Option PremiseTerminal := none
  coveredBranches : Array String := #[]
  deriving Inhabited

structure Runtime where
  mode : RuntimeMode
  state : IO.Ref RecorderState
  ruleContext : Option Simp.Context := none

def Runtime.reference : MetaM Runtime := do
  return { mode := .reference, state := ← IO.mkRef {} }

def Runtime.record (initialFingerprint : String) : MetaM Runtime := do
  let state : RecorderState := { program.initialFingerprint := initialFingerprint }
  return { mode := .record, state := ← IO.mkRef state }

def Runtime.replay (program : Program) (ruleContext : Option Simp.Context := none) : MetaM Runtime := do
  return { mode := .replay, state := ← IO.mkRef { program }, ruleContext }

end Lean.Meta.Simp.Engine
