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
  /-- Append-only producer paths give cache entries stable execution ordinals.
      The cache key itself remains authoritative: expression fingerprints are
      local-context-relative and may change after a binder scope closes. -/
  simpReplayCache : Array ExecutionPath := #[]
  dsimpReplayCache : Array ExecutionPath := #[]
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
  /-- Ephemeral expression fingerprints shared by one engine execution. Simproc
      candidate loops commonly present the same expression to many candidates;
      recomputing its proof-insensitive DAG hash for every observation is both
      redundant and unbounded in practice. -/
  fingerprintCache : IO.Ref (ExprStructMap String)
  ruleContext : Option Simp.Context := none

def Runtime.reference : MetaM Runtime := do
  return {
    mode := .reference
    state := ← IO.mkRef {}
    fingerprintCache := ← IO.mkRef {}
  }

def Runtime.record (initialFingerprint : String) : MetaM Runtime := do
  let state : RecorderState := { program.initialFingerprint := initialFingerprint }
  return {
    mode := .record
    state := ← IO.mkRef state
    fingerprintCache := ← IO.mkRef {}
  }

def Runtime.replay (program : Program) (ruleContext : Option Simp.Context := none) : MetaM Runtime := do
  return {
    mode := .replay
    state := ← IO.mkRef { program }
    fingerprintCache := ← IO.mkRef {}
    ruleContext
  }

/-- Fingerprint an instantiated expression once per engine execution. The
    cache is deliberately outside `RecorderState`: speculative simplifier
    state rollback does not invalidate a pure fingerprint. -/
def Runtime.cachedFingerprintHash (runtime : Runtime) (expression : Expr) : MetaM String := do
  let expression ← instantiateMVars expression
  if let some fingerprint := (← runtime.fingerprintCache.get).get? { val := expression } then
    return fingerprint
  let fingerprint ← exprFingerprintHash expression
  runtime.fingerprintCache.modify fun cache => cache.insert { val := expression } fingerprint
  return fingerprint

end Lean.Meta.Simp.Engine
