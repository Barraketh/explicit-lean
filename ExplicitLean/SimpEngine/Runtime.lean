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
  lastPremiseTerminal : Option PremiseTerminal := none
  congruenceInvocationOrdinal : Nat := 0
  simpInvocationOrdinal : Nat := 0
  dsimpInvocationOrdinal : Nat := 0
  simpStepOrdinal : Nat := 0
  pendingMonadSimpPaths : Array PathStep := #[]
  expectedPremiseTerminal : Option PremiseTerminal := none
  deriving Inhabited

/-- Observations of work that actually ran.  Unlike the logical recorder
    cursor, these values do not roll back when a speculative rewrite or
    congruence candidate fails. -/
structure PassiveObservations where
  deferred : Option DeferredReason := none
  simprocs : Array SimprocObservation := #[]
  coveredBranches : Array String := #[]
  deriving Inhabited

structure CacheProvenance where
  /-- Provenance for Lean's staged `Simp.Cache`; it switches and restores with the cache. -/
  simpSources : SExprMap (ExecutionPath × Nat) := {}
  /-- Provenance for the `State.dsimpCache` value outside the active dsimp traversal. -/
  dsimpStateSources : ExprStructMap (ExecutionPath × Nat) := {}
  /-- Provenance for the cache threaded locally through the active dsimp traversal. -/
  dsimpSources : ExprStructMap (ExecutionPath × Nat) := {}
  /-- Append-only producer paths give cache entries stable execution ordinals.
      The cache key itself remains authoritative: expression fingerprints are
      local-context-relative and may change after a binder scope closes. -/
  simpOrder : Array ExecutionPath := #[]
  dsimpOrder : Array ExecutionPath := #[]
  deriving Inhabited

structure Runtime where
  mode : RuntimeMode
  state : IO.Ref RecorderState
  observations : IO.Ref PassiveObservations
  /-- Cache provenance is operational simplifier state, not logical trace
      state.  In particular, Lean's stage-1 cache insertions survive exception
      backtracking, so this reference must not be overwritten by recorder
      snapshots for failed theorem or congruence attempts. -/
  cacheProvenance : IO.Ref CacheProvenance
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
    observations := ← IO.mkRef {}
    cacheProvenance := ← IO.mkRef {}
    fingerprintCache := ← IO.mkRef {}
  }

def Runtime.record (initialFingerprint : String) : MetaM Runtime := do
  let state : RecorderState := { program.initialFingerprint := initialFingerprint }
  return {
    mode := .record
    state := ← IO.mkRef state
    observations := ← IO.mkRef {}
    cacheProvenance := ← IO.mkRef {}
    fingerprintCache := ← IO.mkRef {}
  }

def Runtime.replay (program : Program) (ruleContext : Option Simp.Context := none) : MetaM Runtime := do
  return {
    mode := .replay
    state := ← IO.mkRef { program }
    observations := ← IO.mkRef {}
    cacheProvenance := ← IO.mkRef {}
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
