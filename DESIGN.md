# Principled simp cache fork

## Boundary

The fork is confined to `ExplicitLean/SimpTrace/Traversal.lean` and the
recorder's method plumbing in `ExplicitLean/SimpTrace/Recorder.lean`.  The
stock `Lean.Meta.Simp.State.cache` remains the execution cache type, but its
entries are mirrored atomically in a recorder-owned cache carrying the exact
root-relative event sequence.  No matcher is rerun on a hit, and no proof or
term is serialized.  A hit returns the stock `Simp.Result` and re-roots only
the term-free event metadata at the caller's position.

## Ported surface

`cacheResult`, the cache lookup at the start of `simpLoop`, and all cache
lifecycle wrappers (`withFreshCache`, `withPreservedCache`, and the staged
switch behavior) are copied into the fork.  `simpLoopT` remains the
position-threaded copy of upstream `simpLoop`; its reduction, pre, step, and
post branches all use the same insertion point and `Result.cache` gate.
Opaque nested `simp` calls used by the built-in conditional simprocs are
routed through a recorder-local controlled entry point so their nested cache
and event frame are the same fork.

## Types and atomicity

`CacheEntry` contains `{ result : Simp.Result, events : Array Event }`.
The recorder cache is the `TraceState.cache : SExprMap CacheEntry`; its
`map₁`/`map₂`/`stage₁` fields are the staged frame, so no second ad-hoc frame
type can diverge from stock `SExprMap`.  `cacheResultT` computes the complete
event slice before updating both the stock `State.cache` and the recorder
mirror.  Event slices are normalized once by stripping the invocation root;
hits append the same slice after re-rooting.  The two state updates are
adjacent in the same `SimpM` operation and no partial entry is published.

## Lifecycle map

* normal insertion/hit: `simpLoopT` lookup then result insertion;
* `cache := false`: no entry, while result/proofs/counters are untouched;
* `withFreshCache`: save and restore both cache layers;
* `withPreservedCache`: switch the linear stage and preserve both map layers;
* new lemmas/context changes: use the exact upstream fresh-cache scope;
* discharger and recursive entry: preserve/switch frames independently;
* nested `reduceIte`/`reduceDIte` and `dsimp`: enter the same fork, with a
  nested event frame and no duplicate registration or counters.

## Parity tests

The focused fixture covers first compute/repeated hit, `cache := false`, a
contextual fresh-cache scope, recursive discharging, nested conditional
simprocs, and position re-rooting.  `T20IteSimproc` additionally covers
applied/nested `ite` and `dite` plus `dsimp` conditional paths.  The seven-
module capture gate remains an integration check owned by the coordinator;
this isolated worktree has no completed Mathlib `.olean` cache, so it is not
claimed here.
