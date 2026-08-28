# Explicit Lean roadmap

## Goal

Explicit Lean turns successful `simp` and `simp only` executions into stable
Lean source whose meaning is explicit. A certificate records the operations and
control-flow choices that the pinned simplifier committed; replay consumes that
program without ambient simp theorems, congruence rules, simproc registries, or
dischargers.

The current scope is `simp` and `simp only`. `simpa`, `simp_all`, `simp_rw`, and
`rw` are later projects. The normative engine contract is in
[SIMP_ENGINE_COVERAGE.md](SIMP_ENGINE_COVERAGE.md), and the corpus evidence and
per-simproc decisions are in [simprocs.md](simprocs.md).

## Current design

The implementation is a pinned fork of Lean 4.32.2's simplifier at commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`. It has three modes:

- reference mode follows upstream behavior;
- recording mode emits schema-27 programs, structural witnesses, subject
  transport, and rollback-aware committed simproc traces; and
- replay mode consumes those programs in the same traversal.

Recording is checked against a separate upstream execution before its result is
accepted. The comparison covers the result expression, proof presence and
proposition, cache flag, and the complete operational `Simp.State`: step count,
simp/congruence/dsimp caches, used theorem origins, and diagnostics. Proof terms
inside state are compared modulo proof irrelevance because independent custom
discharger runs may generate extension-local private proof names. Fresh local,
expression-metavariable, and universe-metavariable identities are canonicalized.

The certificate never treats a result proof as a substitute for an unidentified
operation. Unsupported result-bearing simprocs and arbitrary custom dischargers
make the containing subject explicitly deferred.

### Simproc boundary

Every invoked candidate is observed with its declaration, phase, registry set,
procedure kind, disposition, execution flag, extra-argument count, proof/cache
facts, fingerprints, and bounded result tree/DAG size. The certificate trace is
part of rollback-able recorder state, so calls made only by failed speculative
candidates do not appear in histograms or replay validation. Append-only runtime
observations remain conservative diagnostics and may still force deferral when
an unmodelled candidate ran before rollback.

A supported result is represented as a `semanticSimproc` fold. The fold records
ordered candidates and their actual procedure protocol, but the declaration
name is provenance rather than replay authority. Replay reconstructs the result
from a closed semantic descriptor, verifies all fingerprints and protocol
fields, composes proofs/cache flags exactly, and requires a matching committed
observation. Observations validate authority; they never create it.

The supported protocol is intentionally closed:

| declaration | procedure protocol | semantic operation |
| --- | --- | --- |
| `Fin.isValue` | dsimproc, post registry, `done` | range guard or canonical modulo literal |
| `reduceIte` | simproc, pre registry, `visit` | nested condition program and selected input branch |
| `Nat.reduceAdd`, `Nat.reduceDiv` | dsimproc, post registry, `done` | canonical Nat binary value |
| `reduceDIte` | simproc, pre registry, `visit` | nested condition program, selected dependent branch, head beta |
| `Int.reduceNeg` | dsimproc, post registry, `done` | syntax guard or canonical negative literal |
| `reduceCtorEq` | simproc, post registry, `done` | constructor disjointness and no-confusion proof |
| `Matrix.cons_val` | dsimproc, post registry, `continue some` | checked vector spine/index lookup |
| `Fin.reduceFinMk` | dsimproc, post registry, `done` | canonical `Fin.mk` via a checked Nat evaluation trace |
| `ExistsAndEq.existsAndEq` | simproc, pre registry, `visit` | checked route and explicit equivalence proof |

The `fieldEq` simproc is not replay authority yet. A separate Mathlib-dependent
audit library runs a source-faithful shadow from the saved pre-state, records the
four discharger strategies and recursive calls, and requires exact authoritative
versus shadow result, `Simp.State`, and tracked metavariable/message effects. The
hook restores the complete authoritative Core/Meta post-state; its payload is
diagnostic only.

## Completed work

1. The upstream source surface and semantic helper implementations are pinned
   by hashes.
2. The structural recorder covers simplifier recursion, reductions, rewrite
   selection and failed attempts, congruence, caches, nested discharge/ground
   programs, dsimp traversal, and goal/hypothesis transport.
3. Closed replay validates paths, fingerprints, provenance, assignments,
   dispositions, final state, and exact program consumption.
4. Certificate source round-trips as compact schema-27 JSON embedded in Lean
   strings and materializes at original tactic sites.
5. Syntax-aware local and cloud harnesses inventory complete Mathlib modules,
   classify every occurrence, and support deterministic sharding and strict
   reduction.
6. A full pre-schema-27 closure run at the pinned Mathlib commit classified all
   83,425 inventoried occurrences in 6,319 modules with zero harness failures.
   This is a historical baseline, not evidence that the current schema-27 tree
   has completed a fresh full-corpus closure.
7. A full rollback-aware record-only census measured 12,731 committed
   result-bearing simproc calls. The top ten account for 12,049 (94.6%).
8. Focused semantic gates cover the nine replay-supported declarations/families
   above, exact fold/observation linkage, source round trips for constructor and
   existential equality slices, and single-field mutation rejection.

## Acceptance gates

`Experiment/run.sh` is the commit gate. It builds the generic and Mathlib-audit
libraries and runs:

- source pinning and upstream/fork reference equivalence;
- focused simproc-entry and semantic interpreter/fold differentials;
- passive `fieldEq` shadow parity;
- constructor and existential source round trips;
- the 54-row implementation-to-IR observer audit and reviewed-source hash lock;
- exact recording parity, closed replay, and mutation rejection;
- the representative complete-module source materializer; and
- cloud reducer and Vast scheduler/harness mutation tests.

Cloud production commands refuse a dirty worktree unless `--allow-dirty` is
explicitly supplied. Record-only runs reuse the syntax inventory across
certificate schema changes but validate report schema, repository commit,
Mathlib commit, and all harness inputs.

## Remaining work

1. Run a fresh full-Mathlib schema-27 closure and compare its terminal
   classifications with the historical baseline.
2. Build a memory-safe, resumable full-corpus `fieldEq` audit. The discarded
   whole-module prototype could exceed 12 GB for a module and was not suitable
   as a production census. Use occurrence isolation or bounded shards before
   choosing its semantic IR.
3. Extend semantic support only from measured committed calls. For each new
   declaration, pin its actual kind/registry/disposition protocol, model any
   state or meta effects, add a closed interpreter, prove observation/fold
   correspondence, and reject mutations.
4. Reassess the four `ExistsAndEq` deferrals. Three require explicit
   certificate effects for procedure-created metavariable assignments. The
   fourth uses the post registry; supporting both registries would require
   binding that provenance into observation validation.
5. After simproc closure is current, begin the separate tactic families
   (`simpa`, `simp_all`, `simp_rw`, and `rw`).

Git history is the record of superseded schemas and experiments; this document
describes only the current design, evidence, and next decisions.
