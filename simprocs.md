# Semantic simproc design

## Evidence and rule

A simproc declaration is opaque executable code. Explicit Lean may record its
name as provenance, but replay must represent what the call established and may
not invoke the declaration or consult an ambient registry.

The measurements below come from the full pinned Mathlib checkout at commit
`905b95818eb32af7874a58b427f50c1711a5e96c`, with Lean 4.32.2 commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`. The frozen record-only report is
the local output
`.lake/simproc-hist-committed-record-only/final/simp-engine-closure.json`
(SHA-256 `48a23b2661e5c8f72daadb8a4051521547e30f02bcca2f10a376abe6f8ff04ac`).
The locked source manifests and the aggregate table below are versioned; the
large shard workspace is not a test-time dependency.

That census used the rollback-aware committed trace. It excludes calls made
only by failed speculative candidates and ranks only committed result-bearing
calls (`done`, `visit`, and `continue some`). Executed `continue none` calls are
still recorded for safety but have no result term and do not enter this table.
The census contains 12,731 result-bearing calls across 55 declarations; the top
ten contain 12,049 (94.6%).

| rank | simproc | committed results | changed | source occurrences / modules | tree mean / p90 / max | DAG mean / p90 / max | disposition |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | --- |
| 1 | `Fin.isValue` | 4,084 | 6 | 878 / 223 | 73.6 / 111 / 1,323 | 30.7 / 42 / 108 | `done` |
| 2 | `reduceIte` | 2,648 | 2,648 | 1,467 / 497 | 308.7 / 293 / 121,159 | 41.6 / 109 / 572 | `visit` |
| 3 | `Nat.reduceAdd` | 1,817 | 1,817 | 749 / 252 | 9 / 9 / 9 | 8 / 8 / 8 | `done` |
| 4 | `reduceDIte` | 1,225 | 1,225 | 796 / 293 | 3,074.0 / 4,037 / 320,993 | 106.5 / 258 / 636 | `visit` |
| 5 | `Int.reduceNeg` | 721 | 5 | 501 / 162 | 23.5 / 45 / 211 | 18.6 / 36 / 62 | `done` |
| 6 | `reduceCtorEq` | 481 | 481 | 326 / 147 | 1 / 1 / 1 | 1 / 1 / 1 | `done` |
| 7 | `fieldEq` | 384 | 284 | 227 / 113 | 888.7 / 1,071 / 136,835 | 95.8 / 209 / 600 | `visit` |
| 8 | `Matrix.cons_val` | 304 | 304 | 44 / 19 | 1,433.1 / 5,189 / 21,275 | 95.1 / 273 / 449 | `continue some` |
| 9 | `Fin.reduceFinMk` | 291 | 291 | 76 / 23 | 41 / 41 / 41 | 23.3 / 24 / 24 | `done` |
| 10 | `ExistsAndEq.existsAndEq` | 94 | 94 | 77 / 65 | 234.6 / 335 / 6,375 | 52.6 / 88 / 309 | `visit` |

A source occurrence is an instrumented `simp` site whose committed trace
contains at least one result from that simproc. One site may execute repeatedly,
so call counts exceed source-site counts.

Tree size expands sharing; DAG size counts structurally distinct expression
nodes. The gap for `reduceDIte` and `Matrix.cons_val` is direct evidence that a
descriptor should point into input structure instead of serializing the output
tree. Sizes exclude equality proofs: `reduceCtorEq` returns the one-node term
`False`, but its proof still requires explicit no-confusion semantics.

## Common schema-27 representation

Every call records its actual kind, pre/post registry provenance, set index,
phase and invocation ordinal, extra arguments, disposition, proof/cache facts,
input/output fingerprints, execution flag, and optional bounded tree/DAG size.

A replayable call becomes a candidate in an ordered `SimprocFold`. The candidate
contains a closed semantic descriptor and checked dependency references. Replay
requires the declaration's pinned kind/registry/disposition protocol,
reconstructs the result without running the simproc, checks all fingerprints,
and matches the fold field-for-field and in order against the committed trace.
If an earlier result-bearing candidate is unsupported, the whole registry fold
is deferred; replay cannot skip it and take credit for a later candidate.

Dependency terms are deliberately restricted to input subterms, locals with
context/type/value fingerprints, literals, and named declaration applications
with explicit universes. Semantic derivation and interpretation restore saved
meta-state, perform no ambient instance search, and reject dependencies that
cannot be represented in this grammar.

## Top-ten decisions

### 1. `Fin.isValue` — implemented

The high call count is mostly semantically meaningful control flow despite only
six changed outputs: its `done` result tells the simplifier that a Fin literal is
already canonical. The interpreter therefore models both branches.

- In-range values record a `finLiteralInRange` guard and reproduce the unchanged
  result/disposition.
- Out-of-range values record a `finLiteralModulo` derivation and reconstruct the
  canonical literal.
- Modulus/source views and the `OfNat (Fin n)` witness must come from checked
  input paths and pinned standard instances.

Rewriting the 878 source sites would be disproportionate and would still need
to preserve the terminating guard behavior, so semantic replay is the natural
representation.

### 2. `reduceIte` — implemented

The result is a selected input branch, while most measured tree size is shared
structure. The descriptor records the condition and branch input paths plus a
scoped nested program that simplifies the condition. Replay shares the outer
simp state, verifies the Boolean terminal, selects the recorded branch, and
constructs the fixed `ite` proof. Extra arguments are re-applied and checked.

### 3. `Nat.reduceAdd` — implemented with `Nat.reduceDiv`

Every result is the same tiny canonical numeral shape, so a compact value trace
is preferable to either source rewriting or term serialization. `natBinary`
records the operator, operand values/views, result, and standard operator
instance. Replay recomputes the arithmetic and constructs the literal. The same
interpreter covers measured `Nat.reduceDiv` calls outside the top ten.

### 4. `reduceDIte` — implemented

The very large tree/DAG ratio rules out output-term serialization. This is the
dependent analogue of `reduceIte`: replay runs the scoped condition program,
constructs the proposition proof, applies the selected dependent branch, checks
the explicit head-beta witness, and constructs the fixed equality proof.

### 5. `Int.reduceNeg` — implemented

The implementation has two distinct semantics.

- The unchanged negative-`OfNat` syntax guard is instance-insensitive and
  records the exact inspected argument path.
- The changing literal branch records magnitude/result plus the outer and inner
  `Neg Int` and `OfNat Int` witnesses, which must be the pinned standard
  instances.

Modelling both branches is simpler and more faithful than rewriting 501 source
sites to reproduce the terminating guard.

### 6. `reduceCtorEq` — implemented

The result term is just `False`, but the proof is the operation. The descriptor
records checked constructor views, inductive identity and constructor indices,
and the exact `ctorIdx`, `noConfusion`, and equality-to-false declarations.
Replay validates the views and constructs the no-confusion proof directly.

The focused source slice contains 109 `simp` occurrences in four complete
modules. On schema 27, 67 occurrences materialize across 73 replay executions;
42 remain deferred for unrelated operations. All 41 committed
`reduceCtorEq` results have matching constructor-disjoint candidates.

### 7. `fieldEq` — audit implemented; replay design pending

`fieldEq` is the only top-ten declaration not yet replay authority. Its outputs
are moderately large and proof-producing, and its actual meaning depends on a
recursive discharger with four ordered strategies:

1. contextual assumption;
2. `norm_num` derivation for disequalities;
3. positivity;
4. recursive simp with the field-simp nonzero lemmas.

The retained Mathlib audit runs the authoritative procedure once, restores its
pre-state, runs a source-faithful instrumented shadow, and requires exact step,
output/proof/cache, complete `Simp.State`, and parity for tracked metavariable and
message effects. It restores the complete authoritative Core/Meta post-state,
records the recursive discharge tree and attempt outcomes as passive
diagnostics, and provides no replay authority.

The discarded whole-module census prototype could consume more than 12 GB for
one module and did not provide a safe production boundary. The next step is a
resumable occurrence-isolated or bounded-shard census across the 227 measured
sites. That evidence must determine whether the stable representation is a
field-normalization derivation, an explicit discharger program, or a small set
of semantic subcases. Until then every result-bearing `fieldEq` call defers.

### 8. `Matrix.cons_val` — implemented

The output is a lookup into shared vector structure. The descriptor records a
checked vector-cons spine, WHNF witnesses, signed index view, closed/symbolic
tail length, wrapped index, and either a prefix selection or residual tail
application. Replay reconstructs only the selected term. Input/local dependency
terms cover symbolic tails without ambient elaboration.

### 9. `Fin.reduceFinMk` — implemented

The output is a fixed-size canonical `Fin.mk`, but its modulus can be an
evaluated Nat expression. The descriptor records the modulus input reference,
a recursive `NatEvalTrace` for raw values, metadata, assigned metavariables,
`OfNat`, successor, arithmetic, and power, plus the value view. Replay validates
every operator/instance, recomputes the modulus and normalization, and constructs
the canonical term. Power traces store the recording-time exponent threshold so
replay does not depend on an ambient option.

Assigned subtrees whose overloaded operator or `OfNat` instance cannot be
expressed as an input-backed dependency remain conservatively unsupported.

### 10. `ExistsAndEq.existsAndEq` — implemented with four explicit deferrals

The descriptor records the left-first route through nested existentials and
conjunctions, which side of equality contains the bound variable, and an
input-backed replacement subterm. Replay validates the transformation and
constructs both directions of the equivalence from fixed proof combinators.

The 65-module targeted source gate accounts for all 94 committed results across
77 source sites. Ninety produce semantic candidates. Three calls begin with
unassigned metavariables that the opaque source procedure may solve; they remain
unsupported because those assignments are not certificate operations. One
additional call uses the post registry, outside the pinned pre-registry
protocol. A candidate in a source occurrence deferred for another simproc is
accepted as correct semantic evidence but does not make that whole occurrence
replayable.

## Extension rule

This representation extends naturally to a new simproc only when all of the
following can be made explicit:

1. the actual simp/dsimp kind, registry placement, and result disposition;
2. every input, local, instance, environment, state, and meta-state dependency;
3. a closed derivation whose interpreter reconstructs the result and proof;
4. the state effects of result and no-result paths;
5. ordered composition with earlier/later candidates; and
6. focused differential, source, and mutation evidence.

If one of these is missing, the correct representation is deferral. Rare
declarations should also be compared with the cost of rewriting their source
sites; the committed histogram, rather than raw registry invocation counts, is
the basis for that choice.
