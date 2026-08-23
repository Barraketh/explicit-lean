# Explicit Lean implementation plan

Status: E1 and E2 complete; E3 is next.

## 1. Current goal

For every committed successful `simp` and `simp only` execution, produce
deterministic Lean source that replays the operations the pinned simplifier
performed. A certificate may use recorded theorem applications, fixed
reductions and builtins, explicit structural traversal, and recursively explicit
premise programs. It may not replace an unidentified operation with a generated
event proof, whole-result proof, aggregate `change`, or enclosing-body proof.

Simprocs and arbitrary custom dischargers are observed exactly but deferred for
separate designs. `simpa`, `simp_all`, `simp_rw`, and `rw` are later phases.

The normative engine model, certificate IR, invariants, and acceptance gates are
in [SIMP_ENGINE_COVERAGE.md](SIMP_ENGINE_COVERAGE.md).

## 2. Architecture

The implementation is a pinned copy of Lean's simplifier with three modes:

- reference mode, which must be observationally equivalent to upstream;
- recording mode, which emits schema-16 operations and structural witnesses at
  the engine's commit points; and
- replay mode, which will consume that program without ambient simp theorems,
  congruence rules, simprocs, or dischargers.

Recording and replay share the same traversal. This makes completeness a finite
implementation audit instead of an open-ended cycle of inferring missing steps
from corpus failures.

## 3. Implementation sequence

Each package is committed before work begins on the next.

### E1. Pinned reference engine — complete

- The authoritative Lean source surface is version- and hash-pinned.
- Focused `simp` and `dsimp` probes compare the fork with upstream.
- Two syntax-instrumented Mathlib modules compare 57 real `simp`/`simp only`
  calls with upstream.

### E2. Total structured recorder — complete

- Schema 16 represents all structural paths in the pinned engine audit, exact
  rule variants and matches, nested premise programs, reductions, congruence
  choices, subject transport, and final state.
- All simp and dsimp simproc phases are observed and assigned a deferred
  classification rather than converted to proof fallbacks.
- Failed speculative candidates roll back recorder state transactionally.
- Focused static and dynamic branch gates plus the two production modules test
  the recorder.

### E3. Closed structural replay — next

- Add replay mode to the same pinned traversal.
- Empty ambient simp, congruence, simproc, and discharger dependencies.
- Gate every changing branch by the next recorded command and validate paths,
  identities, assignments, phases, fingerprints, and exact consumption.
- Add mutation tests that change one field at a time and require failure at the
  mutated item.

Gate: every focused non-deferred recording replays; every mutation is rejected.

### E4. Certificate source and materializer

- Define and parse a stable schema-16 source form.
- Print qualified rule identities, engine/configuration identity, nested premise
  programs, and final-state validation.
- Instrument all supported calls in a module once, materialize replacements in
  batches, and bisect only compilation failures.

Gate: every focused and bounded-production non-deferred execution materializes,
and the complete copied modules compile.

### E5. Pre-cloud completeness review

- Mechanically diff the fork against pinned upstream, allowing only namespace,
  recursion, observer, and replay-driver changes.
- Require every changing return and structural decision to map to the IR.
- Run reference, recording, replay, mutation, source, and bounded production
  gates from a clean commit.

Gate: the implementation-to-IR matrix has no partial, implicit, or absent row.

### E6. Full cloud closure

- Inventory the pinned Mathlib checkout once at the tested commit.
- Compile each instrumented module once per mode and shard modules by stable
  hash.
- Upload per-module results and merge them into a terminal outcome for every
  inventoried occurrence.

Gate: every occurrence has a terminal classification; every committed
successful non-simproc/non-custom-discharger execution records, replays,
materializes, and compiles without fallback.

## 4. Current local gate

`Experiment/run.sh` is intentionally small. It builds the new engine and runs
only tests that provide confidence in that engine:

1. upstream source pinning;
2. focused upstream/reference equivalence;
3. implementation-to-IR observer audit;
4. focused dynamic recording coverage;
5. bounded Mathlib reference equivalence; and
6. bounded Mathlib recording equivalence.

Historical proof exporters, schema-15 bridges, fallback materializers, and
their regression tests have been removed. Git history remains the record of
those experiments.
