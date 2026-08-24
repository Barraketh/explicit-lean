# Explicit Lean implementation plan

Status: E1 through E5 complete; E6 cloud execution is in progress.

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
- recording mode, which emits schema-19 operations and structural witnesses at
  the engine's commit points; and
- replay mode, which consumes that program without ambient simp theorems,
  congruence rules, simprocs, or dischargers.

Recording and replay share the same traversal. This makes completeness a finite
implementation audit instead of an open-ended cycle of inferring missing steps
from corpus failures.

## 3. Implementation sequence

Each package is committed before work begins on the next.

### E1. Pinned reference engine — complete

- The authoritative Lean source surface is version- and hash-pinned.
- Focused `simp` and `dsimp` probes compare the fork with upstream.
- The source gate verifies upstream/fork final-state equivalence while compiling
  complete instrumented Mathlib modules; there is no separate bounded adapter.

### E2. Total structured recorder — complete

- Schema 19 represents all structural paths in the pinned engine audit, exact
  rule variants and matches, nested premise programs, reductions, congruence
  choices, subject transport, and final state.
- Every invoked simp and dsimp simproc candidate, including `continue none`, is
  observed and assigned a deferred classification rather than converted to a
  proof fallback. Every invoked custom discharger is likewise deferred.
- Failed candidates that execute recursive work are retained as explicit failed
  attempts; candidates with no executable progress are omitted.
- Focused static and dynamic branch gates test the recorder; the source gate
  exercises the same recorder in complete modules.

### E3. Closed structural replay — complete

- Add replay mode to the same pinned traversal.
- Empty ambient simp, congruence, simproc, and discharger dependencies.
- Gate every changing branch by the next recorded command and validate paths,
  identities, assignments, phases, fingerprints, and exact consumption.
- Add mutation tests that change one field at a time and require failure at the
  mutated item.

Gate: every focused non-deferred recording replays; every mutation is rejected.

Status: complete. The focused suite replays 37 dynamic branch classes and 23
single-field mutations are rejected. Complete-module recording, replay, and
classification are owned by the source gate below rather than a second replay
harness.

### E4. Certificate source and materializer — complete

- Define and parse a stable schema-19 source form.
- Print qualified rule identities, engine/configuration identity, nested premise
  programs, and final-state validation.
- Instrument all supported calls in a module once, materialize replacements in
  batches, and bisect only compilation failures.

Gate: every focused and bounded-production non-deferred execution materializes,
and the complete copied modules compile.

Status: complete. Schema 19 is serialized as compact JSON inside shallow Lean
string arrays. Every payload is decoded and compared structurally with the
recorded certificate before it is written; `Name` values use lossless
string/numeric components rather than Lean's lossy default JSON codec. A source
occurrence emits one passive, non-deduplicated completion record per dynamic
execution. Selection keys on `(initial proof-state fingerprint, ReplayConfig)`:
equal duplicates under that full key are allowed, while unequal duplicates under
the same full key are rejected. Nested occurrences are instrumented by replacing
only their `simp` head; an attached quotation source antiquotation such as `%$s`
moves with that head instead of being stranded after injected arguments. Rule-origin
identity canonicalizes the recording/materialization wrappers without executing
ambient simp. The source gate covers 510 occurrences in seventeen complete module
copies: 213 materialize across 242 dynamic executions, 296 are explicitly
simproc-deferred, and one executes unsuccessfully under `first`. A mutated
engine identity is rejected before replay. Multiline certificate source keeps
trailing tactic configuration to the right of the original tactic column, as
required by Lean's offside rule. The production fixture also covers a cache hit
after the cached expression's binder has left the current local context and a
generated matcher whose private name changes during source materialization.
It also covers a successful user-congruence traversal whose auto-congruence
child explicitly unfolds numeric literals inside `dsimp`, plus an authored
local rule whose lhs retains a let-bound set after the subject unfolds it.
It further requires user-congruence preprocessing and closed certificate-term
elaboration to be observational: neither may solve, allocate, or leak
metavariables in the surrounding declaration before replay begins.

### E5. Pre-cloud completeness review

- Mechanically diff the fork against pinned upstream, allowing only namespace,
  recursion, observer, and replay-driver changes.
- Require every changing return and structural decision to map to the IR.
- Run reference, recording, replay, mutation, and complete-module source gates
  from a clean commit.

Gate: the implementation-to-IR matrix has no partial, implicit, or absent row.

Status: complete. The source-level review maps 120 semantic fork declarations
to their pinned upstream declarations, separately audits 108 controlled
declarations, and locks every semantic module by hash. The review corrected
staged simp/dsimp cache provenance, binder and metadata paths, exact
theorem-variant selection, stable
lazy-equation origins, generated- and user-congruence identity, match-attempt
rollback, ground-context isolation, and reduction/builtin eligibility. The
focused recorder covers 42 dynamic branch classes, focused replay covers 37,
and 23 independent certificate mutations are rejected.

### E6. Full cloud closure

- Inventory the pinned Mathlib checkout once at the tested commit.
- Compile each instrumented module once per mode and shard modules by stable
  hash.
- Upload per-module results and merge them into a terminal outcome for every
  inventoried occurrence.

Gate: every occurrence has a terminal classification; every committed
successful non-simproc/non-custom-discharger execution records, replays,
materializes, and compiles without fallback.

Status: validated inventory and parallel Vast.ai infrastructure complete;
cloud corpus result pending. GitHub-hosted runners were rejected because their
observed eviction behavior prevented parallel execution from producing durable
results; the superseded workflow has been removed.

The accepted run inventories 8,264 files and validates 83,425 occurrences in
6,319 modules byte-for-byte, including 91 nested occurrences. It uses 256
deterministic batches across eight distinct verified Vast.ai hosts, with eight
Lean module processes per host: 64 modules record or materialize concurrently.
Every host must expose at least 32 effective CPU cores and 192 GB RAM, reserving
24 GB per process. This replaces the earlier one-process/250 GB plan: reproducing
the worst failure showed that recursive premise traces duplicated their outer
prefix, expression fingerprints expanded shared DAGs as trees, and fingerprint
observers leaked speculative meta-state. After correcting all three invariants,
the module that had exceeded 250 GB completes the production harness in 7.5
seconds at 1.61 GB RSS. Capacity exits remain failing outcomes rather than being
reclassified as certificate behavior.

Offers are selected from the live market under unique-machine, reliability,
CPU, RAM, disk, network, hourly-price, and total-runtime guards. Setup raises
and verifies a 65,536 file-descriptor limit before parallel Mathlib cache
extraction. All hosts set up concurrently; failed setup or transfer hosts are
destroyed and replaced while healthy workers continue. The compressed
inventory is transferred once, and durable reports, logs, and failing sources
are copied home every 30 seconds while transient `work/` trees are excluded.
Every batch records each assigned module once and compiles one materialized
copy for all accepted occurrences. The strict reducer rejects incomplete or
missing batches, modules, occurrences, source or engine drift, mismatched
deferred certificate/reason unions, replay-count mismatches, and every recorder,
harness, capacity, or materialization failure. Every rented instance is
destroyed on success,
failure, timeout, or interruption.

## 4. Current local gate

`Experiment/run.sh` is intentionally small. It builds the new engine and runs
only tests that provide confidence in that engine:

1. upstream source pinning;
2. focused upstream/reference equivalence;
3. implementation-to-IR observer audit;
4. locked fork-to-upstream source review;
5. focused dynamic recording coverage;
6. focused closed replay;
7. single-field replay mutation rejection;
8. schema-19 source round-trip and complete-module upstream comparison,
   classification, replay, and materialization; and
9. cloud shard assignment and strict reducer mutation rejection; and
10. total Vast worker assignment, unique-host selection, SSH parsing, and
    hourly-price guards.

Historical proof exporters, schema-15 bridges, fallback materializers, and
their regression tests have been removed. Standalone bounded reference/replay
harnesses were also removed once the complete-module source gate subsumed them.
Git history remains the record of those experiments.
