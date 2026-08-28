# Explicit Lean roadmap

This document is the authoritative product and engineering contract. The
existing schema-27 implementation is retained as legacy evidence; its frozen
contract in [SIMP_ENGINE_COVERAGE.md](SIMP_ENGINE_COVERAGE.md) does not override
this plan. See [README.md](README.md) for setup, repository orientation, and
terminology.

## Goal and scope

Explicit Lean replaces each source `simp` or `simp only` tactic occurrence in a
Prop-valued proof body with generated source while leaving every tactic before
and after that occurrence unchanged. The active correctness boundary is:

> Reproduce the externally visible proof state after each `simp` call, without
> reproducing the internal simplifier execution.

The replacement tactic is called `simp_engine_apply`. It may initially consume a
machine-oriented boundary artifact. Making that argument maximally readable
Lean source is a later presentation step.

The first closure target is the pinned Mathlib corpus and toolchain recorded in
`lake-manifest.json` and `lean-toolchain`. It includes parsed
`Lean.Parser.Tactic.simp` nodes for `simp` and `simp only` that participate in
elaborating Prop-valued declarations. The following are outside this milestone:

- `simpa`, `simp_all`, `simp_rw`, `rw`, and tactics that merely call `simp`
  internally;
- tactic syntax quoted and retained as data rather than executed while proving
  an in-scope declaration; and
- tactic use that constructs computational, non-Prop data.

Reusable tactic or macro source that executes during the pinned build may have
several recorded boundary variants. Syntax that could execute only in a future
downstream build is not silently considered generalized: it is either supplied
with a parameterized boundary program later or fails closed as unobserved.

## Current implementation status

The current Lean implementation records and replays schema-27 simplifier
operations. Its tactic happens to be named `simp_engine_apply`, but it still
parses schema-27 certificate JSON, constructs a simp context, and invokes the
operational replay engine. It is not the boundary-state replacement specified
here.

The current syntax inventory finds parser-level occurrences and stable ranges,
including nested and quoted syntax, but it is not yet a proof-body scope
classifier. The active harness must associate occurrences with enclosing
declarations and distinguish Prop-valued proof execution, reusable tactic code,
quoted data, and non-Prop construction before it can make a zero-call claim.

`Experiment/run.sh` is the passing legacy regression gate. No active boundary
prototype or boundary acceptance command exists yet. The next task is to add a
side-by-side prototype without weakening the legacy gate; suggested files are:

- `ExplicitLean/SimpEngine/Boundary.lean` for boundary snapshots, comparison,
  artifacts, selection, and apply-only transport;
- `Experiment/SimpEngineBoundaryProbe.lean` for focused Lean fixtures; and
- `Experiment/check_simp_engine_boundary.py` as the first active gate.

Once that path is accepted, the public `simp_engine_apply` syntax can move from
schema-27 replay to boundary artifacts. Until then, code and reports must label
the two implementations explicitly.

## Correctness contract

Let `S` be the state immediately before one dynamic source execution. Running
the original tactic with stock pinned Lean either succeeds with state `S_stock`
or fails transactionally. From the same `S`, the generated replacement must
produce a continuation-compatible `S_apply`, or fail transactionally under the
same selector conditions, without invoking simplification. The exact unchanged
continuation must then elaborate and kernel-check.

### Continuation-visible state

`S_stock` and `S_apply` are continuation-compatible when there is a consistent
renaming of fresh internal identifiers under which all of the following agree:

1. The tactic succeeds, fails, or closes the active goal in the same way.
   Diagnostic wording and simplifier statistics do not have to match.
2. The ordered goal list has the same length. Corresponding target types are
   definitionally equal.
3. Each corresponding goal has the same ordered local context: declaration
   kind, binder information, user-facing name, type, and optional local value.
   Types and values may differ only by definitional equality and the consistent
   identifier renaming.
4. Expression and universe metavariables that existed before the call have the
   same assignment status and definitionally equal assignments. Assignments
   induced by elaborating the generated proof are allowed when they produce the
   same delta.
5. Pre-existing postponed constraints or synthetic metavariables have
   equivalent status whenever the unchanged continuation can observe them.
6. Scoped options and environment extensions are expected to remain unchanged.
   If measurement finds that stock `simp` or a custom discharger persistently
   changes another Core/Meta field that can affect the unchanged continuation's
   proof state, the occurrence is an `external_effect_failure` until that effect
   is represented and tested generically.

Fresh goal, local, expression-metavariable, and universe-metavariable identities
need not be numerically equal. Simplifier caches, rule search order, internal
candidate rollback, used-theorem counters, messages and diagnostics, step
counts, and simproc traces are outside the proof-state boundary.

The prototype must implement one canonical snapshot/comparison function for
this contract. Successful compilation of the unchanged continuation is the
end-to-end oracle, but it does not replace focused comparison tests for each
listed field.

### Declaration boundary and trust

For each translated declaration:

- its type must be definitionally equal to the original declaration's type;
- its proof must contain no unresolved metavariables or `sorryAx`;
- its transitive axiom set must be a subset of the original declaration's axiom
  set; and
- the generated source must compile with the pinned unmodified Lean kernel.

Fewer axiom dependencies are allowed. Any necessary exception to the subset
rule must be explicitly reviewed and documented before corpus acceptance.

For two proofs of the same proposition, Lean's proof irrelevance makes the proof
bodies definitionally equal. The project therefore does not reproduce the
original proof-term structure; it reproduces the proposition, accepted proof,
and continuation-visible state at each replaced call.

## Boundary artifact and selection

One source occurrence owns a closed artifact containing zero or more boundary
variants. A successful variant contains:

- checked references to each authored hypothesis or target being transformed;
- the resulting expression for each subject;
- an equality, iff, or transport proof, or an explicit definitional-equality
  marker;
- ordered subject terminals: replace, assert-and-clear, close from `False`,
  close target from `True`, or transport target;
- the resulting ordered goals; and
- explicit deltas for pre-existing expression/universe metavariables and any
  other supported continuation-visible effect not established by elaborating
  the generated proof.

A failure variant contains no post-state mutation and causes the replacement to
fail so that unchanged tactic alternatives behave as before. Exact error text is
diagnostic only.

### Dynamic selection rule

Selection must not construct a simp context or consult simp theorems, simproc
registries, or dischargers. The initial selector key is:

1. stable source occurrence ID (`module:startByte:endByte` hash);
2. canonical fingerprint of the complete ordered pre-call goal/context state;
3. a deterministic fingerprint of the full scoped Lean option map; and
4. stable caller identity: module and enclosing declaration.

The full option map is intentionally conservative: the current schema-27 source
gate has already observed one source occurrence with the same goal under
different scoped options. A later reviewed reduction to relevant options is
permitted only after differential evidence.

Recording may observe the same key more than once. Equal boundary variants are
deduplicated. Unequal variants under one key are an
`ambiguous_boundary_variant`; the selector identity must be extended with the
measured pre-call discriminator before materialization. Any extension must be
stable in transformed source and computable without inspecting simp theorems,
registries, dischargers, or operational state. A missing key fails closed as
`boundary_variant_missing`.

The final boundary fingerprint is defensive validation, not replay authority.
It uses the same canonical comparison model as the prototype oracle.

### Generated source shape

The target form is conceptually:

```lean
by
  intro h
  simp_engine_apply (artifact := boundaryArtifactForThisOccurrence)
  exact unchangedContinuation
```

This replaces the whole original `simp ...` tactic. Its rule list, configuration,
discharger, and location may be retained only as inert provenance inside closed
data; the apply path must not elaborate them or reconstruct a simp context.
“Leave the surrounding script unchanged” means the tactics before and after the
replaced call are byte-for-byte unchanged except where source-range composition
requires indentation or quotation handling.

The syntax above is illustrative; the current parser still has the legacy
schema-27 shape. The first prototype may use a temporary syntax name to prevent
accidental confusion.

## Closed-world corpus completion

The initial product claim is deliberately pinned and closed-world. A complete
run must:

1. freeze the exact Mathlib module manifest, clean-build command, environment,
   and scope-classification version in the run manifest;
2. inventory every parsed `simp`/`simp only` node and produce a source-backed
   classification of whether it belongs to the stated scope;
3. collect every dynamic execution seen while compiling every module in the
   frozen manifest;
4. rewrite every in-scope source occurrence, including occurrences with no
   observed execution;
5. give observed executions unambiguous boundary variants;
6. give an unobserved occurrence an explicit fail-closed replacement that
   raises `boundary_occurrence_unobserved` if it unexpectedly executes;
7. compile the complete translated tree with the original continuations;
8. report a syntax-aware zero count of remaining in-scope source occurrences;
   and
9. archive the inventory, classifications, compilation result, declaration
   checks, and remaining-call audit.

An occurrence may be classified as `materialized`, `expected_failure`,
`unobserved`, `out_of_scope_quotation`, `printer_failure`,
`ambiguous_boundary_variant`, or `external_effect_failure`. Only the first four
may appear in a successful pinned closure, and every exclusion must retain a
source range and reason.

This claim does not promise that a translated reusable tactic supports new
downstream states. Encountering an unrecorded state fails closed and requires a
fresh translation or a future parameterized artifact.

## Focused prototype

Build the smallest end-to-end implementation against stock Lean:

1. Save the complete boundary snapshot immediately before one source call.
2. Execute the unmodified call with Lean's stock tactic implementation.
3. Capture the canonical stock post-boundary snapshot and the minimal result
   expressions, transport proofs, terminals, and persistent assignment delta.
4. Restore the exact pre-call state.
5. Apply the captured transformation through the new apply-only module.
6. Compare the stock and apply snapshots with the canonical boundary comparator.
7. Resume the exact original continuation.
8. Compare declaration types and transitive axiom sets.

The focused matrix must cover:

- target-only `simp` and `simp only`;
- `simp at h`, multiple hypotheses, `simp at h ⊢`, and `simp at *`;
- targets simplified to `True` and hypotheses simplified to `False`;
- proof-producing and definitional-only transformations;
- dependent hypotheses, local definitions, binder names, and instance binders;
- multiple ordered goals and fresh goals introduced around the call;
- success, no-progress failure inside an alternative, and goal closure;
- repeated execution under different goals and under identical goals with
  different scoped options;
- pre-existing expression and universe metavariable assignments, including the
  measured `ExistsAndEq` examples;
- pre-existing postponed constraints or synthetic metavariables;
- custom dischargers and representative large/shared simproc outputs; and
- an unchanged continuation that consumes every transformed boundary feature.

### Prototype acceptance gate

`Experiment/check_simp_engine_boundary.py` will be the first active gate and
must establish:

- focused snapshot equivalence for every contract field;
- successful compilation with the original continuation unchanged;
- definitionally equal declaration types and the axiom-subset rule;
- rejection of missing, ambiguous, mutated, and wrong-option variants; and
- apply-path independence from simplification.

Apply-path independence requires both a reviewed static dependency check and a
runtime probe. The static check rejects calls from the apply-only dependency
closure to `Meta.simp`, `Meta.simpGoal`, `mkSimpContext`, the schema-27 replay
engine, simproc registries, or dischargers. The runtime probe materializes while
instrumented forbidden entry points fail if reached. Translation/recording code
is allowed to call stock `simp`; generated apply code is not.

## Existing assets and boundaries

Reuse:

- syntax inventory, stable source ranges, nested/quoted head rewriting, and
  occurrence IDs from `Inventory.lean` and `simp_engine_inventory.py`;
- the stock `Meta.simpGoal` oracle and location/transport patterns in
  `Recording.lean`, after extracting them from schema-27 program generation;
- canonical expression/local-context machinery in `Fingerprint.lean`, extended
  to the boundary fields specified above;
- complete-module copy/compile logic from `check_simp_engine_source.py`; and
- deterministic corpus sharding/reduction and S3 report storage.

Treat the schema-27 fork, replay engine, semantic simproc interpreters, observer
matrix, and mutation suite as legacy oracle material. Do not extend them merely
to reproduce more internal simplifier execution. Git commits `f117aae`,
`0106ddd`, and `60f8a0f` contain prior proof-source experiments for stable
binders, shared subterms, and expanded proof terms; inspect them when the printer
work begins rather than copying them blindly.

## Simprocs and custom dischargers

Opaque simprocs and custom dischargers run only during translation. Their checked
result expressions and proofs become boundary evidence. No declaration-specific
semantic interpreter is needed unless a measured persistent effect escapes the
stock call and cannot be represented as a generic boundary transformation.

The measured risks and focused cases are summarized in
[simprocs.md](simprocs.md). Internal registry order, candidate rollback,
discharger strategy, and simproc traces are not acceptance conditions.

## Roadmap

1. Implement and review the focused boundary prototype and active gate.
2. Stabilize the boundary comparator, selector, artifact schema, and failure
   classifications from measured focused cases.
3. Produce readable, stable source for results, proof terms, local references,
   universes, instances, and explicit assignment deltas.
4. Adapt the source harness into a deterministic translator that replaces the
   complete tactic occurrence while preserving the enclosing proof body.
5. Run module-scale and then full pinned-corpus recording/materialization,
   closing printer, ambiguity, and external-effect failures from measurements.
6. Require zero remaining in-scope calls, compile the full translated tree, run
   declaration type/axiom checks, and archive the closure report.
7. Generalize boundary artifacts for reusable downstream contexts where demand
   justifies it.
8. Improve `simp_engine_apply` arguments toward maximally human-readable source
   without weakening kernel, axiom, selector, or boundary checks.

Durable report procedures are in [REPORTS.md](REPORTS.md). The next milestone is
step 1, not another attempt to close schema-27 operational replay.
