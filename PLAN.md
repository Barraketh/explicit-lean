# Explicit Lean roadmap

This document is the authoritative product and engineering contract. The
existing schema-27 implementation is retained as legacy evidence; its frozen
contract in [SIMP_ENGINE_COVERAGE.md](SIMP_ENGINE_COVERAGE.md) does not override
this plan. See [README.md](README.md) for setup, repository orientation, and
terminology.

## Goal and scope

Explicit Lean replaces each source `simp` or `simp only` tactic occurrence in a
Prop-valued proof body with generated source. Preserving every surrounding
tactic and authored binder spelling is preferred because it gives the strongest
local regression test, but it is not the semantic correctness boundary. The
translator may consistently alpha-rename theorem parameters and their uses when
generated source cannot otherwise refer to them. The active correctness boundary
is:

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

The legacy Lean implementation records and replays schema-27 simplifier
operations. Its tactic happens to be named `simp_engine_apply`, but it still
parses schema-27 certificate JSON, constructs a simp context, and invokes the
operational replay engine. It is not the boundary-state replacement specified
here.

The branch now also contains a separate boundary-state prototype:

- `ExplicitLean/SimpEngine/Boundary.lean` runs stock `simp` as the oracle,
  captures a closed boundary artifact, restores the pre-state, applies the
  artifact, and compares canonical post-state snapshots;
- `ExplicitLean/SimpEngine/Boundary/Apply.lean` applies target and authored
  hypothesis transformations in stock-visible order;
- `ExplicitLean/SimpEngine/Boundary/Tactic.lean` elaborates temporary explicit
  generated source without importing the recorder; and
- `Experiment/check_simp_engine_boundary.py` checks target and location
  behavior, apply import isolation, unchanged continuations, declaration types,
  axiom subsets, and absence of `sorryAx`.

`Experiment/check_simp_engine_boundary_source.py` is the first source-to-source
gate. It currently inventories seventeen focused occurrences, including
hypothesis locations, inaccessible binders, inline calls, two nested calls on
one line, a custom discharger with pre-existing expression/universe assignments,
transactional whole-tactic failure inside an unchanged alternative, and one
quoted reusable occurrence that succeeds in one caller and fails in another,
plus one explicitly authorized unobserved reusable occurrence that is replaced
by a fail-closed tactic.
It instruments them, captures artifacts, replaces the whole tactic, compiles
the continuations, and requires a syntax-aware zero remaining count. Generated
machine-oriented evidence refers to locals by deterministic declaration-index
aliases and parses its fully explicit term strings only after variant selection;
this survives macro hygiene and theorem-parameter alpha-renaming. A two-phase
placeholder rewrite preserves source ranges and final indentation.

The in-memory comparator has nineteen focused executions. In addition to the
source cases, it explicitly preserves pre-existing pending synthetic
metavariables and postponed constraints when stock `simp` leaves them
unchanged. The custom-discharger assignment case is reproduced by elaborating
the captured checked proof, so measurement has not justified a separate
assignment-delta representation yet.

`Experiment/check_simp_engine_boundary_mathlib.py` applies the same process to
four complete pinned source modules after joining the scope classification.
In `Mathlib/CategoryTheory/EqToHom.lean`, it transforms all 27 proof-body
occurrences, retains all six non-proof occurrences, compiles the result, and
finds zero remaining in-scope calls. In `Mathlib/Data/Fintype/List.lean`, all
six occurrences are non-proof data construction, so none are transformed and
all six are retained. In
`Mathlib/Analysis/CStarAlgebra/SpecialFunctions/PosPart.lean`, all three
occurrences are transformed; they produce six executions because one occurrence
selects among four distinct pre-states reached via `all_goals`/`fin_cases`.
The materialized copy compiles with zero remaining in-scope calls. Earlier broad
round trips of all syntactic occurrences remain useful renderer stress evidence:
`Fintype/List` exercises a committed `ExistsAndEq` result and beta-redex
lowering, while `PosPart` exercises a large `Matrix.cons_val` result. These are
representative module results, not a corpus claim.

`Mathlib/Algebra/Algebra/NonUnitalHom.lean` contributes seven excluded
occurrences and guards parser compatibility. This regression exposed an unused
bare `apply` production in the generated boundary tactic grammar that changed
how a Mathlib command parsed an identifier named `apply`; the production was
removed. The materializer emits only the unambiguous `apply_encoded` form.

`Experiment/check_simp_engine_boundary_scope.py` now conservatively joins syntax
ancestry with the final compiled types and source ranges of the smallest
enclosing declarations. Its 13-occurrence fixture distinguishes proof-valued
declarations, computational definitions, proposition data (`def p : Prop`), a
proof field inside non-proof structure construction, reusable tactic syntax,
retained quotation data, irreducible definition RHSs, declaration-signature
tactics, and generated commands. A standalone
`ExplicitLean/SimpEngine/Boundary/ScopeProbe.lean` carries each selected source
ID through a temporary copy, logs execution, and appends a report command that
resolves final declaration types with `Meta.isProp`. Anonymous examples are
renamed to temporary private definitions only for this measurement. Probe
copies inject global `set_option Elab.async false`, so the report runs after all
original bodies deterministically; the option and rename never reach
materialized output. Missing caller/type, missing execution, duplicate or extra
IDs, and mixed proof/non-proof observations fail closed.

The fixture has two statically proof-valued declarations, three statically
non-proof declarations, one reusable quotation, one retained quotation, one
irreducible exclusion, one signature exclusion, two observed proof declarations,
and two observed non-proof declarations. On the three representative Mathlib
modules it classifies `EqToHom` as 27 proof-body and six non-proof occurrences,
`Fintype/List` as six non-proof occurrences, and `PosPart` as three proof-body
occurrences. The exact
`Mathlib.Tactic.ToDual.«commandTo_dual_insert_cast_:=_»` command path is a narrow
static `in_scope_generated_proof_command` exception: its elaborator consumes the
RHS as the proof value of a generated theorem. Quotations outside that exact
path remain unclassified until execution evidence distinguishes use from
retention. Mathlib parsing uses the same pure `Mathlib` grammar environment as
inventory; the controlled fixture's extra grammar is loaded only for the
fixture.

`Experiment/simp_engine_boundary_corpus.py` now defines that boundary-native
manifest and its fail-closed construction rules. It pins repository, Lean,
Mathlib, the complete active implementation source families, source, and module
identities; retains modules with no supported calls; and joins every occurrence
to its source-backed scope classification. Statically unclassified occurrences
are probed one affected module per temporary process; compact execution
evidence records the report module, caller/count summaries, final proof flags,
status, and probe-only scheduling option in the occurrence record. The 3-module
smoke has no unknowns and therefore does not invoke this probe. Byte-identical
raw syntax records sharing one replaceable source range are collapsed and
counted; conflicting records still fail. Its scope join and execution join
preserve distinct paths/IDs and reject missing, duplicate, extra, or conflicting
data. The builder requires a clean pinned Mathlib checkout and rechecks
repository/toolchain identity, implementation hashes, and every selected source
before emitting, rejecting the result if any of those inputs changed.
Dirty-repository and unclassified diagnostic allowances are explicit manifest
fields. Policy enforcement also precedes atomic output replacement, so a
rejected run cannot publish a newly generated manifest. Its bounded smoke gate
builds the same three-module manifest twice and requires byte-identical output
with the exact 30 eligible and 12 excluded occurrence partition. A separate
targeted diagnostic over the existing pre-probe manifest closes the old 101
unknowns as 38 static non-proof commands, 3 signature exclusions, 5 generated
proof commands, and 55 dynamically observed proof declarations, with zero
unclassified.

That classifier was then used to generate
`.lake/boundary-corpus-manifest/manifest-scope-closed-v2.json` (SHA-256
`541a2d71f338e53b55335f76c699b14f8a2f12532b9a8cd865cbbd369e34ff25`).
It covers all 8,264 pinned Mathlib module files and inventories 83,425
occurrences: 69,403 eligible and 14,022 excluded, with zero unclassified. Its
explicit policy is `allowDirty: true, allowUnclassified: false`; because the
working repository was dirty, this is diagnostic evidence and must not be
uploaded as the clean archival closure report. It predates the repair that
added the Lean inventory executable to the implementation fingerprint, so the
current consumer rejects it and a clean full manifest must be regenerated from
the committed implementation.

`Experiment/boundary_materialize_shard.py` is the first fail-closed consumer of
current manifests. A fresh one-module repair-review
`Mathlib/Algebra/AddConstMap/Basic.lean` canary has 17 total occurrences. It
observes and materializes all nine eligible occurrences as nine successful
boundary variants, retains exactly eight excluded occurrences, compiles, and
proves that authored source bytes outside the replaced tactic ranges are
unchanged. It preserves all authored binders without alpha-renaming. The
pre-commit manifest and report are disposable; committing changes their pinned
repository identity, so the durable run begins by regenerating them.

`Experiment/run.sh` retains the legacy regression checks and now also runs all
boundary prototype commands. These are focused engineering gates, not a pinned
Mathlib closure claim.

Once that path is accepted, the public `simp_engine_apply` syntax can move from
schema-27 replay to boundary artifacts. Until then, code and reports must label
the two implementations explicitly.

The next engineering gaps are dependency-aware recording for the 66 reusable
tactic-syntax occurrences, safe composition for the 91 nested occurrences,
larger deterministic materialization shards, and any generic state-delta or
external-effect cases exposed by those shards. The current runner rejects
reusable syntax and nested/overlapping replacement ranges rather than guessing.

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
6. Scoped options and continuation-visible environment extensions are expected
   to remain unchanged. Elaborating a `simp` argument may create inaccessible
   private helper declarations; the recorder inlines references to those helpers
   into the closed artifact and restores the pre-call environment. Any persistent
   environment or other Core/Meta change that an unchanged continuation can
   observe is an `external_effect_failure` until that effect is represented and
   tested generically.

Fresh goal, local, expression-metavariable, and universe-metavariable identities
need not be numerically equal. Simplifier caches, rule search order, internal
candidate rollback, used-theorem counters, messages and diagnostics, step
counts, and simproc traces are outside the proof-state boundary.

The prototype must implement one canonical snapshot/comparison function for
this contract. Successful compilation of the continuation—source-identical when
possible and otherwise changed only by consistent binder alpha-renaming—is the
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
deduplicated. The current generated dispatcher computes the canonical state,
full options, and stable caller before elaborating any evidence, selects exactly
one observed outcome, and fails closed when none matches. This non-backtracking
selection is necessary so a selected failure variant escapes to the unchanged
surrounding tactic control flow. Unequal variants under one key are an
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
The preferred materialization leaves tactics before and after the replaced call
byte-for-byte unchanged except for source-range composition. The current
machine-oriented encoding uses deterministic declaration-index aliases for all
locals so the same artifact works inside hygienic tactic quotations and after
theorem-parameter alpha-renaming. A later readable renderer may retain authored
names where safe. A translator may instead alpha-rename theorem parameters and
all of their references; that fallback must preserve
binder order, binder information, and types, and the declaration-equivalence
gate must accept it before the module is counted as translated. Surrounding
tactic structure may not otherwise change merely to make materialization pass.

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

Scope closure uses a source-backed, two-phase probe for only the occurrences
left unclassified by the static pass. The temporary copy replaces each selected
`simp` head with an ID-carrying standalone probe, disables asynchronous body
elaboration with global `set_option Elab.async false`, and appends a report
command after the original source. The report groups repeated executions,
resolves the final declaration type, and records `Meta.isProp` evidence; it
does not inspect simplifier internals. Anonymous `example` commands are
temporarily renamed to private definitions so their final types survive
elaboration. Missing/extra IDs, missing callers or types, missing execution,
and mixed proof/non-proof observations remain unclassified. The exact
`Mathlib.Tactic.ToDual.«commandTo_dual_insert_cast_:=_»` command is separately
classified as a generated proof command because its elaborator consumes its RHS
as a generated theorem proof; this is not a general caller-null fallback.

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
7. Resume the original continuation, unchanged when possible and otherwise
   changed only by consistent binder alpha-renaming.
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
- a continuation, unchanged except for any required binder alpha-renaming, that
  consumes every transformed boundary feature.

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

Durable report procedures are in [REPORTS.md](REPORTS.md). The focused boundary,
selector, conservative scope-classification, ID-carrying execution probe, and
explicitly authorized unobserved paths now support the measured cases and are
integrated in the representative translators. The deterministic manifest
format, bounded smoke gate, and targeted old-unknown closure are in place; the
full pinned diagnostic manifest and one exact-source-preserving materialization
canary are also complete. The immediate milestone is designing dependency-aware
handling for reusable tactic syntax, then scaling deterministic shards while
closing nested-range and measured boundary failures.
