# Explicit Lean roadmap

This document is the authoritative product and engineering contract. The
existing schema-27 implementation is retained as legacy evidence; its frozen
contract in [SIMP_ENGINE_COVERAGE.md](SIMP_ENGINE_COVERAGE.md) does not override
this plan. See [README.md](README.md) for setup, repository orientation, and
terminology.

## Goal and scope

Explicit Lean replaces each executed source `simp` or `simp only` tactic
occurrence with generated source, regardless of whether the enclosing
declaration produces a proof or computational data. Preserving every
surrounding tactic and authored binder spelling is preferred because it gives
the strongest local regression test, but it is not the semantic correctness
boundary. The translator may consistently alpha-rename declaration parameters
and their uses when generated source cannot otherwise refer to them. The active
correctness boundary is:

> Reproduce the semantically observable output of each `simp` call, without
> reproducing the internal simplifier execution.

The replacement tactic is called `simp_engine_apply`. It may initially consume a
machine-oriented boundary artifact. Making that argument maximally readable
Lean source is a later presentation step.

The first closure target is the pinned Mathlib corpus and toolchain recorded in
`lake-manifest.json` and `lean-toolchain`. It includes parsed
`Lean.Parser.Tactic.simp` nodes for `simp` and `simp only` that execute, or form
reusable executable tactic code, during the pinned build. The following are
outside this milestone:

- `simpa`, `simp_all`, `simp_rw`, `rw`, and tactics that merely call `simp`
  internally;
- tactic syntax quoted and retained as syntax data rather than executed; such a
  value is not a `simp` call and changing it would change observable data; and
- executions that occur only in a future downstream build.

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
  behavior, apply import isolation, and unchanged continuations.

`Experiment/SimpEngineDeclarationOracle.lean` separately compares the completed
stock and materialized modules: declaration kinds and metadata, definitionally
equal types and non-`Prop` values (including opaque/irreducible values),
recursor rules, compiler/runtime IR, persistent environment extensions,
transitive axiom subsets, and absence of unresolved terms or `sorryAx`.
Private-like proof declarations (theorems or `Prop`-valued definitions/opaques),
including generated `_proof_N` helpers, are closed-world proof artifacts: they
may be added or omitted, or differ in type and metadata. A same-name
proof/non-proof classification change fails. Public metadata and types, every
non-`Prop` value, public axiom subsets, compiler IR, and relevant extension state
remain checked, and applied expressions remain resolved and `sorry`-free.

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
this survives macro hygiene and declaration-parameter alpha-renaming. A two-phase
placeholder rewrite preserves source ranges and final indentation.

The in-memory comparator has nineteen focused executions. In addition to the
source cases, it explicitly preserves pre-existing pending synthetic
metavariables and postponed constraints when stock `simp` leaves them
unchanged. The custom-discharger assignment case is reproduced by elaborating
the captured checked proof, so measurement has not justified a separate
assignment-delta representation yet.

The artifact and apply path are sort-neutral: they transform tactic
goals, local declarations, metavariables, and constraints without requiring the
enclosing declaration to be proof-valued. The scope classifier and schema-2
manifest now record independent `executionRole`, `declarationKind`, and
`action` fields; proof status never controls materialization. The paired
in-memory comparator uses actual definitional equality under one consistent
fresh-identifier renaming. Fingerprints select recorded variants and aid
diagnostics; a matching hash is never semantic proof.

`Experiment/check_simp_engine_boundary_mathlib.py` now materializes every
executable occurrence in five complete pinned source modules: all 17 calls in
`Mathlib/Algebra/AddConstMap/Basic.lean`, all 33 in
`Mathlib/CategoryTheory/EqToHom.lean`, all six in
`Mathlib/Data/Fintype/List.lean`, all seven in
`Mathlib/Algebra/Algebra/NonUnitalHom.lean`, and all three in
`Mathlib/Analysis/CStarAlgebra/SpecialFunctions/PosPart.lean`. Every materialized
copy compiles with zero remaining executable calls and passes the
declaration/environment oracle. The successful reports respectively accounted
for 141, 134, 10, 165, and 5 declarations, with 103, 71, 5, 104, and 5 common
public declarations. Here `checkedDeclarationCount` is the number processed
under the applicable comparison or private-proof rule, not the number receiving
a definitional-equality comparison.

Earlier broad round trips remain useful renderer stress evidence:
`Fintype/List` exercises a committed `ExistsAndEq` result and
beta-redex lowering, while `PosPart` exercises a large `Matrix.cons_val`
result. These are representative module results, not a corpus claim.

`Mathlib/Algebra/Algebra/NonUnitalHom.lean` contributes seven transformed
computational occurrences and guards parser compatibility. This regression
exposed an unused bare `apply`
production in the generated boundary tactic grammar that changed how a Mathlib
command parsed an identifier named `apply`; the production was removed. The
materializer emits only the unambiguous `apply_encoded` form.

`Experiment/check_simp_engine_boundary_scope.py` currently joins syntax ancestry
with the final compiled types and source ranges of the smallest enclosing
declarations. Its 13-occurrence fixture distinguishes proof-valued
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
IDs, and mixed observations fail closed.

The classifier does not use `Meta.isProp` as an eligibility test. It records
whether syntax is directly executable, reusable executable code, retained
syntax data, or unresolved separately from the semantic kind of the enclosing
declaration or command. Proof/computational status selects the declaration
comparison rule, not whether the occurrence is translated. The focused fixture
has 11 direct, one reusable, and one retained occurrence; 12 materialize and one
is retained.

The fixture has two statically proof-valued declarations, three statically
non-proof declarations, one reusable quotation, one retained quotation, one
irreducible computational case, one signature/default case, two observed proof
declarations, and two observed computational declarations. The exact
`Mathlib.Tactic.ToDual.«commandTo_dual_insert_cast_:=_»` command path is a narrow
static generated-command case: its elaborator consumes the RHS as the proof
value of a generated theorem. The classifier handles this as one
instance of command output rather than a proof-only eligibility exception.
Quotations remain unresolved until execution evidence distinguishes executable
code from retained syntax data. Mathlib parsing uses the same pure `Mathlib`
grammar environment as inventory; the controlled fixture's extra grammar is
loaded only for the fixture.

`Experiment/simp_engine_boundary_corpus.py` now defines that boundary-native
manifest and its fail-closed construction rules. It pins repository, Lean,
Mathlib, the complete active implementation source families, source, and module
identities; retains modules with no supported calls; and joins every occurrence
to its source-backed scope classification. Statically unresolved occurrences
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
Dirty-repository and unresolved diagnostic allowances are explicit manifest
fields. Policy enforcement also precedes atomic output replacement, so a
rejected run cannot publish a newly generated manifest. Its bounded smoke gate
builds the same three-module manifest twice and requires byte-identical output
with all 42 occurrences marked `materialize`. A separate targeted diagnostic
over the existing pre-probe manifest resolved 38 computational commands, 3
signature/default occurrences, 5 generated proof commands, and 55 dynamically
observed proof declarations, with zero unclassified under that older schema.

That classifier was then used to generate
`.lake/boundary-corpus-manifest/manifest-scope-closed-v2.json` (SHA-256
`541a2d71f338e53b55335f76c699b14f8a2f12532b9a8cd865cbbd369e34ff25`).
It covers all 8,264 pinned Mathlib module files and inventories 83,425
occurrences. Its 69,403 eligible and 14,022 excluded split encodes the obsolete
proof-only rule. The old rule excluded 13,981 occurrences in computational
declarations, 38 in special computational commands, and 3 in
signatures/defaults. Those categories are no longer exclusions: every
executable occurrence among them is now a translation candidate. The old
classifier did not independently establish execution role, so the revised
candidate count is unknown until it separates executable code from syntax
retained only as data. The old manifest remains inventory evidence only and
must not be used for product closure. It was also generated with
`allowDirty: true` and predates the hardened implementation fingerprint, so the
current consumer correctly rejects it.

`Experiment/boundary_materialize_shard.py` is the first fail-closed consumer of
current manifests. The schema-2 one-module
`Mathlib/Algebra/AddConstMap/Basic.lean` canary materializes all 17 occurrences,
observes 17 variants, compiles, and proves exact authored-source preservation
outside the replaced ranges. Its schema-4 materialization report now includes a
mandatory declaration/environment oracle and one ordered result record for every
selected occurrence. Each record is one of the four successful classifications:
`materialized`, `expected_failure`, `unobserved_executable`, or
`retained_syntax_data`. The report also records the exact schema-1 artifact
identity and protocol encoding, while aborting without publishing a successful
report for printer, variant, effect, declaration-value, or environment failures.
That oracle accepts 103 common public
declarations and omission of two stock-only private proof helpers, while checking
all computational values, metadata, compiler IR, extensions, and axiom subsets.
One reserved-name action recreates `AddConstMap.mk.congr_simp`. Compiler LCNF is
compared structurally modulo a consistent renaming of local FVar IDs; module-doc
text is exact while source ranges may shift for the tooling import; derived
non-tooling module-use dependencies may shrink but may not grow.

`Experiment/run.sh` retains the legacy regression checks and now also runs all
boundary prototype commands. These are focused engineering gates, not a pinned
Mathlib closure claim.

Once that path is accepted, the public `simp_engine_apply` syntax can move from
schema-27 replay to boundary artifacts. Until then, code and reports must label
the two implementations explicitly.

The schema-1 artifact, schema-1 selector, and schema-4 shard report are now
stabilized and pass the focused, corpus-smoke, and five-module semantic gates.
The immediate next milestone is dependency-aware recording for the 66 reusable
tactic-syntax occurrences and safe composition for the 91 nested occurrences.
The current runner rejects reusable syntax and nested/overlapping replacement
ranges rather than guessing.

## Correctness contract

Let `S` be the state immediately before one dynamic source execution. Running
the original tactic with stock pinned Lean either succeeds with state `S_stock`
or fails transactionally. From the same `S`, the generated replacement must
produce a continuation-compatible `S_apply`, or fail transactionally under the
same selector conditions, without invoking simplification. The original
continuation must then elaborate and kernel-check. This rule applies equally to
proof-valued and computational declarations.

### Semantically observable call boundary

`S_stock` and `S_apply` are continuation-compatible when there is a consistent
renaming of fresh internal identifiers under which all of the following agree:

1. The tactic succeeds, fails, or closes the active goal in the same way.
   Diagnostic wording and simplifier statistics do not have to match.
2. The ordered goal list has the same length. Corresponding target types are
   definitionally equal.
3. Each corresponding goal has the same ordered local context under the
   permitted renaming: declaration kind, binder information, type, and optional
   local value. Types and values may differ only by definitional equality and
   the consistent identifier renaming. User-facing names should be preserved;
   when necessary, a consistent alpha-renaming and the corresponding rewrite of
   the continuation are allowed.
4. Every expression or universe metavariable reachable from the pre-state, the
   resulting goals, or the continuation has the same assignment status and a
   definitionally equal assignment. Fresh reachable metavariables correspond
   under the same renaming.
5. Postponed constraints, synthetic metavariables, and pending elaboration work
   have equivalent status whenever later elaboration can observe them.
6. Scoped options and continuation-visible Core, Meta, Term, and environment
   deltas agree. Elaborating a `simp` argument may create private helper
   declarations; the artifact may inline and remove them only when no later
   elaboration or generated declaration can observe the difference. Any other
   persistent change is an `external_effect_failure` until represented and
   tested generically.

Fresh goal, local, expression-metavariable, and universe-metavariable identities
need not be numerically equal. The corresponding allocator positions in
`Core.State` (`ngen`, `auxDeclNGen`, and `nextMacroScope`) are likewise internal
identities: later generated names may differ only under the same consistent
alpha-renaming, while every declaration, expression, extension entry, and other
observable consequence remains subject to this contract. Simplifier caches,
rule search order, internal candidate rollback, used-theorem counters, messages
and diagnostics, step counts, and simproc traces are outside the semantic
boundary. Raw source spelling and performance are also outside it, although
preserving surrounding source is preferred. Syntax deliberately retained as
data is an output value, not an executed call, and must remain semantically
unchanged.

The prototype must implement one paired-state comparator for this contract.
Fingerprints and hashes may route variants and improve diagnostics, but they do
not establish equality. Acceptance requires actual definitional-equality checks
performed in an isolated comparison state so that checking cannot mutate either
execution. Successful compilation of the continuation—source-identical when
possible and otherwise changed only by consistent binder alpha-renaming—is an
end-to-end oracle, but it does not replace comparison of every listed field.

### Declaration boundary and trust

Private-like proof declarations are the closed-world exception described above:
they may be added or omitted, or differ in kind, type, and metadata, but a
same-name proof/non-proof classification change fails. The following
requirements apply to every public declaration and every non-proof declaration
or command affected by translation:

- its declaration kind, safety, reducibility, level parameters, and externally
  visible attributes must agree with the original;
- its type must be definitionally equal to the original type;
- if its type is a proposition, any accepted proof is allowed by proof
  irrelevance;
- if its type is not a proposition, its elaborated value must be definitionally
  equal to the original value; this includes functions and data containing
  proof fields;
- opaque and irreducible values must compare their underlying bodies before
  sealing and retain the same opacity and compiler metadata;
- generated commands must produce an equivalent environment delta, including
  declarations, attributes, registrations, and scoped extensions;
- unsafe or runtime-oriented declarations must retain the same elaborated value
  and compiler-relevant metadata, with a dedicated runtime oracle whenever
  kernel comparison cannot cover an observable behavior;
- no result may contain unresolved metavariables or `sorryAx`;
- each public declaration's transitive axiom set must be a subset of the
  original declaration's axiom set; and
- the generated source must compile with the pinned unmodified Lean kernel.

Fewer axiom dependencies are allowed. Any necessary exception to the subset
rule must be explicitly reviewed and documented before corpus acceptance.

Definitional equality is intentionally stronger than propositional or pointwise
equality because later type checking and computation may reduce the value. A
future relaxation requires a separately reviewed observational-equivalence
oracle. For two proofs of the same proposition, Lean's proof irrelevance makes
the proof bodies definitionally equal, so original proof-term structure remains
outside the contract.

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
- `stateDeltas`, which is currently required to be exactly empty because no
  continuation-visible effect independent of the encoded transformations,
  environment actions, and consistently renamed fresh state has been admitted;
  and
- any supported observable environment action (currently reserved-name
  realization) plus a boundary-contract version.

A failure variant contains no post-state mutation and causes the replacement to
fail so that unchanged tactic alternatives behave as before. Exact error text is
diagnostic only. A pre-state fingerprinting failure, or any recording,
rendering, application, or comparison failure after stock `simp` succeeds, is
different: the recorder emits a durable
`simp_engine_boundary_recording_abort` marker through direct IO. This marker
survives an enclosing tactic alternative and makes every consumer abort; a
missing success report may be classified as unobserved only when no such marker
was emitted.

The artifact wire identity is `kind=simp_engine_boundary_artifact`,
`schema=1`, `semanticContract=boundary-observable-v1`, and
`selectorSchema=1`. Its encoding policy is `terms=lean_source_v1`,
`locals=local_decl_index_v1`, and `universes` and `instances` inferred at
application. Local references use `LocalDecl.index`, not generated FVar IDs.
Universes and instances are inferred only after an exact selector match and are
then checked by the semantic boundary and declaration/environment gates.
The four encoding literals are part of artifact-schema-1 semantics: changing
any encoding requires an artifact schema bump even though generated tactic
headers carry the schema rather than repeating those literals. The
`stateDeltas` field is currently required to be exactly empty: no independent
continuation-visible delta is admitted. Environment actions are the only
explicit effect currently supported.

### Dynamic selection rule

Selection must not construct a simp context or consult simp theorems, simproc
registries, or dischargers. The initial selector key is:

1. stable source occurrence ID (`module:startByte:endByte` hash);
2. canonical fingerprint of the pre-call state that can affect the current
   `simp` outcome, including reachable assignments and pending synthetic work;
3. a deterministic fingerprint of the full scoped Lean option map; and
4. stable caller identity: module and enclosing declaration.

The artifact's module and source occurrence ID are exact provenance, validated
before selector matching or evidence elaboration. Materializers pass the known
compiled module and manifest occurrence to the grouping validator; a
self-reported module cannot broaden the selection scope.

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

The final boundary fingerprint is defensive validation, not replay authority or
equality evidence. After selection and application, the paired-state comparator
must perform the definitional-equality checks specified above.

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
declaration-parameter alpha-renaming. A later readable renderer may retain authored
names where safe. A translator may instead alpha-rename declaration parameters and
all of their references; that fallback must preserve
binder order, binder information, and types, and the declaration-equivalence
gate must accept it before the module is counted as translated. Surrounding
tactic structure may not otherwise change merely to make materialization pass.

The syntax above is illustrative. The current parser uses the
`simp_engine_boundary_select` artifact header and machine-oriented encoded
variants described below; its durable artifact wire identity is schema 1.

## Closed-world corpus completion

The initial product claim is deliberately pinned and closed-world. A complete
run must:

1. freeze the exact Mathlib module manifest, clean-build command, environment,
   semantic-contract version, and classification version in the run manifest;
2. inventory every parsed `simp`/`simp only` node and classify it as an executed
   call, reusable executable code, retained syntax data, or unresolved;
3. collect every dynamic execution seen while compiling every module in the
   frozen manifest;
4. rewrite every executable source occurrence, independent of whether its
   enclosing declaration is proof-valued, including executable occurrences with
   no observed execution;
5. give observed executions unambiguous boundary variants;
6. give an unobserved occurrence an explicit fail-closed replacement that
   raises `boundary_occurrence_unobserved` if it unexpectedly executes;
7. compile the complete translated tree with the original continuations;
8. compare every affected declaration value and environment delta under the
   declaration-boundary rules;
9. report a syntax-aware zero count of remaining executable `simp` calls while
   separately preserving retained syntax data; and
10. archive the inventory, classifications, compilation result, declaration
    checks, environment checks, and remaining-call audit.

Scope closure uses a source-backed, two-phase probe for only the occurrences
left unresolved by the static pass. The temporary copy replaces each selected
`simp` head with an ID-carrying standalone probe, disables asynchronous body
elaboration with global `set_option Elab.async false`, and appends a report
command after the original source. The report groups repeated executions,
resolves the final declaration, and records its semantic kind, including
`Meta.isProp`, safety, reducibility, and command context; these facts select a
comparison rule rather than eligibility. It does not inspect simplifier
internals. Anonymous `example` commands are
temporarily renamed to private definitions so their final types survive
elaboration. Missing/extra IDs, missing callers or types, missing execution,
and conflicting execution roles remain unresolved. Generated commands require
explicit environment-delta classification; there is no proof-only exception.

Successful shard reports contain exactly one result for every selected
occurrence. The only successful occurrence classifications are
`materialized`, `expected_failure`, `unobserved_executable`, and
`retained_syntax_data`. Their execution and deduplicated-variant counts are
validated against the selected manifest action partition. The five abort
categories are `printer_failure`, `ambiguous_boundary_variant`,
`external_effect_failure`, `declaration_value_mismatch`, and
`environment_delta_mismatch`. An abort publishes no successful shard report;
the CLI may emit one machine-readable failure marker. The unsupported
environment-delta comparison is mapped to `external_effect_failure`, while
declaration-oracle categories are preserved unchanged. Retained syntax data must
keep its observable value and is not counted as a remaining call. If
surrounding replacements shift its source locations, the normal declaration and
environment checks must show that no semantic output changed; otherwise the
renderer must preserve the relevant positions or the closure fails.

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
6. Compare the stock and apply states with the paired definitional-equality
   comparator; use fingerprints only for selection and diagnostics.
7. Resume the original continuation, unchanged when possible and otherwise
   changed only by consistent binder alpha-renaming.
8. Compare affected declaration types, non-`Prop` values, environment deltas,
   safety/reducibility metadata, and transitive axiom sets.

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
  consumes every transformed boundary feature;
- a transparent computational definition whose value is definitionally equal;
- a non-`Prop` structure containing proof and computational fields;
- declaration-signature/default, generated-command, opaque/irreducible, and
  runtime-oriented cases; and
- a negative case whose transformed declaration compiles but has a
  non-definitionally-equal computational value.

### Prototype acceptance gate

`Experiment/check_simp_engine_boundary.py` will be the first active gate and
must establish:

- focused snapshot equivalence for every contract field;
- successful compilation with the original continuation unchanged;
- actual, non-hash definitional equality at the call boundary;
- definitionally equal declaration types and non-`Prop` values, equivalent
  environment deltas, and the axiom-subset rule;
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

1. **Complete:** replace proof-only eligibility with execution-role and
   declaration-kind classification; make all executable computational
   occurrences candidates.
2. **Complete:** replace hash equality in the boundary oracle with a paired-state
   definitional-equality comparator and complete observable pre/post state.
3. **Complete:** add declaration-value and environment-delta comparison, including opaque,
   irreducible, generated-command, and runtime-oriented cases.
4. **Complete:** revise the representative gates to transform all 17
   `AddConstMap`, 33 `EqToHom`, 6 `Fintype/List`, 7 `NonUnitalHom`, and 3
   `PosPart` occurrences, with declaration/environment oracle checks.
5. **Complete for the representative boundary:** stabilize the selector, artifact schema, failure
   classifications, local references, universes, instances, and explicit
   deltas from those measurements. Maximally human-readable rendering is
   intentionally deferred to Step 8.
6. Add dependency-aware reusable tactic handling and safe nested-range
   composition, then run increasingly large deterministic shards.
7. Require zero remaining executable calls, compile the full translated tree,
   compare declaration values/environment/axioms, and archive the closure
   report.
8. Generalize boundary artifacts for future downstream states where demand
   justifies it, then improve arguments toward maximally human-readable source
   without weakening semantic checks.

Durable report procedures are in [REPORTS.md](REPORTS.md). The focused boundary,
selector, conservative scope-classification, ID-carrying execution probe, and
explicitly authorized unobserved paths now support the measured cases and are
integrated in the representative translators. The deterministic manifest
format, bounded smoke gate, and targeted old-unknown closure are in place. The
old full-corpus eligible/excluded partition remains obsolete; the schema-2
representative manifest is current. The declaration-oracle coverage milestone
is complete for every representative module. The next milestone is
reusable/nested handling; maximally human-readable artifact rendering remains a
later Step-8 presentation task.
