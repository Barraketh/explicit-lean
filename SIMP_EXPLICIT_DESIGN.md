# Fallback-free deterministic `simp` replay

Status: revised implementation design

Scope: `simp` and `simp only` coverage in [PLAN.md](PLAN.md), section 4.1

## 1. Purpose

`simp_explicit?` must turn each committed successful `simp` or `simp only`
execution into deterministic Lean source that replays the simplifier's actual
operations. If `simp` reached a result through theorem applications,
definitional reductions, congruence traversal, and premise discharge, the
certificate must spell out those operations. A missing operation is a recorder
failure; it is not permission to replace the observed result with an exported
proof.

The prior implementation treated the proof in `Simp.Result` as a semantic
completeness fallback. It could replace one event, a whole simplification, a
presentation gap, or an enclosing tactic body with a generated equality or
proof term. That policy is superseded. Generated-result proofs can demonstrate
that an experiment reached an equivalent state, but they do not explain or
replay how `simp` reached it and therefore do not satisfy section 4.1.

The motivating production example is Centralizer occurrence
`161579b1c1009ed4`. Its hypothesis initially contains `Finsupp.sum`; the first
recorded theorem event is `Finset.mul_sum`, whose input is already a `Finset`
sum. The omitted `Finsupp.sum` reduction prevents every named-rule selector
from consuming even the first event. A whole-result equality hides that defect.
The correct repair is to record and replay the missing reduction.

## 2. Scope and deferred boundaries

The ultimate project goal remains coverage of every supported `simp` and
`simp only` occurrence. The current operational-replay milestone covers every
execution whose state changes come from:

- named simp theorems;
- theorem terms explicitly supplied by the original source;
- local hypotheses used as simp rules;
- Lean's fixed, deterministic simplifier reductions and special rules;
- congruence traversal; and
- premise programs that can themselves be expressed by these operations.

Simproc-produced transitions are a separate design problem. Until that design
is agreed, an execution containing a simproc transition is classified as
`deferred_simproc`; it is not materialized through a generated proof and does
not count as completed coverage. Arbitrary custom dischargers present the same
arbitrary-code boundary and are classified separately as
`deferred_custom_discharger` when their proof cannot be reconstructed by the
ordinary operational premise language.

This phase still does not cover `simpa`, `simp_rw`, or `simp_all`. They remain
separately inventoried inputs to later phases.

## 3. Governing invariants

### 3.1 Operational completeness

Every state change that contributes to the committed subject is represented by
a certificate command. This includes proofless or definitionally equal
transitions that only expose the next theorem redex. A successful callback in
a speculative congruence traversal is retained in the raw execution trace, but
it is not itself a committed subject transition and is classified explicitly
rather than printed as another command.

For each subject, the recorder validates transition continuity:

1. replay from the original subject reaches the input of the first event;
2. replay of each accepted prefix reaches the next event's input; and
3. replay of the complete program reaches the recorded final state.

The event inputs and results are recording-time validation data. They do not
appear in materialized source.

### 3.2 No semantic proof fallback

An accepted `simp` certificate may not contain:

- a generated equality or iff standing in for an unidentified rewrite;
- a whole-result proof;
- an aggregate `change` standing in for omitted simplifier operations;
- an exported proof of an enclosing tactic body or branch;
- a hidden invocation of `simp`, `dsimp`, `unfold`, or another search tactic;
  or
- a proof term returned by a simproc or arbitrary custom discharger merely to
  bypass their operational behavior.

The original theorem term written by the user is allowed: it is an input rule,
not a generated fallback. Kernel proof terms constructed by a fixed replay
primitive are also allowed. For example, a `delta Finsupp.sum` command may use
definitional equality to construct its equality proof; the certificate still
identifies the operation rather than serializing the final result.

### 3.3 Closed dependency surface

Replay may elaborate only recorded theorem terms, resolve recorded local
hypotheses, execute fixed reduction primitives, and run explicit nested premise
programs. It may not consult:

- the ambient simp theorem set;
- the registered simproc set;
- an ambient discharger;
- the original `simp` configuration as an execution mode; or
- automation hidden in generated `by` blocks.

Configuration remains provenance. Its effects must be visible in the selected
operations and traversal.

### 3.4 Exact consumption

Every command is consumed exactly once and in order. Replay fails when a
command is not reached, is reached at the wrong phase or subject, consumes the
wrong premise program, or needs an unrecorded transition.

The raw observer stream and executable command stream are intentionally
distinct. Repeated raw callbacks may be projected to one structural command
only when their phase, operation identity, input, and result are identical
modulo temporary traversal-binder identifiers. Ambient local variables retain
their identities. The command selects the last successful site in the group,
and the projection is accepted only when closed replay reaches the exact
recorded final subject. Omitted callbacks receive the terminal encoding
classification `nonmaterial_internal_execution`; they are never silently
dropped.

Generated source uses structural selectors. Absolute callback ticks remain
useful diagnostics while developing the recorder, but a final corpus
certificate may not depend on a tick merely because an earlier operation was
omitted.

### 3.5 Proof production

Every command produces a kernel-checked equality, iff, or proposition proof:

- rewrite commands use the recorded theorem or local rule;
- reduction commands use a fixed kernel reduction procedure;
- special-rule commands use a named, documented implementation; and
- premise programs produce the exact proposition requested by the rewrite.

The proof establishes the command's local transition. It never substitutes for
an unidentified sequence of transitions.

### 3.6 Context identity

A command identifies the target or a particular local declaration. Context
replay preserves authored location order, local-context indices, dependency
transport, local closure, and the exact final target/context state. Helpers
that perturb the local context are not allowed.

### 3.7 Printable source

Materialized source contains no metavariables, synthetic `sorry`, inaccessible
local names, or unavailable private constants. Rule references are resolved in
the replacement site's namespace and `open` context and are qualified whenever
shorter syntax would resolve differently.

Reduction commands serialize operation identity, such as a definition name or
projection, rather than a pretty-printed intermediate expression.

### 3.8 Full-body validation

An isolated replay is necessary but insufficient. A replacement is accepted
only when its complete declaration compiles. A module is accepted only when
all replacements compile together. Validation compares exact final state,
not merely provable equivalence of the final target.

### 3.9 Exact theorem attribution

An expression-changing theorem event records exactly one `SimpTheorem.origin`:
the candidate whose authoritative `tryTheoremWithExtraArgs?` call returned a
result. Candidate provenance is not reconstructed from proof terms or from
aggregate diagnostic deltas. The candidate loop retains the pinned
descending-priority order, erased filtering, and index-specific matching. For
`index := false`, extra arguments are derived under a saved and restored Meta
state before the authoritative candidate call. The exact pre and post theorem
passes are separate tracked methods; their residual methods retain the pinned
`simpMatch`, user-simproc, ground, arithmetic, and decide order. Rewrites used
while discharging a theorem premise remain premise activity, not top-level
events. Simproc transitions remain deferred.

## 4. Operational certificate model

The following Lean-like types are schematic:

```lean
inductive SubjectRef where
  | target
  | local (contextIndex : Nat) (sourceName : Name)

inductive Phase where
  | pre
  | post

inductive Selector where
  | next
  | matchOrdinal (index : Nat)

structure RuleTerm where
  source : String
  elaboratedFingerprint : String

inductive RuleRef where
  | theorem (term : RuleTerm) (inverse : Bool)
  | localRule (subject : SubjectRef) (inverse : Bool)
  | traversalLocalRule (slot : Nat)

inductive ReductionKind where
  | beta
  | eta
  | iota
  | zeta
  | projection (structureName : Name) (fieldIndex : Nat)
  | delta (declaration : Name)
  | builtin (name : Name)

mutual
  inductive PremiseTerminal where
    | isTrue
    | dischargeRfl
    | localAssumption (subject : SubjectRef)
    | equationHypothesis

  structure PremiseProgram where
    propositionFingerprint : String
    commands : Array Command
    terminal : PremiseTerminal

  structure RewriteCommand where
    subject : SubjectRef
    phase : Phase
    selector : Selector
    rule : RuleRef
    premises : Array PremiseProgram

  structure ReductionCommand where
    subject : SubjectRef
    phase : Phase
    selector : Selector
    kind : ReductionKind

  inductive Command where
    | rewrite (command : RewriteCommand)
    | reduce (command : ReductionCommand)
end

structure Certificate where
  version : Nat
  commands : Array Command

structure StateFingerprint where
  target : String
  context : Array String

structure ValidationEnvelope where
  initialState : StateFingerprint
  finalState : StateFingerprint
```

`builtin` is not an extension hook. Each accepted builtin name must have one
fixed implementation, documented semantics, and focused mutation tests. It is
intended for simplifier operations that are neither ordinary theorem rewrites
nor one of the standard kernel reductions.

Persistent JSON stores source text and alpha-stable fingerprints, not raw
position-bearing `Syntax` or `Expr`. Historical event expressions remain in
ephemeral recorder state only.

## 5. Recording model

### 5.1 Required observation boundary

Wrapping only the simplifier's top-level pre/post methods is insufficient.
Nested and proofless activity can change the expression before the first
recorded method result, as the `Finsupp.sum` example demonstrates.

The recorder must observe, in simplifier execution order:

- theorem applications from the simplifier theorem index;
- explicitly requested definition unfolding;
- beta, eta, iota, zeta, and projection reductions;
- fixed special-rule applications;
- pre- and post-method results;
- premise requests and their operational solutions; and
- congruence descent and return boundaries needed to attribute a structural
  selector to each operation.

If Lean's public simplifier API does not expose a sufficiently precise hook,
the implementation should instrument or mirror the relevant pinned Lean
simplifier functions. Approximate attribution from diagnostic deltas is not an
acceptable correctness boundary.

### 5.2 Event identity

The authority for an event is its operation identity plus its observed local
transition:

- theorem term or named fixed operation;
- direction;
- subject and phase;
- structural match ordinal; and
- ordered premise subprograms.

Diagnostics can corroborate theorem names and support reports, but they do not
fill missing transitions and do not authorize a generated proof.

### 5.3 Definitional and presentation transitions

Every definitionally equal change is classified by the operation that caused
it. The initial implementation must distinguish at least:

- named delta unfolding, beginning with `Finsupp.sum`, `rdropWhile`, and
  `rtakeWhile` from the known corpus gaps;
- beta and zeta reduction;
- iota/match reduction;
- structure projection reduction; and
- reflexive or proof-irrelevant simplifier closure.

An unknown definitionally equal gap is reported as `missing_transition`; it is
never collapsed into `change` or a reflexive whole-result proof.

### 5.4 Premises

A rewrite that requests premises records one ordered `PremiseProgram` per
request. The program is replayed with an empty ambient discharger and must
produce exactly the requested proposition. Failed probes restore both
metavariables and premise cursors.

A premise solved by assumption, reflexivity, a named theorem, deterministic
reduction, or nested simplification is expressible operationally. Exporting the
returned proof term because its derivation was not recorded is prohibited.
An arbitrary custom discharger that cannot be decomposed this way is deferred,
not papered over.

For the built-in discharger, recording mirrors Lean 4.32.2's fixed branch
order. An equation-theorem premise first tries a particular eligible local
assumption and then the fixed equation-hypothesis solver. Otherwise the
recorder captures the complete recursive `simp` execution and records whether
the residual proposition closed as `True` or by `dischargeRfl`. The selected
terminal is part of the program; replay does not rediscover one by searching
the local context or trying several closure procedures.

Premise recording is hierarchical. Events executed by recursive `simp` belong
to that premise program, including recursively requested premise programs, and
do not also appear in the enclosing subject's command stream. Candidate
failure and selector probing restore the whole hierarchy together with Meta
state.

When the source `simp` supplied a custom discharger, a successful returned
proof is not evidence that the built-in operational derivation was used. Such
a request is classified `deferred_custom_discharger`; its proof may be retained
ephemerally for diagnostics but is neither serialized nor accepted as a
certificate. This boundary can be narrowed later only by giving a particular
custom discharger its own deterministic operational specification.

### 5.5 Simprocs

The operational semantics of simprocs are intentionally not specified here.
The recorder must identify which transitions came from simprocs and retain
their names, inputs, results, and proof metadata for the later design. The
non-simproc encoder stops with `deferred_simproc` rather than translating the
result proof into a rewrite command.

## 6. Replay model

Replay uses an empty simp theorem collection, no registered simprocs, and no
ambient discharger. It interprets the certificate as a closed program.

A `traversalLocalRule` is the exact one-based declaration-index offset from
the simplifier context's recorded `lctxInitIndices`. It represents a theorem
hypothesis introduced temporarily by congruence descent (for example beneath
an implication while recording `simp +contextual`). It is not a type- or
name-based local search. Replay resolves exactly that slot in the callback's
current local context, constructs only that simp theorem, and marks the result
non-cacheable so a proof depending on one traversal binder cannot escape into
another binder scope. Ambient locals continue to use stable `SubjectRef.local`
identity and printable names.

For a rewrite command it:

1. resolves the recorded subject;
2. elaborates the recorded theorem term or local rule;
3. installs only the command's premise programs;
4. probes structural sites without committing metavariables or premise state;
5. selects the requested changing application; and
6. commits its kernel-checked result.

For a reduction command it:

1. resolves the recorded subject;
2. probes only sites where the named reduction is available;
3. counts structural matches using the same rollback discipline;
4. executes exactly that reduction; and
5. constructs and checks the local equality or iff proof.

The replay traversal uses `Simp.neutralConfig`, so beta, zeta, delta, and other
built-in reductions cannot run merely because the interpreter is implemented
on top of `Simp.mainCore`. Pinned Lean 4.32.2 needs iota enabled to expose
matcher applications to the pre-method hook, and its structural `simpProj`
path reduces native projections independently of the `proj` flag. Replay
therefore probes and rejects an iota or native-projection redex unless the
current command consumes it first. The corresponding command primitive
locally enables only the machinery required by its named kernel reduction.
In particular, pinned `reduceRecMatcher?` needs beta enabled internally to
reduce a matcher after an earlier pre-phase theorem exposes its constructor;
this does not authorize a separate ambient beta transition.

Target certificates may omit a final `eq_self` or `iff_self` diagnostic event:
closing the final reflexive residual goal is fixed behavior of the
`simp_explicit` command itself. This does not permit an earlier reduction or
rewrite to be omitted. Context subjects retain their final reflexive event
because their rewritten declaration must be transported explicitly.

At the end, replay requires complete command and premise consumption and exact
agreement with the validation envelope.

## 7. Source representation

Existing theorem syntax remains valid:

```lean
simp_explicit [
  List.drop_zero,
  match 2 => List.append_nil
]
```

O2a fixes reduction syntax as `reduce delta Name`, `reduce beta`, `reduce
zeta`, `reduce iota`, `reduce projection Structure field`, and `reduce eta`.
Reductions default to the pre phase; `↑ reduce ...` selects the post phase.
Theorem rules retain their existing post-phase default and `↓ theorem`
pre-phase spelling. Structural selectors apply to both kinds. A Centralizer
certificate should read conceptually as:

```lean
simp_explicit_context [
  at hw => [
    ↓ reduce delta Finsupp.sum,
    ↓ reduce beta,
    Finset.mul_sum,
    match 2 => Algebra.TensorProduct.tmul_mul_tmul,
    match 2 => one_mul,
    Finset.sum_mul,
    match 2 => Algebra.TensorProduct.tmul_mul_tmul,
    match 2 => mul_one
  ]
]
```

The exact selectors above are illustrative; the generated program is accepted
only after discovery and fresh-source validation. No intermediate expression
or final expression appears in the source.

Premise programs print as deterministic `have` bindings consumed by the
existing ordered `using [...]` provider. A `True` terminal prints a nested
`simp_explicit` program; `dischargeRfl` and a recorded local assumption print
their corresponding fixed Lean term or dedicated primitive; and the equation-hypothesis terminal
uses a dedicated fixed replay primitive. These forms describe the recorded
operation and are allowed to construct a kernel proof during elaboration. The
printer may not invoke `simp`, `assumption`, or another search tactic, and may
not render the authoritative proof returned by the recorder. Generated
bindings are validated with a deliberately failing ambient discharger.

For `simp at h`, multiple locations, and `at *`, source uses the existing
explicit context program. Stable local renames may precede it, but no generated
proof declaration may be inserted into the context.

## 8. Source ownership and multiple executions

One syntax occurrence can execute on multiple goals or in several tactic
branches. The recorder retains every execution with an attempt token and a
committed, backtracked, failed, or unknown disposition.

The rewriter expands common combinators into explicit branches when necessary.
It may duplicate operational certificates for the committed executions, but it
may not close an enclosing `first`, repeated body, or singleton owner with an
exported proof. If source ownership cannot be rewritten without such a proof,
the occurrence remains a `source_rewrite` coverage failure.

Unreached, originally failing, and backtracked-only occurrences receive
terminal classifications rather than fabricated certificates.

## 9. Report schema and failure taxonomy

Each occurrence report includes:

- stable module, declaration, source range, line, and column;
- original syntax and normalized configuration provenance;
- dynamic executions and dispositions;
- ordered operational event counts by kind;
- theorem, reduction, selector, and premise-program details;
- transition-continuity validation results;
- isolated, declaration, and aggregate compilation results;
- generated source size and module compile counts; and
- one terminal outcome or one primary failure category.

Terminal outcomes remain:

- `materialized`;
- `not_reached`;
- `attempted_backtracked`;
- `original_failure`; and
- `coverage_failure`.

Deferred arbitrary-code boundaries are reported separately and do not count as
materialized coverage:

- `deferred_simproc`;
- `deferred_custom_discharger`.

Primary failure categories for required non-simproc executions are:

- `missing_transition`;
- `unidentified_theorem_application`;
- `unsupported_reduction`;
- `premise_program`;
- `selector`;
- `context`;
- `source_rewrite`;
- `isolated_replay`;
- `declaration_compile`;
- `aggregate_compile`; and
- `infrastructure`.

`generated_proof`, `whole_result_proof`, `presentation_change`, and body-proof
outcomes are migration diagnostics, not successful encodings. A report that
contains one for a committed execution fails the new gate.

## 10. Corpus pipeline

The corpus pipeline remains batched:

1. Build the syntax-aware inventory once for the pinned Mathlib revision.
2. Instrument every supported occurrence in one copied module and compile that
   module once when possible.
3. Record all operational events and execution dispositions without attempting
   per-occurrence source compilation.
4. Reject transition gaps before certificate printing.
5. Encode and validate closed operational programs in-process.
6. Materialize all candidates in one optimistic module copy.
7. Partition by declaration and bisect only failing replacement groups.
8. Recompile the final accepted aggregate and store one terminal outcome for
   every occurrence.

All stages are resumable and cached by Mathlib revision, source hash,
occurrence identity, and certificate schema version. Single-occurrence
compilation is a diagnostic tool, never a semantic fallback.

## 11. Implementation sequence

Each package lands with focused tests, a bounded production fixture, the full
regression, and its own commit.

### O1. Transition continuity and fallback rejection

- Add explicit continuity checks from the original subject to the first event,
  between event prefixes, and from the last event to the final state.
- Classify the first missing transition and its structural location.
- Make generated event proofs, whole-result proofs, presentation changes, and
  body proofs fail the operational completion gate.
- Preserve the old encoders temporarily only as diagnostic comparison tools;
  they may not materialize accepted replacements.

Gate: the Centralizer occurrence is reported specifically as a missing
`Finsupp.sum` transition before any proof export is attempted, and existing
direct named-rule certificates remain accepted.

Implementation status (2026-08-21): complete. Report schema 10 separates
`acceptedCertificate` from `legacyCertificate`, applies one structured
operational-admissibility decision at recording and materialization, and
retains the first continuity gap with bounded fingerprints, selector counts,
structural path, theorem origins, and an operation hint. Speculative continuity
expressions and temporary simplifier locals do not escape their owning Meta
state; when a detailed passive report cannot render such a local, a closed,
permanently inadmissible report still preserves execution disposition. The
coverage driver never selects generated event proofs, direct premise terms,
whole-result proofs, presentation changes, first-owner proofs, or body-scope
proofs. Centralizer `161579b1c1009ed4` now reports event 0, `before_event`, path
`app.fn/app.arg`, and `delta Finsupp.sum`; direct named-rule fixtures remain
accepted. `Experiment/run.sh` passes in full.

### O2a. Deterministic reduction language and conservative public seam

- Add reduction IR, replay, selectors, source syntax, JSON, and mutation tests.
- Replay named delta, beta, zeta, iota, native projection, and eta as fixed
  primitives. On pinned Lean 4.32.2 eta is replay-only because `reduceStep`
  has no eta branch.
- Capture explicitly selected named delta at the conservative public seam.
- At the public pre-method boundary, record only reductions whose identity is
  exact and whose precedence against the pinned simplifier's earlier reduction
  cases has been checked. This seam is useful evidence, but it is not a claim
  of complete observation.

Gate: every reduction command has positive replay and wrong-kind/name/selector/
order mutation tests; the public seam records an explicitly selected
`Finsupp.sum` delta without inventing theorem provenance.

Implementation status (2026-08-21): complete. Schema 11 carries the closed
reduction IR through recording reports, source printing, selector replay, and
encoding metrics. Replay uses an inert traversal plus explicit guards for the
pinned iota and native-projection paths, and the conservative public seam
records only exact explicitly selected named deltas. The historical ten-case
DropRight presentation cohort now materializes and compiles as one operational
aggregate; Bilinear now materializes all ten occurrences, including its
contextual-binder case through the O6c local-rule certificate. Centralizer
`161579b1c1009ed4` consumes the public `Finsupp.sum` delta and the first named
event, then remains an intentional O2b coverage failure before event 2 rather
than accepting an incomplete trace. `Experiment/run.sh` passes in full.

### O2b. Pinned simplifier transition observer

- Interpose after the pinned public pre method and before private `reduceStep`,
  preserving its supported reduction precedence and returning `.visit` for an
  observed reduction so the private path cannot perform it twice.
- Classify the hardwired `simpMatch` path as iota only when its origin-free,
  proofless result exactly equals an isolated `reduceRecMatcher?` probe.
- Preserve the complete raw callback stream, including speculative congruence
  executions, while deriving an executable stream of committed operations.
- Project exact repeated local transitions to a structural `match n` command
  only when exact final-state replay validates the projection.

O2b does not claim every private `reduceStep` branch. The pinned branches for
metavariable instantiation, projection-function reduction (`reduceProjFn?`),
general `autoUnfold`, and raw natural-literal folding still lack certificate
operations. If one changes a subject, closed replay cannot reach the recorded
final state, so the occurrence remains a coverage failure rather than being
materialized. O6 must add fixed operations for any such branches reached by
the non-simproc corpus.

The split is required by the Centralizer experiment: the public seam observes
the first `Finsupp.sum` delta, but not the recursive reductions needed under
congruence traversal. The raw observer later reports 12 successful callbacks.
Four theorem callbacks are duplicate local transitions from speculative and
committed congruence sites. Replaying the first site changes no final subject;
selecting the second site does. Consequently the operational certificate has
eight commands with four `match 2` selectors, while the report retains and
classifies all 12 callbacks.

Gate: Centralizer `161579b1c1009ed4` materializes as the authoritative
`Finsupp.sum` and beta reductions plus six named theorem commands. Its raw
trace contains all ten named theorem callbacks, with four classified as
`nonmaterial_internal_execution`. No generated proof, `change`, or
unclassified callback is permitted.

Implementation status (2026-08-21): schema 12 implements the supported
recursive pre-method interposer, exact hardwired-`simpMatch` iota
classification, raw/executable callback projection, stable local-name
validation in passive context recording, and the bounded Centralizer gate.
The gate records 12 raw callbacks, emits eight operational commands with four
`match 2` selectors, and compiles the materialized full module. The same fixed
iota primitive closes both dynamic branches of the historical DropRight
`simp [h]` fixtures as event-only certificates; their enclosing source-owner
rewrite remains O5 work. `Experiment/run.sh` passes in full.

### O3. Complete theorem-event attribution

- Observe individual theorem-index applications instead of inferring a
  semantic event from aggregate diagnostics.
- Preserve source theorem terms, direction, phase, and exact structural site.
- Eliminate generated event proofs for multiple-origin and special-rule
  diagnostic clusters.

Gate: all non-simproc multiple-origin fixtures replay as individual named or
fixed builtin operations.

Implementation status (2026-08-21): complete for the pinned public rewrite
seam. Schema 13 adds exact pre/post theorem interposers that mirror Lean
4.32.2's indexed and liberal candidate loops, including stable priority order,
erased filtering, and explicit Meta-state rollback around index-false
extra-argument derivation. Each committed theorem event retains only the
selected theorem origin; abandoned candidates remain diagnostic-only, and
premise rewrites remain nested premise events. The bounded DropRight and
Subalgebra/Lattice checks compile one copied module each: the 16 historical
non-simproc multi-origin post events are now single-origin named events (with
the conditional `sup_of_le_right` event retaining `bot_le`), while two
simproc-tagged events remain deferred. The focused attribution checker asserts
schema 13, exact `Nat.sub_zero`, `List.take_length_add_append`, and
`sup_of_le_right`/`bot_le` provenance, plus an `index := false` theorem probe.
Generated proof encoding is rejected for `multiple_origins` and `special_rule`;
the synthetic `Origin.other` fixture confirms that no generated special
fallback is accepted. Exact attribution also removes the historical c9
unidentified-theorem gap: its remaining non-operational branch is now
classified precisely as an O4 direct-premise program. Lattice continuity,
reduction gaps, and simproc design remain outside O3.

### O4. Operational premise programs

- Mirror the pinned built-in discharger's branch order and record an explicit
  `isTrue`, `dischargeRfl`, `localAssumption`, or `equationHypothesis` terminal.
- Capture recursive simplifier events hierarchically and compile them into
  closed nested premise programs, including recursive premise programs.
- Remove premise proof-term export from accepted source and persistent JSON.
- Classify every source-supplied custom discharger at
  `deferred_custom_discharger` until it has a separate operational design.

Gate: premise fixtures pass with a failing ambient discharger and contain no
generated premise proof term. The multi-event `guardedEqConj` fixture is an
accepted nested program rather than `inadmissible_direct_term_premise`, and a
focused custom-discharger fixture is deferred rather than materialized.

If any recorded child transition is not yet operationally expressible, the
enclosing event is classified `inadmissible_premise_program`. Its recursive
trace remains available for coverage work, but neither an event proof nor a
whole-result proof may replace the missing child command.

Implementation status (2026-08-22): schema 14 records premise programs as a
recursive event hierarchy with explicit `isTrue`, `dischargeRfl`,
`localAssumption`, and `equationHypothesis` terminals.  Built-in discharge
follows the pinned branch order with complete recorder, Meta, and Simp
rollback at premise and candidate boundaries; source custom dischargers are
classified as `deferred_custom_discharger` without certificate or proof-term
serialization.  Accepted premise bindings rebuild their proofs from the
recorded terminal and nested commands, and proposition types use an unshared
export path so the printer cannot introduce an unrecorded zeta transition.
The focused O4 fixtures cover all four terminals, recursive premise nesting,
closed materialization, terminal-selector mutation, and passive custom
discharger classification. Premise-program gaps fail closed as
`inadmissible_premise_program` without invoking either proof exporter. Full
corpus closure and remaining simproc and context packages remain outside O4.

### O5. Fallback-free contexts and source ownership

- Apply reduction programs uniformly to targets and local declarations.
- Replace presentation `change` with the underlying reductions.
- Remove enclosing-body and singleton proof closure from materialization.
- Preserve local indices, dependent transport, multi-goal execution order, and
  backtracking dispositions.

Gate: the existing DropRight presentation, inaccessible-local, shared-body,
and first-owner fixtures materialize operationally or remain precise coverage
failures; none passes via proof export.

Implementation status (2026-08-22): the O5 gate is implemented. Target and
context subjects now use the same operational event/reduction/premise encoder;
presentation and whole-result builders are no longer called or available as
materialization paths. Non-replayable plans preserve their recursive raw trace
and report `inadmissible_operational_program` (or the more precise continuity
or premise reason) with an empty certificate. Committed `first` branches are
replaced at their own occurrence ranges while backtracked siblings remain
classified, and enclosing-body proof syntax, reports, and Python materializers
are removed. The bounded first-owner, body-scope, context, DropRight, O4, and
simp-coverage checks pass; schema 14 is unchanged apart from the explicit
`operationalProgramFailures` metric.

### O6. Non-simproc Mathlib closure

- Run the complete 83,015-occurrence `simp`/`simp only` inventory.
- Partition simproc and arbitrary custom-discharger executions explicitly.
- Fix every remaining required reason-code cluster without weakening the
  invariants.
- Compile final complete-module aggregates and publish JSON and Markdown
  summaries.

Gate: every non-deferred occurrence has a terminal outcome; every committed
successful non-simproc execution is materialized from operational commands;
there are no fallback encodings, coverage failures, or unclassified outcomes.

O6a implementation status (2026-08-22): a fresh schema-14 pilot stopped at 50
finalized modules when three module recordings exposed five deterministic
timeouts in the recorder's local premise/diagnostic definitional-equality
check. The historical 20-heartbeat cap was below the work already performed by
ordinary `simp` on these instance-heavy propositions. The check remains local
and bounded at 2,000 user-facing heartbeats, while the Unitization, Finset, and
Expect production sites now form a permanent one-compile-per-module regression.
The interrupted pilot's remaining truncated logs were cancellation artifacts,
not additional recorder failures. Full corpus closure remains O6 work.

O6b implementation status (2026-08-22): persistent event diagnostics now
render expressions below expired contextual binders through their canonical,
raw-id-free form instead of replacing the entire recording with an
unclassified placeholder. The Bilinear contextual occurrence
`5795dc0135cc7db3` therefore retains its complete raw trace for the subsequent
O6c operational replay. Separately, closure treats
a sole successful execution with no body scope or attempt token as committed:
that is the direct `by simp` case, not missing rollback metadata. The Tower
occurrence `f27035b0710b8604` now materializes and permanently guards this
distinction. Schema 14 is unchanged because neither the report shape nor the
fingerprint algorithm changed.

O6c implementation status (2026-08-22): contextual simp hypotheses introduced
only inside congruence traversal are operational rules, not proof fallbacks.
The recorder captures their positive declaration-index offset from
`Simp.Context.lctxInitIndices` while the callback local still exists. Source
prints this identity as `local_rule n`; replay resolves exactly that slot at a
matching callback, never searches the local context, and disables caching for
the resulting local-dependent rewrite. The pinned implication traversal uses
`contextual := false` and introduces the binder without `withNewLemmas` or
contextual simp search; consequence simplification runs under a fresh cache
boundary. Missing, stale, or non-theorem slots fail closed. The schema-14
Bilinear occurrence `5795dc0135cc7db3` now materializes with `local_rule 3`
and `local_rule 4`; the focused source gate rejects a wrong positive slot with
the ordered-rule mismatch diagnostic. Schema 14 is unchanged.

O6d implementation status (2026-08-22): named theorem replay now uses the
same discrimination-index candidate selection as ordinary `simp`, rather than
calling the theorem unifier directly. Recorded declaration rules are rebuilt
through the exact source-level elaboration path used by printed certificates,
and first-site selection is accepted only when its final expression and proof
are well-formed in the ambient context and reach the recorded final state.
Historical-site discovery is the bounded fallback for a rejected fast path;
it compares expired traversal locals modulo binder renaming while preserving
ambient fvar identities. The AddConstMap occurrence
`5771ee0e1343e576` now materializes with the explicit second-site command
`match 2 => AddConstMap.coe_mk`; the bare generic-rule mutation fails with the
ordered-rule diagnostic under the dual candidate path. Declaration printing
also checks resolution in the replacement site's namespace/open context and
adds `_root_.` only when the ordinary dotted name would resolve to a different
constant. Consequently the LinearEquiv occurrence `ef04e0e8339535de` now
materializes with `_root_.map_smul` instead of reaching the retired body-proof
rejection gate. Schema 14 is unchanged.

O6e implementation status (2026-08-22): schema 15 adds the exact
`projection_function` reduction command, using a local clone of Lean 4.32.2's
`reduceProjFn?` branch for both recording and replay. The
NonUnitalSubalgebra occurrence `add0ff7c330214e4` materializes through a
bounded certificate-only continuity bridge containing one pre-phase command,
`reduce projection_fn NonUnitalSubring.toNonUnitalSubsemiring`. Bridge synthesis
tries this shortest program first and retains the former `reduce zeta` plus
projection pair only as a bounded compatibility candidate. Candidate heads
come only from the matched subexpression, the full augmented program is
replay-validated, and the raw recorder trace and premise metadata remain
unchanged; no ambient simp or proof fallback is introduced. The production
gate rejects deletion, order swapping, and a different known projection
identity.

O6f implementation status (2026-08-22): a bare global theorem identifier that
is not a shadowing local now follows ordinary `simp`'s declaration path first,
preserving polymorphic universe and typeclass parameters. The same authored
theorem also gets a deterministic context-specialized term-elaboration
candidate when that term is not a plain constant; plain constants are
deduplicated to the generic candidate. Compound terms and local hypotheses
retain term elaboration, generated declaration rules validate the printed name
and use the same dual candidate path, and no ambient search or proof fallback is
introduced. The `Set.mem_neg` regression remains generic on a custom negated
type, and Spectrum occurrence `a2c03aa81fb3fb0b` materializes with seven named
rules, zero reductions, and no operational fallback. Accepted source plans
run historical discovery before the generic `.next` fast path. Schema 15 is
unchanged.

O6g implementation status (2026-08-22): projection-function recording keeps
the exact pinned Lean 4.32.2 clone from O6e. Replay uses a separate copy of the
same branch under a locally scoped Meta configuration with `beta := true` and
`proj := .yesWithDelta`, and its nested `reduceProj?` does not reinstall the
neutral simplifier configuration. This permits only the head normalization
that is part of the named projection operation; `runReplay` remains neutral,
and the pre-hook probes the pinned neutral reducer rather than this stronger
explicit operation when rejecting uncommanded reductions. The
Quasispectrum occurrence `226e61786984b7bc` materializes with two explicit
`Units.val` projection-function reductions followed by six named rules, with
zero fallback metrics. Deletion, reordering past the first theorem rule, and
identity-substitution mutations fail closed. Schema 15 is unchanged.

O6h implementation status (2026-08-22): `reduce local_def <local>` is the
explicit operation for expanding one ambient local let declaration. Its replay
identity retains the exact fvar, declaration index, accessible user name, and
stored value; it applies only to that fvar and returns only that value. It does
not run whnf, `reduceStep`, a simplifier, or name-based local lookup. The
certificate-only bridge is eligible only when continuity has already matched
the gap to that local fvar, including when the next recorded event is itself a
reduction. After insertion, the existing bounded historical-selector discovery
is rerun over the augmented trace, and exact full-result validation remains the
acceptance check. Directed occurrence `26c72cb4c4292d08` materializes as local
definition expansion, recorded zeta, and named theorem applications (including
the discovered third `Subalgebra.coe_mk` site), with zero fallback metrics.
Delete, reorder, and wrong-local mutations fail closed. Schema 15 is unchanged.

The same O6h bridge eligibility applies when the next recorded event is a
reduction rather than a theorem; consequently Lattice occurrence
`6f575c90cdb8a389` also materializes without adding another reduction kind.

O6i implementation status (2026-08-22): the exact name in `reduce
projection_fn <name>` authorizes the pinned class-projection unfolding branch.
This replaces only ordinary `simp`'s transient `isDeclToUnfold` test, which was
set by source such as `simp only [..., default]` but is absent from closed
replay. The operation still requires the current application head to be that
exact declaration, uses `withReducibleAndInstances` for the same single
unfolding, installs no simp theorem, and remains subject to historical
transition and final-state validation. Lattice occurrence
`02a5cd6ee869c03d` now materializes with explicit `Inhabited.default` reduction
and four named rules; deletion, reordering, and identity substitution fail
closed. Schema 15 is unchanged.

### S. Simproc design

Simproc handling begins only after a separate design discussion and document.
No decision about re-execution, extraction, certification, or replacement is
implied by this design.

## 12. Focused test matrix

| Behavior | Target | Named hypothesis | Dependent context | Multi-goal |
| --- | ---: | ---: | ---: | ---: |
| Named theorem | required | required | required | required |
| Delta unfolding | required | required | required | required |
| Beta/zeta/iota/projection | required | required | sampled | required |
| Multiple theorem events | required | required | sampled | required |
| Operational premise | required | required | required | required |
| Structural selector rollback | required | required | sampled | required |
| Nondefault configuration | required | required | sampled | required |
| Zero-theorem reduction-only result | required | required | sampled | required |
| Missing-transition rejection | required | required | sampled | required |
| Generated-proof rejection | required | required | required | required |

Mutation tests must change reduction names, selectors, directions, premise
program order, local subjects, and operation order and require failure at the
mutated command.

## 13. Migration from the proof-fallback baseline

Packages A through G in the earlier implementation established useful
infrastructure: passive module recording, versioned reports, structural
selectors, premise observation, stable locals, body ownership, aggregate
materialization, and exact final-state validation. Those components remain
inputs to this design.

Their proof-result encoders, whole-result encoders, presentation changes, and
body-proof materializers are no longer completion mechanisms. Existing commits
and regression fixtures remain historical evidence and migration diagnostics;
future package gates must assert that those paths were not used.

`ExplicitLean.ProofExport` remains useful elsewhere in the project and for
diagnostics. Its existence does not authorize proof export in a successful
`simp` operational certificate.

## 14. Resolved decisions

- The operational sequence, not `Simp.Result`'s aggregate proof, is the
  certificate authority.
- Every definitional presentation change is an operation to identify and
  replay.
- Missing transitions are hard coverage failures.
- Final certificates contain no generated-result, whole-result, presentation,
  or enclosing-body proof fallback.
- Premises are nested operational programs, not captured proof terms.
- Context and body rewriting preserve exact source and local-state identity.
- Simprocs are deferred to a separate design rather than silently translated
  into proof rules.
- Full aggregate compilation is the acceptance test.
