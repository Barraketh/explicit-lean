# Deterministic `simp` certificate design

Status: implementation draft

Scope: the `simp` and `simp only` coverage work in [PLAN.md](PLAN.md), section
4.1

## 1. Purpose

`simp_explicit?` must turn each committed successful `simp` or `simp only`
execution into Lean source whose replay is deterministic and does not consult
the ambient simp set. The replacement is complete only when it compiles in the
original theorem body and, after module-wide aggregation, in the original
module. Inventoried syntax that is never reached or is observed only in a
failed or backtracked branch receives an explicit terminal outcome rather than
a fabricated certificate.

The first recorder proves the basic approach, but it identifies a semantic
rewrite by looking for one changed diagnostics origin. That approximation is
the source of most current failures: a proof-producing simplifier step can have
zero, one, or several diagnostics origins; it can use a simproc; and it can
solve premises through a separate discharge procedure.

The revised design records the proof-producing result as the authority.
Diagnostics remain useful for finding a compact theorem-based encoding, but
they are never required for correctness. When no compact encoding validates,
the recorder emits a local equality or iff proof and replays that proof as an
ordinary explicit rewrite rule.

## 2. Goals and non-goals

The design has four goals:

1. Every committed successful `simp` and `simp only` execution has a
   deterministic source replacement, including calls in hypotheses, under
   tactic combinators, and across multiple goals; every other inventoried
   occurrence has a justified terminal outcome.
2. Replay uses only the certificate and named deterministic normalizers. It
   does not use the global simp set, registered simprocs, an ambient discharger,
   or the original simp configuration.
3. Compact certificates remain readable when theorem names adequately explain
   the simplification.
4. A proof-producing fallback makes semantic coverage independent of the
   quality of that compact explanation.

This phase does not try to:

- preserve the simplifier's internal traversal algorithm as a public contract;
- reconstruct one uniquely "correct" explanation from diagnostics;
- minimize every generated certificate globally; or
- cover `simpa`, `simp_rw`, or `simp_all`. They remain separately inventoried
  inputs to later phases.

## 3. Certificate invariants

Every accepted certificate must satisfy all of the following invariants.

### 3.1 Closed dependency surface

Replay may elaborate named theorem terms and invoke explicitly named
normalizers. It may not consult:

- the active simp theorem set;
- the registered simproc set;
- the caller's discharger;
- the caller's `simp` configuration; or
- search tactics hidden in generated `by` blocks.

Generated proof terms may rely on ordinary declarations and local hypotheses,
as any Lean proof does.

### 3.2 Exact consumption

Every recorded command is consumed exactly once and in order. Replay fails if
it finishes with an unused command, reaches a command at the wrong phase or
subject, or needs an unrecorded rewrite or premise proof.

### 3.3 Proof authority

Each semantic rewrite carries, directly or through a named theorem, a proof of
the equality or iff used to transform the expression. The kernel remains the
final authority. Diagnostics counters and traversal observations are metadata,
not evidence.

### 3.4 Context identity

A command identifies whether it changes the target or a particular local
declaration. Context replay preserves dependency order and updates later local
declarations when the type of an earlier declaration changes.

### 3.5 Printable source

Materialized source contains no metavariables, synthetic `sorry`, inaccessible
local names, or references to private constants that are unavailable at the
replacement site. Generated names are deterministic and collision-checked.
Every declaration reference is rendered and re-elaborated in the replacement
site's namespace and `open` environment, using a fully qualified or `_root_.`
qualified name whenever shorter syntax would resolve differently.

### 3.6 Full-body validation

An isolated replay is necessary but not sufficient. A certificate is accepted
only after its rewritten complete declaration compiles. A module is accepted
only after all materialized replacements compile together.

## 4. Internal representation

The implementation should separate its internal representation from the
current parser syntax. The following types are schematic Lean, not a commitment
to exact constructor or field names:

```lean
inductive SubjectRef where
  | target
  | local (name : Name)

inductive Phase where
  | pre
  | post

inductive Selector where
  | next
  | matchOrdinal (index : Nat)
  | traversalTick (tick : Nat)

structure RuleTerm where
  source : String
  elaboratedFingerprint : String

inductive RuleRef where
  | theorem (term : RuleTerm) (inverse : Bool)
  | localProof (name : Name) (inverse : Bool)

structure PremiseRef where
  binding : Nat

structure RewriteCommand where
  subject : SubjectRef
  phase : Phase
  selector : Selector
  rule : RuleRef
  premises : Array PremiseRef

structure NormalizerInvocation where
  name : Name
  arguments : Array RuleRef

inductive Command where
  | rewrite (command : RewriteCommand)
  | normalize (subject : SubjectRef) (invocation : NormalizerInvocation)

inductive BindingKind where
  | premise
  | rewrite

inductive ProofSource where
  | nestedCertificate (id : Nat)
  | term (proof : Expr)

structure Binding where
  name : Name
  type : Expr
  kind : BindingKind
  source : ProofSource

structure Certificate where
  id : Nat
  bindings : Array Binding
  commands : Array Command

structure CertificateBundle where
  version : Nat
  certificates : Array Certificate

structure StateFingerprint where
  target : String
  context : Array String

structure ValidationEnvelope where
  certificate : Nat
  initialState : StateFingerprint
  finalState : StateFingerprint
```

The actual serialized report should use a versioned JSON equivalent of this
model. `Expr` values require both a diagnostic pretty-printed form and an
alpha-stable fingerprint. Rule terms likewise store canonical source text and
the fingerprint of their elaborated proof; persistent reports do not store raw
position-bearing `Syntax`. Only generated Lean source is used for replay.

The program remains linear. A nested premise certificate is referenced through
a proof binding in the enclosing bundle, so the main rewrite cursor does not
become a tree-walking protocol. Bundle-local numeric IDs do not appear in
generated Lean source. The validation envelope is recorder and report metadata,
not certificate syntax.

## 5. Recording model

### 5.1 Semantic events

The recorder wraps the pre- and post-methods used by the original simplifier.
For every method call it records:

- the input expression;
- the phase and absolute diagnostic tick;
- the returned `Simp.Step`;
- the changed `Simp.Result`, including its proof when present;
- diagnostics deltas as candidate origins; and
- any premise proofs requested while producing that result.

A semantic event exists when the returned result changes the input expression.
The returned result, not the number of changed origins, defines the event.
When `Simp.Result.proof?` is absent because the change is definitional, the
recorder constructs and kernel-checks the corresponding reflexive equality or
iff proof before encoding the event.

The recorder also captures the simplifier's final result even when there are no
semantic events. This is needed to diagnose presentation changes that affect a
following tactic.

### 5.2 Event encoding

Each semantic event is encoded using the first candidate below that validates
against the recorded input and result:

1. one named theorem or local theorem;
2. an ordered group of named theorem or local theorem applications at the same
   redex;
3. a generated local equality or iff proof derived from the recorded
   `Simp.Result`.

Candidate origins from diagnostics are used only in the first two cases. A
candidate validates only when closed replay produces the recorded output and a
kernel-checked proof. If an origin is noisy, incomplete, or unprintable, the
encoder proceeds to the proof fallback.

An ordered group is an encoding optimization, not a new replay primitive. The
printer may render it as consecutive rewrite commands or collapse it to one
generated proof binding, whichever produces smaller validated source.

### 5.3 Proof export

The proof fallback should promote the proof-export work currently prototyped in
`Experiment/Main.lean` into a reusable expression-rendering library. It must
handle proof bodies, theorem and binding types, and goal types used by `change`
or transport fallbacks. Before printing, it must:

- instantiate all metavariables;
- abstract only locals that are in scope at the replacement site;
- inline inaccessible private constants when possible;
- assign stable source names to otherwise inaccessible locals;
- share repeated subterms when that reduces rendered size; and
- reject placeholders and synthetic `sorry`.

The fallback is allowed to be verbose. Its purpose is to make coverage
complete; named rules and later normalizers provide compression.

## 6. Replay model

Replay uses fixed, certificate-specific simplifier methods. There is no ambient
simp theorem collection and no registered simproc collection.

For each rewrite command, replay:

1. resolves its subject in the current goal state;
2. elaborates only the recorded theorem term or local proof binding;
3. installs the recorded premise provider;
4. finds the selected pre- or post-phase application;
5. checks that the application consumes all recorded premise proofs; and
6. applies the returned equality or iff to the subject.

At the end, replay checks that all commands and bindings have been consumed and
that every selected rule produced a proof-carrying change. During recording and
materialization, the validation driver additionally compares the resulting
target and context with the final state in the validation envelope. That
out-of-band check reports the command index, subject, phase, expected
fingerprint, and actual fingerprint. Emitted source does not contain historical
intermediate or final expressions.

Named normalizers such as `normalize_category` remain proof-producing commands
in the same linear program. A normalizer transition is accepted only after the
same final-state validation as an exact rewrite segment. Any `using [...]`
arguments are stored as explicit `RuleRef` values in the invocation; a
normalizer command never obtains extra rules from the ambient simp set.

## 7. Source representation

The current syntax remains valid:

```lean
simp_explicit [
  ↓ List.drop_zero,
  11 => List.append_nil
]
```

The bare numeric selector is retained as compatibility syntax for an absolute
traversal tick. New generated source should spell selectors explicitly:

```lean
simp_explicit [
  ↓ List.drop_zero,
  match 2 => List.append_nil,
  tick 11 => h_rewrite_1
]
```

Here `match 2` means the second callback site, in the requested phase, where
the recorded rule applies and changes the current expression using exactly the
command's premise proofs. It does not compare with a hidden expected
expression. Counting starts at one. Probes clone metavariable state and the
premise cursor so unsuccessful candidates have no effects. The selected
application is then committed. `tick 11` is the exact callback tick fallback.

The printer omits a selector when ordinary ordered replay validates. It prefers
`match` over `tick`, and uses `tick` only when the structural selector cannot
distinguish the recorded event.

When the recorded simplifier leaves a definitionally reflexive target open for
the following tactic, generated source spells that final-state choice rather
than silently applying `rfl`:

```lean
simp_explicit leave_open [rule_1, rule_2]
```

Ordinary `simp_explicit [...]` retains its compatibility behavior of closing a
reflexive final target. The recorder selects `leave_open` only when the
original `simp` execution itself did not close, and full-state validation
checks the resulting open target before materialization.

Generated proof bindings appear immediately before the certificate in the
smallest source scope containing all uses:

```lean
have h_premise_1 : P := by
  simp_explicit [rule_for_P]
have h_rewrite_1 : lhs = rhs := by
  exact exported_proof
simp_explicit [
  rule_with_premise discharging [h_premise_1],
  h_rewrite_1
]
```

The exact parser spelling of `discharging` is an implementation detail to
settle in the premise-prototype work package. The semantic rule is fixed: the
listed proofs are ordered, proposition-checked, and fully consumed.

For hypothesis locations, generated source uses an explicit context program:

```lean
simp_explicit_context [
  at h => [rule_1, rule_2],
  at k => [rule_3],
  at target => [rule_4]
]
```

This is the serialized result of `simp at h`, `simp at h k ⊢`, or `simp at *`;
replay never executes a wildcard location. A target-only context program may be
printed with the shorter `simp_explicit` syntax.

## 8. Known failure categories

### 8.1 Multiple recorded origins

Several diagnostics origins may correspond to one returned `Simp.Result`.
They are attempted as a validated ordered group. If grouping does not reproduce
the exact result, the event becomes one generated equality or iff binding.
There is no requirement to assign a unique origin to the step.

### 8.2 Discharged side conditions

The recording discharger wraps the original discharger. When it returns a
proof, the recorder stores the requested proposition and proof before returning
that proof to the original simplifier.

The encoder first tries to express that proof as a nested certificate. If that
does not validate or would require unsupported automation, it exports the proof
term. Replay uses a closed provider that returns only the next listed proof
after checking its type against the requested proposition. It first uses a
cheap structural comparison and then, when needed, bounded definitional
equality under ordinary heartbeat accounting. It never calls the original or
ambient discharger; a timeout is a structured premise-validation failure.

### 8.3 Simprocs and special rules

A simproc is a recording-time implementation detail. Its returned
`Simp.Result` is encoded exactly like any other semantic event: preferably by a
recognized named theorem, otherwise by a generated proof binding. Replay never
invokes the simproc.

Reflexive closure and other special rules may be omitted only when the closed
replayer reaches the same final result definitionally and consumes every other
command. Otherwise they also use an explicit proof binding.

### 8.4 Traversal failures

The preferred identity of a rewrite is `(subject, phase, rule,
match-ordinal)`. This is more stable than the number of unrelated simplifier
callbacks encountered first. Absolute ticks remain a last-resort certificate
field because some rules can match indistinguishable sites whose earlier
rewrites affect traversal.

A prototype must demonstrate that rule probing can be performed without
committing metavariables or consuming premise proofs before this selector is
made the printer default. The ordinal counts rule applications that change the
current expression; it never consults a recorded output expression.

### 8.5 Hypothesis locations

The certificate state consists of a metavariable target plus an ordered local
context. User-named declarations are referenced by their source names. Generated
or inaccessible declarations receive deterministic names such as
`h_explicit_1`, chosen in local-context order and checked for collisions.

After simplifying a local declaration's type, replay uses Lean's metavariable
context operations to replace that declaration and transport dependent later
declarations. It records the resulting declaration mapping rather than keeping
raw `FVarId` values in source or JSON.

For `at *`, the recorder stores the actual ordered sequence of affected local
declarations and the target. The generated context program spells out that
sequence. This makes context mutation reviewable and independent of future
changes to wildcard traversal.

### 8.6 Configurations and custom dischargers

The original configuration influences recording only. Its semantic effect is
captured by the resulting commands, selectors, and proof bindings. Replay has
no configuration mode.

The report retains the original syntax and a normalized configuration summary
for provenance. If a configuration changes a result that cannot be reconstructed
by compact commands, proof-result fallback is used. Custom dischargers follow
the premise-proof design above.

### 8.7 Unprintable local facts

The body rewriter, rather than the event printer, owns local naming. It assigns
names at the smallest enclosing tactic sequence where the local exists and
updates certificate references structurally. It must not perform textual name
replacement over raw source.

If a usable source name cannot be introduced without changing elaboration, the
event is represented by a generated rewrite proof that abstracts over the
available named locals instead of naming the inaccessible fact directly.

### 8.8 Nested and multi-goal use

One source occurrence can execute more than once and on more than one goal.
The coverage report therefore stores an ordered array of executions, each with
an execution index, goal fingerprint, initial context fingerprint, and
certificate. Recording instrumentation assigns an attempt token and brackets
enclosing combinator branches with completion markers so the report can
distinguish committed results from failures and restored backtracking states.
If that status cannot be established, the occurrence is a `coverage_failure`;
the driver does not guess that an attempt committed.

The source rewriter rewrites the smallest enclosing tactic construct that owns
those executions. For common combinators, it expands implicit distribution
into explicit goal branches. For example, a shared tactic under `<;>` can
become separate bullet-local certificates. Goal order and fingerprints are
then validated by compiling the complete declaration.

For backtracking combinators such as `first` and repeated tactics, the rewriter
preserves the successful branch as straight-line proof source. If it cannot do
so safely, it exports the smallest enclosing proof fragment as a proof term.
Replay does not add goal-shape search or branch selection.

### 8.9 Zero-event presentation changes

A simplifier call with no recorded semantic events is not automatically a
no-op. Reducible unfolding or conversion can leave a presentation expected by
the next tactic even when the isolated target is definitionally equal.

The same fallback applies when a call has later semantic events but an
unrecorded definitional transition is required to reach the first event (or to
move between two recorded events). Such a trace is not a valid linear event
certificate merely because its recorded premise and rewrite steps are
individually replayable.

Full-body compilation decides this case. On failure, the body rewriter may emit
an explicit `change` justified by definitional equality, an equality/iff
transport, or an exported proof for the smallest enclosing fragment. The
recorder must classify which fallback was used rather than silently deleting
the call.

For corpus closure, whole-body proof export is an on-demand fallback only after
an occurrence-level candidate has been isolated as `materialized_body_rejected`.
It is eligible only when the inventoried body owns exactly one supported
occurrence in the current module entry set. The exporter abstracts unresolved
elaboration metavariables to inferred proof arguments; inaccessible locals are
made printable with exact context-index/name commands. The resulting body
candidate is accepted only when the final aggregate compile succeeds. The
earlier optimistic aggregate failure and the proof-export/final-aggregate
attempts remain in the closure audit record.

## 9. Source rewriting pipeline

The coverage driver should batch work by module while preserving per-occurrence
identity:

1. Parse the complete module and assign a stable ID to every occurrence and its
   enclosing declaration and tactic combinators.
2. Instrument all supported occurrences in one fresh module copy with a passive
   recorder that preserves the original tactic result and reports recording
   problems without aborting the module.
3. Compile that copy once and collect every dynamic execution, including its
   occurrence ID, attempt outcome, and semantic trace. If instrumentation
   itself causes a hard module failure, partition the module's occurrences and
   retry only the failing shards.
4. Encode and validate traces in-process with the closed replayer and validation
   envelopes.
5. Search for shorter mixed programs using registered deterministic
   normalizers.
6. Introduce proof bindings and stable local names in enclosing bodies, and
   rewrite combinators when one occurrence served several goals.
7. Apply all candidate replacements to a fresh module copy and compile that
   optimistic aggregate once.
8. If aggregate compilation fails, partition first by declaration and then
   bisect only failing replacement groups. Use single-occurrence compilation as
   the final diagnostic fallback, not the normal execution path. Only an
   isolated `materialized_body_rejected` occurrence with an exact singleton
   body owner may trigger the on-demand whole-body proof export.
9. Recompile the final accepted aggregate and store a terminal outcome for
   every occurrence. A fallback proof is materialized only when that final
   aggregate compiles; the failed optimistic attempt remains auditable.

All stages are resumable and cached by pinned Mathlib revision, module source
hash, occurrence identity, and certificate schema version. Aggregate rewriting
is based on source ranges or syntax identities from the original file, not on
sequential substring replacement. Reports include module compile counts, wall
time, and CPU time so corpus closure has a visible compute budget.

## 10. Report schema and failure taxonomy

The JSON report needs a schema version and, per occurrence:

- stable source identity: module, declaration, byte range, line and column;
- original syntax and normalized configuration provenance;
- zero or more dynamic execution records, each with a result (`succeeded` or
  `failed`) and, when applicable, a disposition (`committed` or `backtracked`);
- event counts by semantic kind and encoding kind;
- emitted bindings and certificate source;
- selector use (`next`, `match`, or `tick`);
- isolated replay, declaration compilation, and module compilation results;
- generated source byte counts;
- one terminal occurrence outcome; and
- for coverage failures, one primary failure category plus structured stage
  details.

Terminal occurrence outcomes are mutually exclusive:

- `materialized`: at least one successful execution committed and every such
  execution has a validated replacement;
- `not_reached`: the occurrence had no dynamic execution;
- `attempted_backtracked`: at least one execution succeeded, but every
  successful execution belonged to a failed or abandoned tactic branch;
- `original_failure`: the occurrence was reached but no execution of the
  original tactic succeeded; and
- `coverage_failure`: recording, encoding, replay, source rewriting, or
  compilation failed for a committed successful execution, or instrumentation
  could not establish the required execution outcome.

Primary failure categories should remain stable enough for trend reports:

- `recording`;
- `proof_export`;
- `premise`;
- `selector`;
- `context`;
- `source_rewrite`;
- `isolated_replay`;
- `declaration_compile`;
- `aggregate_compile`; and
- `infrastructure`.

The current descriptive labels, such as multiple origins or discharged side
conditions, become reason codes nested under these stages. No failure may be
reported only as unclassified stderr. Terminal non-failure outcomes are not
counted as materialized replacements and must be reported separately.

## 11. Implementation sequence

Each work package must land with focused tests and a bounded coverage run. The
order below follows dependency rather than current failure frequency.

### A. Semantic trace and versioned certificate IR

Status: implemented on 2026-08-20.

- Replace `RecordedEvent.origin` as the authority with the input and returned
  proof-producing result.
- Retain origin deltas as candidate metadata.
- Add validation envelopes, terminal execution outcomes, JSON serialization,
  and precise cursor mismatch diagnostics.
- Make whole-module passive recording the default corpus path.
- Preserve all current target-only theorem certificates.

Gate: existing replay tests and the four successful `DropRight` replacements
still pass, all 24 `DropRight` occurrences can be passively recorded in one
module compile, and multiple-origin events are reported without aborting that
compile.

The bounded gate records 27 dynamic executions under the 24 stable occurrence
IDs in one compile. The versioned report retains proof-producing
`Simp.Result`s, candidate-origin arrays, premise observations, alpha-stable
state fingerprints, nullable execution disposition, and validation envelopes.
Nine top-level events have multiple candidate origins and four carry
discharged premises. Reentrant method activity is retained in its enclosing
event's provenance rather than duplicated as a main-cursor event. Raw
recording deliberately leaves terminal outcomes unset; the
coverage driver may assign them only after materialization and, for branching
uses, after Package F can establish commitment.

### B. Generated rewrite-proof fallback

Status: implemented on 2026-08-20.

- Promote and harden the proof exporter from `Experiment/Main.lean` as a
  renderer for proof terms and types.
- Encode multiple-origin, simproc, and special-rule results through named rules
  when possible and proof bindings otherwise.
- Add source-size and encoding-kind metrics.

Gate: the four target-local multiple-origin failures in the `DropRight`
baseline (`df0c0dff00516f2a`, `f582f1aac3e05ab2`, `22c673bcce0f227e`, and
`220c8550c1042081`) materialize, and dedicated simproc and special-rule
fixtures replay with an empty ambient simp/simproc environment. The original
eight-way diagnostic bucket also contained two executions whose whole-result
proof mentions an inaccessible case binder; those close in Package E. Its two
remaining occurrences execute under `<;>` on more than one branch and close in
Package F. This partition is based on the semantic recorder, not on the old
diagnostic-origin count.

The reusable exporter now renders both proof terms and their declared types in
the replacement namespace, preserves the recorded redex type for
definitionally reflexive proofs, shares profitable subterms, and rejects
metavariables, synthetic `sorry`, inaccessible locals, and residual private
constants. Schema version 3 reports event and whole-result proof fallbacks with
source-size and premise-binding metrics, plus premise provenance. All four
Package B `DropRight` replacements compile both
in isolation and together. A real `pushFun` simproc fixture materializes a
certificate that contains no ambient simproc invocation, and a lower-level
`Origin.other` fixture validates the same public proof-result encoder and
closed replayer. The complete `Experiment/run.sh` regression passes.

### C. Recorded premise proofs

Status: implemented on 2026-08-21.

- Record proposition/proof pairs from the original discharger.
- Add the closed ordered premise provider.
- Support nested certificates and proof-term fallback for bindings.
- Report bounded definitional-equality timeouts distinctly.

Gate: focused fixtures materialize both nested-certificate and proof-term
premise bindings, reject missing, mismatched, and unconsumed providers, and
replay when the relevant simp theorem and discharger are not ambiently
registered.

The four single-execution `DropRight` occurrences originally classified as
discharged-side-condition failures (`03210e4a7b3567e3`, `aaf54961bf787d28`,
`739c7ac9dd3cd521`, and `90925e8b6e53287f`) have a layered failure: premise
provenance is now separated and replayable, but an unrecorded definitional
unfold is required before the first semantic event. Their existing
whole-result fallbacks remain compile-checked here; compact event closure moves
to Package F's presentation-gap work. The fifth old diagnostic,
`c9eca03fcd0280ed`, also closes in Package F because one source occurrence
executes in both branches of `<;>`.

The recorder now stores each successful discharger request with its proof and
diagnostic-origin delta, subtracting that multiset from the enclosing rewrite
event. Schema version 3 reports premise provenance, deterministic binding
names, encoding kinds, and source-size metrics. Generated source attaches an
ordered closed provider with `using [...]`; replay performs a structural type
check followed by bounded reducible definitional equality, restores
metavariables and the provider cursor after every rejected probe, and requires
exact premise consumption before committing a rule. Permanent fixtures compile
both a nested `simp_explicit` premise certificate and a direct ProofExport term
fallback, plus missing, mismatched, and unconsumed-provider mutations. The four
layered `DropRight` cases retain their premise traces and compile individually
and together through the deferred whole-result fallback. The complete
`Experiment/run.sh` regression passes.

### D. Structural selectors

Status: implemented on 2026-08-21.

- Implement side-effect-free rule probing whose ordinal counts applications
  and does not inspect a recorded expected expression.
- Add `match` and explicit `tick` syntax while retaining numeric compatibility.
- Prefer the shortest validated selector during printing.

Gate: focused fixtures require a structural `match` selector, exercise explicit
`tick` and legacy numeric compatibility, verify skipped probes do not leak
metavariable assignments or consume premise proofs, and make selector
mutations fail at the exact command. Existing position-free certificates must
remain position-free.

The six `DropRight` occurrences originally classified as traversal failures
(`bdfebd4de6e5f543`, `f578fdc66fc0399a`, `e72c0cbdffdb90b1`,
`7a1c618c3a39b1cb`, `3acd3e1c76ad7f24`, and `e0e91bd09649e027`) also begin
with an unrecorded unfold of `rdropWhile` or `rtakeWhile`. Their selector layer
is implemented here and their existing whole-result fallbacks remain
compile-checked; compact event closure moves to Package F with the other
presentation gaps.

Replay now distinguishes selector-free `next`, structural `match n`, and
absolute `tick n` commands. A structural probe counts only exact-premise,
proof-carrying applications that change the expression, and restores both
metavariables and premise-provider state at every rejected or skipped site.
The encoder first validates a selector-free program, then discovers structural
ordinals using the recorded input and result only inside the encoder, replays
the emitted expression-free program, and finally falls back to explicit ticks.
Legacy numeric ticks still parse, while newly generated source always spells
`tick` explicitly.

Schema version 4 reports the nullable selector kind and value for each encoded
event, aggregate counts for `next`, `match`, and `tick`, and treats
`positionsNeeded` as meaning that an absolute tick was actually emitted.
Permanent fixtures cover `match`, explicit and legacy ticks, phase and ordinal
mutations, zero selectors, theorem-metavariable rollback, and premise-provider
rollback. The six layered `DropRight` cases retain nonempty semantic traces and
compile individually and together through their documented whole-result
fallbacks without falsely reporting selector commands. The complete
`Experiment/run.sh` regression passes.

### E. Stable locals and context programs

Status: implemented on 2026-08-21.

- Deterministic, collision-checked local naming emits one exact-index
  `simp_explicit_rename` prefix and sanitizes the complete report under the
  renamed local context. Exact-index replay is idempotent: an entry already
  carrying its requested printable name is a no-op, while an absent index or a
  collision with another local is an error. Generated base names include that
  stable context index, so different locals cannot receive the same name from
  independently recorded certificates. This lets certificates generated
  independently within one declaration compose without `rename_i` consuming a
  different set of inaccessible locals on each invocation.
- Closed `simp_explicit_context` records and replays authored local order,
  target locations, `at *`, dependent-local transport, local closure, and
  zero-event subjects; passive location recording rolls back before running the
  original `simp` once.
- Fresh-clone validation compares the complete context program and preserves
  actual fvar transport identities and alpha-stable fingerprints.

Gate: focused fixtures cover a single hypothesis, multiple hypotheses, a
dependent later hypothesis, an inaccessible local fact, and `at *`.
The gate also materializes `f3d6dce9ae772ce2` and `54d6b0e3b2ad8e41` from the
`DropRight` baseline in isolation and together; both generated whole-result
proofs require naming an inaccessible `cases` binder. The bounded regression
retains all 24 stable occurrences and their 27 dynamic executions in one
passive compile, and the complete `Experiment/run.sh` regression passes.

### F. Enclosing-body and multi-goal rewriting

Status: implemented on 2026-08-21.

- Store all dynamic executions for one source occurrence.
- Distinguish committed, failed, and backtracked attempts.
- Expand common tactic combinators into explicit branches.
- Add smallest-fragment proof export and presentation-change fallbacks.

Schema v6 assigns attempt tokens inside rollback-aware body scopes and
classifies each successful execution as committed or backtracked. Syntax
inventory records exact owners for `<;>`, `all_goals`, `repeat`, `repeat'`, and
`first`; the materializer expands shared committed executions into explicit
bullets and reports terminal outcomes for unreached, backtracked-only, and
originally failing occurrences. A closed `first` owner can export its exact
input-goal assignment as the smallest enclosing `exact` proof, without
straightening an outer tactic body.

The encoder also performs one bounded presentation-only simplifier pass. It
removes recorded proof-bearing theorem origins from the original context,
rolls back rejected proof-bearing method results, requires a structurally
different but definitionally equal whole-goal candidate, and validates the
complete parenthesized `change` plus event program on a fresh clone. Named
events under traversal binders are constructed without an invalid event-local
context check, but are accepted only after complete ordered replay and
fresh-source validation succeed.

Gate: fixtures cover `<;>`, `all_goals`, a repeated occurrence, a backtracking
branch, and the `DropRight` zero-event presentation failure. It also
materializes `c485b5d0b1a08fac` and `754e9f44f095fc5d`, the two baseline
occurrences whose one source `simp` executes in both branches of `<;>`, plus
the similarly shared premise-bearing occurrence `c9eca03fcd0280ed`. Its
presentation-gap gate also closes compact event programs for
`03210e4a7b3567e3`, `aaf54961bf787d28`, `739c7ac9dd3cd521`, and
`90925e8b6e53287f`, whose premise layer was completed in Package C, together
with `bdfebd4de6e5f543`, `f578fdc66fc0399a`, `e72c0cbdffdb90b1`,
`7a1c618c3a39b1cb`, `3acd3e1c76ad7f24`, and `e0e91bd09649e027`, whose
selector layer was completed in Package D.

The gate passes. The three shared `DropRight` owners compile in isolation and
together after explicit branch expansion. Of the ten deferred presentation
sites, eight compile with `presentation_change` programs and two with direct
event programs; none retains a whole-result fallback. The two Package E
inaccessible-local sites also now compile as renamed event programs. Focused
fixtures cover all required combinators and terminal classifications, and a
mutation check rejects a changed smallest-owner proof. The bounded one-compile
recording regression and the complete `Experiment/run.sh` regression pass.

### G. Corpus closure

- Run all 83,015 supported `simp` and `simp only` occurrences.
- Fix reason-code clusters without weakening replay invariants.
- Run module aggregates and publish the generated Markdown summary.

The bounded closure driver retains one passive module compile and uses
whole-body proof export only for an isolated singleton rejection. Exact body
ownership prevents a fallback from claiming another supported occurrence in
the same body. Proof export abstracts unresolved elaboration metavariables to
inferred arguments and emits exact-index local naming for inaccessible locals;
the final aggregate compile, rather than the optimistic attempt, is the
acceptance check and both attempts are retained in the audit record.

Gate: every occurrence has a terminal outcome; every committed successful
execution is materialized and compiles in its complete module; aggregate
compilation passes; and the report contains no `coverage_failure` or
unclassified outcome.

## 12. Focused test matrix

The permanent test suite should cross semantic behavior with source context:

| Behavior | Target | Named hypothesis | Dependent context | Multi-goal |
| --- | ---: | ---: | ---: | ---: |
| One theorem, no premise | required | required | required | required |
| Multiple origins | required | required | sampled | required |
| Discharged premise | required | required | required | required |
| Simproc result | required | required | sampled | required |
| Structural selector | required | required | sampled | required |
| Proof fallback | required | required | required | required |
| Nondefault configuration | required | required | sampled | required |
| Zero-event presentation | required | sampled | sampled | required |

Tests that claim ambient independence should remove or replace the relevant simp
registration in a controlled fixture, not merely use `simp only`. Tests for
premises should install a failing ambient discharger during replay.

## 13. Implementation spikes and resolved decisions

The following decisions are part of the design:

- `Simp.Result` proofs are authoritative; diagnostics are compression hints.
- explicit proof bindings are the semantic completeness fallback;
- premise proofs are captured and replayed in order;
- wildcard hypothesis locations are expanded to explicit subjects;
- match ordinals count source-reconstructible rule applications and are
  preferred to traversal ticks;
- recorded final states live in validation envelopes rather than emitted
  certificate syntax;
- whole-module recording and optimistic aggregate materialization are the
  normal corpus paths;
- unreachable, failed, and backtracked occurrences receive explicit terminal
  outcomes rather than fabricated certificates;
- multi-goal behavior is made explicit in the surrounding source; and
- full-body compilation, not isolated target equality, is the acceptance test.

Three short API spikes remain before their corresponding packages:

1. Verify that a candidate simp theorem can be probed under saved metavariable
   state without leaking assignments or consuming a premise cursor.
2. Verify proof extraction for built-in simproc and special-rule results across
   equality, iff, and proof-of-proposition simplification.
3. Select the Lean metavariable-context API that most directly replaces a local
   declaration while transporting its dependents.

These spikes can change internal API choices or surface punctuation. They do
not change the certificate invariants or fallback strategy.
