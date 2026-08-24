# Pinned `simp` engine coverage and certificate architecture

Status: implementation specification; E1 through E5 complete

Pinned engine: Lean 4.32.2, commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`

Scope: successful `simp` and `simp only` executions covered by
[PLAN.md](PLAN.md). `simpa`, `simp_all`, `simp_rw`, and `rw` remain
separate phases. Simprocs are observed and classified here, but their replay
semantics remain a separate design.

## 1. Verdict

The superseded schema-15 event IR was not a complete model of Lean's simplifier.
It observes the public `pre` and `post` method boundary and reconstructs some
private reductions around that boundary. Lean's implementation has additional
semantic boundaries:

- a separate `dpre`/`dpost` definitional simplifier;
- reductions in `reduceStep`, `reduceFVar`, and structural projection code;
- recursive match-discriminant simplification inside `simpMatch`;
- generic, generated, and user congruence selection;
- specialized lambda, forall, implication, let, and have-telescope traversal;
- fixed `decide`, arithmetic, and ground-evaluator procedures; and
- goal and hypothesis transport after expression simplification.

The replacement is a pinned instrumented copy of the simplifier's execution
engine. It records at the points where the engine commits operations and
structural choices. Replay uses the same pinned engine with an explicit program
driver, no ambient simp or congruence sets, no simprocs, and no ambient
discharger.

No full-corpus run is warranted until the implementation obligations in
section 10 pass. A corpus run before then would only discover the next missing
observer branch.

## 2. Correctness contract

For one dynamic execution, let:

- `S` be the initial proof state and selected subjects;
- `C` be the elaborated original `simp` context;
- `R(C, S)` be the result of the pinned upstream simplifier;
- `record(C, S)` produce an explicit certificate `P`; and
- `replay(P, S)` be the closed certificate interpreter.

An accepted certificate must establish all of the following.

1. **Engine equivalence.** The uninstrumented mode of the pinned fork produces
   the same expression, proof-presence mode, cache flag, used-theorem set, goal
   closure, hypothesis transport, and resulting proof-state fingerprint as the
   upstream implementation.
2. **Trace totality.** Every committed expression-changing leaf operation and
   every structural choice needed to reach it has exactly one representation
   in `P`. A failed candidate is also in `P` when it performed recursive or
   cache-relevant executable work.
3. **Closed replay.** Replay consults only the recorded program, recorded rule
   terms, exact local identities, fixed kernel/meta primitives, and the local
   elaboration environment required to typecheck those terms.
4. **Exact consumption.** Every operation, structural witness, premise program,
   and subject program is consumed once, in order, at its recorded execution
   path.
5. **Exact result.** Replay reaches the recorded final state fingerprint and
   reproduces the recorded result's proof-presence mode where that mode changes
   goal or local-context transport.
6. **Source validity.** The printed certificate reconstructs the same `P` when
   elaborated at the replacement site, and the entire declaration and aggregate
   module compile.

`Simp.Result.proof?` is evidence checked by the recorder, not an alternative
certificate. A result proof may never replace an unidentified operation.

## 3. The pinned execution model

The authoritative source surface is:

- `Lean/Elab/Tactic/Simp.lean` for context construction and locations;
- `Lean/Meta/Tactic/Simp/Main.lean` for recursion and structural traversal;
- `Lean/Meta/Tactic/Simp/Rewrite.lean` for rules, builtins, and discharge;
- `Lean/Meta/Tactic/Simp/Types.lean` for state, configuration, and congruence;
- `Lean/Meta/Tactic/Simp/SimpTheorems.lean` for rule preprocessing;
- `Lean/Meta/Tactic/Simp/Simproc.lean` for simproc candidate execution;
- `Lean/Meta/Tactic/Simp/SimpCongrTheorems.lean` and
  `Lean/Meta/CongrTheorems.lean` for congruence selection;
- `Lean/Meta/Transform.lean` for the definitional traversal; and
- `Lean/Meta/HaveTelescope.lean` for have-telescope simplification.

At one expression node, `simpLoop` executes this state machine:

1. consult the expression cache and enforce the step bound;
2. execute `pre` and honor `done`, `visit`, or `continue` exactly;
3. execute one `reduceStep`; a change restarts at step 1;
4. structurally simplify the expression with `simpStep`;
5. execute `post` and honor its step result; and
6. unless `singlePass` or unchanged, restart at step 1.

Every `simp` and `dsimp` entry receives a call-frame identity. This is required
because recursive helpers can revisit the same semantic child path. Every
pre/post phase invocation also ends with a `phaseOutcome`, including unchanged
`done`/`continue` results; absence of a changing event is not enough to recover
control flow.

Cache visibility follows Lean's staged `SExprMap`, `withFreshCache`,
`withPreservedCache`, and linearly threaded dsimp-cache scopes exactly.
Producer entries themselves use an append-only execution registry, and each
hit records both the producer path and registry ordinal.
The ordinal is necessary because isolated premise attempts can repeat the same
qualified path and expression fingerprint; neither field alone identifies a
cache value.

The ground evaluator is a nested engine context, not merely another phase. It
uses the pinned seval configuration, methods, theorem environment, and an
isolated simp cache. Replay installs the same fixed configuration with empty
ambient rule sets, consumes the nested program under `ground`, and restores the
outer cache. Lazily generated equation theorems inside that context are
reconstructed from the matcher at the current replay expression and the
recorded equation index, then checked against the recorded rule and lhs
fingerprints. The recording-time matcher name is diagnostic provenance only:
private matcher names can change when a source tactic is materialized.

Structural traversal recursively calls either `simp` or `dsimp`. `dsimp` is a
different state machine based on `transformWithCache`: it has `dpre` and
`dpost`, skips selected instance arguments, introduces locals for telescopes,
and runs repeated definitional reduction after `dpost`.
Each recorded dsimp phase outcome covers the complete upstream phase pipeline:
`dpre` includes the fixed literal/proof guards, and `dpost` includes
definitional reduction. Replay executes the recorded phase program directly;
it does not append those fixed stages a second time.

This means that a flat list of successful `pre`/`post` callbacks is not an
execution model. It is only one projection of the execution.

## 4. Implementation-to-IR coverage matrix

The `Required representation` column is normative for certificate schema 18.

| Upstream site | Committed behavior | Required representation | Schema 15 |
| --- | --- | --- | --- |
| `simpImpl` call boundary | Recursive calls may share the same semantic child path, and proofs stop before `simpLoop` | `simpCall` identity and an explicit `proofSkip` terminal | absent |
| `dsimpImpl` call boundary | Recursive definitional calls may share the same semantic child path | `dsimpCall` identity | absent |
| `simpLoop` cache | Reuses a prior result and can suppress a second traversal | call-qualified structural `cacheHit` with the producing path and exact execution-registry ordinal | implicit |
| `pre` step | `done`, `visit`, `continue none`, and `continue some` have different control flow even without a changing operation | exact `phaseOutcome` for every invocation | partial |
| `post` step | May finish or restart the entire node | exact `phaseOutcome` plus the call-qualified restart edge | partial |
| `simpStep`: unassigned mvar | Stops structurally when instantiation makes no progress | explicit `unassignedMVarStop` terminal | absent |
| metadata traversal | Both simp and dsimp recurse through `.mdata` wrappers | explicit `metadataBody` child path | absent |
| `reduceStep`: mvar head | Instantiates assigned metavariables | `instantiateMVars` reduction | absent |
| `reduceStep`: beta | Head beta reduction | `beta` reduction | present |
| `reduceStep`: native projection | Reduces `.proj` | exact structure/field projection | present only when `config.proj` exposes it in the pre interposer |
| `reduceStep`: projection function | Class/structure projection paths, including explicitly requested class projection unfolding | projection declaration plus branch (`requestedClass`, `constructorClass`, or `structure`) | partial |
| `reduceStep`: iota | Reduces recursor/matcher | `iota` reduction | present |
| `reduceStep`: zeta | Expands a used let/have | `zetaUsed` with `zetaHave` mode | collapsed into `zeta` |
| `reduceStep`: unused let | Drops a nondependent unused let | `zetaUnused` | collapsed into `zeta` and not always observed |
| `unfold?`: requested | Smart, partial-application, or ordinary unfolding | declaration plus unfolding strategy | only ordinary named delta |
| `unfold?`: auto | Smart unfolding or match-definition unfolding | declaration plus `autoSmart` or `autoMatch` strategy | absent |
| `foldRawNatLit` | Repackages an orphan raw Nat literal | `foldRawNatLit` builtin reduction | absent |
| `reduceFVar` | Expands zeta-delta, requested, or implementation-detail local definitions | exact fvar/context index/value fingerprint plus reason | inferred only by O6 bridges |
| `simpProj` | Reduces a projection even outside the `reduceStep` config branch, otherwise simplifies or dsimps its major | projection structural choice plus child mode | incomplete |
| `simpApp` | Chooses user congruence, generated congruence, or generic congruence | exact `CongruenceChoice` and child modes | ambient congruence set |
| failed congruence candidates | A failed user/generated attempt may already have recursively simplified children or changed replay-relevant caches | ordered `userAttemptFailed`/`generatedAttemptFailed` choice when the attempt has executable progress | absent |
| user congruence | Selects a named `[congr]` theorem, simplifies designated hypotheses, and synthesizes remaining side premises | theorem fingerprint, match envelope, priority/variant, hypothesis paths, and nested side-premise programs | absent |
| generated congruence | Computes argument kinds, may synthesize subsingleton instances and remove dummy casts | generated theorem identity/shape, argument kinds, and synthesis fingerprints | implicit |
| generic congruence | Simplifies independent args, dsimps dependent/fixed args, and may skip instances | per-argument `simp`, `dsimp`, or `fixed` path | implicit |
| `simpMatch` direct reduction | Iota before ordinary `reduceStep` | `iota` reduction at `pre` | present |
| `simpMatchDiscrs?` | Recursively simplifies only matcher discriminants | `matchDiscriminants` structural choice and child programs | nested events suppressed |
| failed match-discriminant candidate | Simplified discriminants may fail to produce a matcher reduction after changing replay-relevant state | `matchDiscriminantsAttemptFailed` structural terminal | absent |
| `simpMatchCore` | Tries matcher equation theorems | exact equation theorem rule | only if aggregate origin inference succeeds |
| lambda traversal | Dsimps binder domains, introduces locals, simplifies body | telescope structural path and scoped local identities | implicit |
| implication traversal | Optionally installs antecedent as a contextual simp theorem and resets cache | contextual structural path and traversal-local rule identity | one hand-written implication special case |
| forall traversal | Has proposition-domain transport, dsimp-domain, and non-proposition branches | exact forall branch and scoped child programs | implicit |
| dependent let | Optional `letToHave`, otherwise whole-expression dsimp | `letToHave` structural operation or dsimp child program | absent/inferred |
| have telescope | Computes fixed/used sets, drops unused haves, dsimps fixed values, simps other values/body | fixed/used bitsets, drop operations, and scoped child programs | absent/inferred |
| `dpre`/`dpost` | Applies rfl-only theorems and dsimprocs | `dpre` and `dpost` phases | absent |
| `dsimpReduce` | Repeats all definitional reductions, then `reduceFVar` | the same exact reduction vocabulary in dsimp mode | absent |
| dsimp transform | Uses a separate cache, telescope reconstruction, `usedLetOnly`, and instance skipping | `DSimpPath` structural witnesses and config | implicit |
| theorem preprocessing | One source rule may produce several actual simp theorems, and equation theorems may be generated lazily | source declaration/equation index when needed, lhs/rule fingerprints, and an ordinal among fingerprint-identical variants | all variants retried under one origin |
| indexed rewrite | Discrimination lookup, priority, erased set, extra args | selected rule plus `index` mode, variant, and exact `numExtraArgs` | mostly present |
| theorem match | Unification, permutation orientation, binder hints, no-op rejection | match/instantiation envelope fingerprints | result-only validation |
| failed theorem candidate | Premise simplification may execute before synthesis, no-op, or orientation failure | `rewriteAttemptFailed` with its exact rule, match envelope, and nested premise programs | absent |
| instance arguments | May synthesize typeclass arguments before premise discharge | ordered binder assignment fingerprints | implicit elaboration |
| implicit defeq proof | Changes `proof?` and therefore local transport | recorded proof-presence mode and matching config | only indirectly inherited |
| recursive premise simp | Runs the complete simplifier recursively | nested full `Program`, not only pre/post events | partial |
| default discharge terminals | Assumption, equation solver, recursive simp, rfl, `True`, or failed discharge | exact terminal and nested program | present for current observed subset |
| custom discharger | Arbitrary tactic code | `deferred_custom_discharger` until separately specified | deferred |
| `simpUsingDecide` | Fixed decision procedure with true/false outcome | `decideTrue` or `decideFalse` builtin | unidentified special event |
| `simpArith` | Nat/Int relation, equality, expression, or divisibility normalization | exact arithmetic handler variant | unidentified special event |
| `simpGround`/`seval` | Runs a nested theorem/simproc environment and ground discharger | nested ground program; any simproc leaf defers the execution | opaque aggregate event |
| pre/post simprocs | Ordered simproc candidates and step semantics | exact simproc observation and `deferred_simproc` | only aggregate detection |
| dsimprocs | Simprocs in definitional traversal | exact dsimproc observation and `deferred_simproc` | invisible |
| target result | Closes `True` or transports/replaces target | subject terminal | present |
| local result | Closes on `False`, defeq-replaces, or stages asserted hypotheses | subject terminal and proof-presence mode | mostly present |
| `simpGoal` batching | Erases each local rule while simplifying itself, preserves authored location order, asserts then clears | ordered `SubjectProgram` list and exact transport | present |
| `failIfUnchanged` | Tactic-level failure after all subjects | replay configuration plus the identical final goal-identity check | present as provenance only |

The matrix is complete only for the pinned source files named in section 3. A
Lean upgrade requires regenerating this matrix against the new call graph and
changing the engine identifier.

## 5. Certificate IR v2

The executable authority is a structural program. Fingerprints shown below are
alpha-stable hashes; raw `Expr`, `FVarId`, and position-bearing `Syntax` remain
ephemeral recorder data. Expression fingerprints erase proof subterms before
canonicalization; proof presence is represented separately wherever it changes
control flow or transport.

```lean
structure EngineId where
  leanVersion : String
  leanCommit : String
  certificateSchema : Nat

inductive Mode where
  | simp
  | dsimp

inductive Phase where
  | pre
  | post
  | dpre
  | dpost

inductive PathStep where
  | simpCall (ordinal : Nat)
  | dsimpCall (ordinal : Nat)
  | preVisit (iteration : Nat)
  | reductionVisit (iteration : Nat)
  | postRestart (iteration : Nat)
  | projectionMajor (mode : Mode)
  | appFunction
  | appArgument (index : Nat) (mode : Mode)
  | userCongrHypothesis (theorem : Name) (index : Nat)
  | autoCongrArgument (index : Nat) (mode : Mode)
  | matchDiscriminant (index : Nat) (mode : Mode)
  | lambdaDomain (index : Nat)
  | lambdaBody
  | forallDomain (index : Nat)
  | forallBody
  | metadataBody
  | implicationDomain
  | implicationBody
  | letType (index : Nat)
  | letValue (index : Nat) (mode : Mode)
  | letBody
  | haveValue (index : Nat) (mode : Mode)
  | haveBody
  | premise (index : Nat)
  | ground

structure ExecutionPath where
  steps : Array PathStep

inductive RuleOrigin where
  | decl (name : Name)
  | equation (declaration : Name) (index : Nat)
  | syntax (source : String)
  | local (subject : LocalRef)
  | other (name : Name)

structure RuleRef where
  source : String
  origin : RuleOrigin
  inverse : Bool
  phase : Phase
  variant : Nat
  ruleFingerprint : String
  lhsFingerprint : String
  indexMode : Bool
  numExtraArgs : Nat

structure MatchEnvelope where
  binderAssignments : Array String
  instanceAssignments : Array String
  proofPresent : Bool

inductive Reduction where
  | instantiateMVars
  | beta
  | projection (structureName : Name) (field : Nat)
  | projectionFunction (name : Name) (branch : ProjectionBranch)
  | iota
  | zetaUsed (zetaHave : Bool)
  | zetaUnused
  | delta (name : Name) (strategy : DeltaStrategy)
  | foldRawNatLit
  | localDef (subject : LocalRef) (reason : LocalDefReason)

inductive Builtin where
  | decideTrue
  | decideFalse
  | arith (handler : ArithHandler)

mutual
  structure PremiseProgram where
    propositionFingerprint : String
    program : Program
    terminal : PremiseTerminal

  inductive CongruenceChoice where
    | user (theoremName : Name) (priority : Nat)
        (hypothesisPositions : Array Nat) (theoremFingerprint : String)
        (matchEnvelope : MatchEnvelope) (premises : Array PremiseProgram)
    | userAttemptFailed (theoremName : Name) (priority : Nat)
        (hypothesisPositions : Array Nat) (theoremFingerprint : String)
        (matchEnvelope : MatchEnvelope) (premises : Array PremiseProgram)
    | generated (theoremTypeFingerprint proofFingerprint : String)
        (argumentKinds : Array GeneratedCongruenceArgKind)
        (arguments : Array ChildMode)
        (synthesizedAssignments : Array String)
    | generatedAttemptFailed
    | generic ...

  inductive Structural where
    | phaseOutcome (phase : Phase) (invocationOrdinal : Nat)
        (disposition : StepDisposition) (outputFingerprint : String)
        (proofPresent : Bool)
    | proofSkip (invocationOrdinal : Nat) (typeFingerprint : String)
    | unassignedMVarStop (simpStepOrdinal : Nat)
    | cacheHit (sourcePath : ExecutionPath) (sourceIndex : Nat)
    | congruence (invocationOrdinal : Nat) (choice : CongruenceChoice)
    | projectionMajor (structureName : Name) (field : Nat) (mode : ChildMode)
    | matchDiscriminants (count : Nat)
    | matchDiscriminantsAttemptFailed (count : Nat)
    | lambdaTelescope (count : Nat)
    | forallBranch (choice : ForallBranch)
    | contextualScope (locals : Array ScopedLocalRef)
    | letToHave
    | haveTelescope (fixed used : Array Bool)
    | dropUnusedHave (index : Nat)
    | dsimpCacheHit (sourcePath : ExecutionPath) (sourceIndex : Nat)
    | dsimpTransform (usedLetOnly skipInstances : Bool)

  inductive Operation where
    | rewrite (rule : RuleRef) (match : MatchEnvelope)
        (premises : Array PremiseProgram)
    | rewriteAttemptFailed (rule : RuleRef) (match : MatchEnvelope)
        (premises : Array PremiseProgram)
    | reduce (reduction : Reduction)
    | builtin (builtin : Builtin)

  structure Event where
    path : ExecutionPath
    phase : Phase
    invocationOrdinal : Nat
    operation : Operation
    inputFingerprint : String
    outputFingerprint : String
    stepDisposition : StepDisposition

  structure Program where
    initialFingerprint : String
    finalFingerprint : String
    structural : Array (ExecutionPath × Structural)
    events : Array Event
end

structure SubjectProgram where
  subject : SubjectRef
  initialFingerprint : String
  program : Program
  terminal : SubjectTerminal

structure Certificate where
  engine : EngineId
  config : ReplayConfig
  subjects : Array SubjectProgram
  initialState : StateFingerprint
  finalState : StateFingerprint
```

The `iteration` values in `preVisit`, `reductionVisit`, and `postRestart` are
trace-local ordinals. They are allocated from recorder state and roll back with
a failed speculative candidate; they are deliberately not `Simp.State.numSteps`,
which Lean may advance during work that leaves no certificate event. Cache
provenance and passive simproc observations are operational state outside that
rollback boundary. If a speculative candidate produces a cache entry, its
failed-attempt witness is retained so replay executes the same cache producer.

### 5.1 What is and is not source

The schema-18 source payload is compact JSON embedded in a shallow Lean array
of string literals:

```lean
simp_engine_apply "occurrence-id"
  (certificates := #["{...schema-18 certificate...}", ...]) originalSimpArgs
```

The JSON contains the complete path-qualified operations and structural
witnesses. It never contains intermediate expressions; input and output hashes
are validation fields. Every emitted payload is parsed immediately and compared
structurally with the in-memory certificate before it is accepted. At the
replacement site it is parsed again, its engine identity is checked, and closed
replay validates its initial and final states.

Expression fingerprints hash Lean's shared expression DAG directly with
memoization; they never expand it into a canonical tree. Proof erasure is part
of that traversal, and every public fingerprint operation saves and restores
the meta-state so observation cannot affect later simplifier choices. A
per-engine cache reuses fingerprints for repeated simproc candidate inputs.
Recursive premise recording starts with empty observation buffers and merges
only the premise's new observations into the outer execution; copying the
outer prefix into a nested trace would duplicate it exponentially.

Cache producer registries contain only the recorded producer path and its
append-only ordinal. The live expression cache and its lockstep provenance map
remain authoritative for key equality and value lookup. An alpha-stable
expression fingerprint is relative to the current local context, so the same
cached expression can legitimately acquire a different fingerprint after a
binder scope closes; such a fingerprint is not a valid cache-key witness.

The ordered simproc trace is serialized losslessly as a dictionary of distinct
observations plus an array of dictionary indices. The index array has one entry
per invocation and therefore preserves exact multiplicity and order while
avoiding repeated JSON objects. Source decoding reconstructs and structurally
compares the original ordered trace.

`Name` is encoded as an ordered array of tagged string and numeric components.
This is lossless for generated private declarations; Lean's standard JSON name
codec and name-quotation syntax are not. It also makes rule identity independent
of the replacement site's namespace and `open` declarations.

One syntax occurrence can execute more than once under tactic combinators. Its
replacement therefore carries an array of dynamic certificates and selects the
unique certificate whose recorded initial proof-state fingerprint matches the
current state. Equal duplicates are harmless; different certificates for the
same state are rejected as ambiguous. No mutable execution counter participates
in replay.

Nested source occurrences compose by replacing only the leading `simp` token
of each occurrence, never an enclosing byte range. Recording leaves its already
verified upstream result in the proof state, so elaborating a nested tactic for
an outer explicit rule does not execute it a second time. Explicit-rule origin
identity canonicalizes the recording and materialization wrapper nodes back to
their underlying `simp` syntax. This canonical string is used only to identify
the theorem already elaborated in the source context; replay does not execute
the canonicalized `simp` text.

The reference/recording comparison is a full tactic-elaboration transaction.
Its snapshots include the tactic goals, term-elaborator synthetic metavariables
and pending constraints, and meta/core state. Restoring only `Meta.SavedState`
is insufficient for a source tactic because it can leak term-elaboration work
into the following declaration even when the resulting proof state matches.

The retained original simp arguments reconstruct the authored theorem terms,
configuration, and location subjects. They do not authorize ambient simp,
congruence, simproc, or discharger selection; traversal and operation selection
remain certificate-driven.

The existing `next` and `match n` syntax may later be retained as a compressed
encoding only when elaboration expands it into the same structural `Program`
and validates the same hashes. It is not the authority used to infer missing
events.

The source form includes the engine id and final-state hash. Rule terms include
their variant and elaborated fingerprint so a compound rule, a preprocessed
conjunction, or a differently resolved name cannot silently select a different
theorem.

## 6. Replay configuration

Replay cannot simply use `Simp.neutralConfig`: that changes structural behavior
and theorem matching. Nor may it run the original configuration with ordinary
methods, because that would permit unrecorded reductions and builtins.

`ReplayConfig` is therefore explicit certificate metadata with two roles.

1. It supplies the pinned structural and matching semantics: `contextual`,
   `memoize`, `singlePass`, `dsimp`, `zetaUnused`, `zetaHave`, `letToHave`,
   `congrConsts`, `instances`, `ground`, `index`, `implicitDefEqProofs`, and
   `etaStruct`, plus the meta flags used by exact theorem matching.
2. It records which original reduction/builtin switches were enabled, so a
   recorded operation can be checked against its original eligibility.

It also includes the normalized semantic projection of the pinned
`Context.metaConfig` and `Context.indexConfig`. Those configurations originate
in the ambient `Meta.Config`, then `Simp.mkContext` overrides beta, iota, zeta,
zeta-have, zeta-unused, zeta-delta, structure eta, projection, and transparency.
Recording only `Simp.Config` is therefore insufficient: replay validates the
complete resulting matching/index configuration before applying a rule.

The pinned engine reads several options outside `Simp.Config`. Their treatment
is fixed as follows.

| Option | Semantic effect | Certificate treatment |
| --- | --- | --- |
| `backward.dsimp.instances` | Forces instance traversal | folded into the effective `instances` field produced by `Simp.mkContext` |
| `backward.dsimp.proofs` | Allows dsimp to visit proof terms | explicit replay-config field |
| `backward.whnf.reducibleClassField` | Selects a class-projection reduction branch | projection branch identity plus replay-config field |
| `smartUnfolding` | Changes requested unfolding and smart-declaration use | delta strategy plus replay-config field |
| `backward.defeqAttrib.useBackward` | Makes backward-defeq rules eligible and changes implicit-proof behavior | rule eligibility/proof mode plus replay-config field |
| `backward.dsimp.useDefEqAttr` | Changes rfl/backward-rfl theorem classification | stored rule classification and replay-config field |
| `tactic.skipAssignedInstances` | Changes theorem-argument synthesis | match-envelope and replay-config field |
| `simprocs` | Enables registered simprocs/dsimprocs | exact deferred-simproc observation; never enabled in replay |
| diagnostic/warning/check options | Emit traces, warnings, or extra type checks only | provenance only; excluded from execution config |

Any newly observed option read in the pinned fork fails the source-diff audit
until it is added to this table or proved diagnostic-only.

The replay driver command-gates every changing `reduceStep`, `reduceFVar`,
structural projection, `dpre`, `dpost`, decide, arithmetic, and ground branch.
If the pinned engine can change the current expression but the next program
item does not authorize that exact change at that exact path, replay fails
before the implicit branch runs.

Options used only for diagnostics do not affect execution. User-config options
consumed by a simproc cause `deferred_simproc`; options consumed by a fixed
builtin are represented by that builtin's explicit witness.

## 7. Pinned instrumented engine

The implementation lives in a new module, separate from the 6,000-line tactic,
and carries the upstream Apache license header and pinned commit.

It is a source-level fork of the relevant execution code, not a reimplementation
from observed examples. It uses Lean's public `Simp.Context`, `Simp.State`,
`Simp.Result`, theorem matching, proof constructors, and caches. Private
execution functions are copied with only these controlled changes:

- recursive calls go through the fork;
- each committed leaf operation emits an `Event`;
- every phase invocation emits an exact outcome, even when no leaf changes;
- every recursive simp/dsimp call extends the execution path with a call frame;
- each structural branch emits or consumes a structural witness;
- exact user-congruence selection is recorded at the successful candidate;
- `Meta.simpHaveTelescope` runs through a small wrapper monad whose
  `MonadSimp` instance calls the fork;
- simproc candidate loops report every invoked opaque candidate, including
  `continue none`, before returning a deferred boundary; and
- record and replay drivers share the same execution code.

Three engine modes are required.

- **Reference mode:** no observer decisions; used to compare the fork with
  upstream `Simp.mainCore`.
- **Record mode:** uses the original context, records successful choices, and
  promotes failed/speculative attempts with executable progress into the
  program.
- **Replay mode:** receives choices from the certificate, has empty ambient
  simp/congruence/simproc sets and no ambient discharger, and fails on any
  uncommanded transition.

The fork is the version boundary. We do not continue accumulating local clones
of individual private reductions inside `SimpEngine.lean`.

## 8. Rules, congruence, and premises

### 8.1 Rules

The recorder stores the actual `SimpTheorem` variant that succeeded, not merely
its `Origin`. Rule and lhs fingerprints identify the preprocessing output, and
an ordinal disambiguates fingerprint-identical duplicates. Lazily generated
equation rules retain the recording matcher for provenance and use the equation
index as their semantic selector. Replay obtains the current matcher from the
expression, reconstructs that indexed equation, and validates its rule and lhs
fingerprints; it does not require generated private names to survive source
materialization. Candidate ordering is relevant only while recording; an
explicit replay operation does not consult an ambient theorem tree.

Certificate-selected rule application first uses upstream's ordinary matching
configuration. If that fails, replay retries lhs unification with local-let
unfolding enabled. This covers representation drift where the recorded subject
has unfolded a let explicitly named in the simp arguments while the authored
rule still mentions the local let. The retry cannot select another rule: rule
and lhs fingerprints, variant, match envelope, output fingerprint, and phase
outcome remain mandatory.

For authored compound rule terms, replay searches only the explicit theorem set
elaborated from the retained original arguments. Instrumentation wrappers in a
nested tactic are normalized for origin comparison, then rule/lhs fingerprints
and the variant ordinal select the recorded theorem. The normalized source is
never elaborated as a fallback.

The match envelope validates ordered binder and instance assignments. Replay
may use Lean's unifier and typeclass synthesis to construct those assignments,
but it must agree with the recorded fingerprints before the operation commits.

### 8.2 Congruence

Ambient `getSimpCongrTheorems` is prohibited during replay. Record mode emits
one of:

- the exact user congruence theorem and hypothesis positions;
- the generated congruence theorem type, proof, exact argument kinds, child
  modes, and synthesized assignments; or
- generic congruence with each argument's `simp`, `dsimp`, or fixed mode.

Replay executes that choice directly. A user congruence theorem is resolved and
fingerprinted like an ordinary rule. Generated congruence may use the pinned
generator, but its generated type, proof term, exact argument kinds, child
modes, and synthesized assignments must match the witness before its child
programs run.

Failed user/generated candidates are recorded when they performed recursive or
cache-relevant work. Their failure is replayed before the next candidate. A
candidate with no executable progress is omitted; call frames, phase outcomes,
and certificate-driven cache hits ensure that omitted meta allocation identity
cannot become replay semantics.
Upstream catches hypothesis-processing exceptions while it speculatively tries
user congruence candidates. Replay retains that behavior only for a recorded
failed attempt. Once the certificate selects a successful candidate, nested
replay-validation failures propagate instead of being misclassified as a new
candidate failure and hidden behind a match-envelope mismatch.

### 8.3 Premises

A recursive premise is a complete nested `Program`, including dsimp and
structural witnesses. Default terminal selection remains explicit:
`localAssumption`, `equationHypothesis`, `dischargeRfl`, `isTrue`, or `failed`.

Failed theorem candidates that contain recursive premise work are explicit
`rewriteAttemptFailed` operations with nested premise programs and a `failed`
terminal. A candidate that produced no executable program item is omitted. A
custom source discharger remains `deferred_custom_discharger` whenever it is
invoked, regardless of whether it proves the premise.

## 9. Simproc boundary

This design does not decide how a simproc transition will eventually replay.
It does require exact detection, including:

- pre and post simprocs;
- dpre and dpost dsimprocs;
- simprocs invoked by ground/seval; and
- simprocs inside recursive premise programs.

The instrumented candidate loop records every invoked simproc candidate's
declaration name, phase, input/output fingerprints, step disposition, and
nesting path, then classifies the enclosing execution `deferred_simproc`.
This includes `continue none`: opaque simproc code may recursively simplify and
mutate `Simp.State` caches before returning no result. Such cache entries are
allowed only inside an already simproc-deferred recording and are never
replayed. No result proof is materialized. This makes the non-simproc
completeness gate honest without prematurely choosing simproc semantics.

## 10. Implementation obligations and gates

Each stage is committed before the next begins.

### E1. Reference engine

- Add the pinned fork in reference mode.
- Compare upstream and fork results for every focused fixture, then compare
  final proof states while the source gate records complete modules.
- Compare expression, proof presence, cache flag, used theorems, diagnostics,
  subject closure, and final state.

Gate: zero equivalence mismatches; no certificate or corpus behavior changes.

Status: complete. The fork is pinned by hashes of the complete authoritative
source surface, the focused reference probe covers both `simp` and `dsimp`
branches, and the complete-module source gate rejects any upstream/fork final
proof-state mismatch.

### E2. Total structured recorder

- Add schema-18 paths, structural witnesses, all four phases, total reduction
  identities, exact congruence choices, rule variants, match envelopes, and
  full nested premise programs.
- Add exact simproc/dsimproc observation and deferred classification.
- Remove continuity-bridge synthesis from accepted recording.

Gate: branch-focused tests cover every row of section 4. Deleting any observer
call causes its focused test to fail with `unobserved_transition`.

Status: complete. The recorder covers every matrix row, retains stateful failed
candidate attempts, emits nested premise programs, observes all
simproc/dsimproc phases without accepting them, and matches reference-mode
results on the focused probe and complete-module source gate.

### E3. Closed structural replay

- Add replay mode to the same engine.
- Empty all ambient simp, congruence, simproc, and discharger dependencies.
- Command-gate every changing branch and validate exact path and hashes.
- Preserve exact proof-presence mode and subject transport.

Gate: every branch-focused certificate replays; mutations of path, phase,
operation, rule variant, congruence choice, config, premise order, or terminal
fail at the mutated item.

Status: complete. The focused suite replays 37 dynamic branch classes and
rejects 21 targeted mutations. Complete-module classification and replay are
tested once through the source materialization gate instead of a parallel
record/replay harness.

### E4. Source and materializer migration

- Print and parse the schema-18 source form.
- Include engine id, rule fingerprints, and final-state validation.
- Switch passive recording and context programs to the new engine.
- Keep the source and materializer independent of removed historical bridge
  and selector-discovery implementations.

Gate: all existing non-simproc focused/production fixtures materialize through
schema 18 with zero bridge, generated-proof, presentation, or whole-result
metrics. `Experiment/run.sh` passes.

Status: complete. Each module is instrumented once for all occurrences, every
serialized execution is structurally round-tripped, and complete materialized
copies are compiled. The focused fixture and eleven complete Mathlib modules
contain 341 occurrences: 158 materialize across 182 successful executions, 182 are
explicitly simproc-deferred, and one executes unsuccessfully inside `first`.
The focused gate covers nested source calls, private qualified rule
names, recursive premises, multiple executions of one occurrence, authored
locations, configuration-driven builtins, and lazy-equation origins in both an
isolated ground context and a generated matcher whose private name changes
during source materialization. A source-only engine-schema mutation is rejected
before replay. A trailing `+contextual` fixture requires multiline certificate
payloads to preserve the tactic's offside-rule column. `EventuallyConst.lean`
retains a cache-hit regression in which the producer's binder is no longer in
the local context at the later hit. `Ordinal/Notation.lean` retains the
successful `ite_congr`/auto-congruence case where a nested dsimp phase must
explicitly unfold numeric literals exactly once.
`Probability/Process/Stopping.lean` retains an authored local rewrite whose lhs
mentions a let-bound set after the recorded subject explicitly unfolds it.
`AlgebraicGeometry/Morphisms/SurjectiveOnStalks.lean` retains structure
projection reductions whose major expression exposes a constructor only after
zeta-delta reduction of an explicitly supplied local let declaration.
`Data/Multiset/Functor.lean` retains eta-expanded authored rewrite rules whose
discrimination-index result supplies an extra-argument count that cannot be
reconstructed from the rule lhs application arity.
`Data/Vector3.lean` retains a source context that locally rebinds list notation;
certificate arrays therefore print through `Array.empty` and `Array.push`
rather than the list-backed `#[...]` macro.

### E5. Pre-cloud completeness review

- Mechanically check that every changing return in the pinned fork is paired
  with an event or structural witness.
- Diff the fork against the pinned upstream sources, allowing only namespace,
  recursion, observer, and replay-driver changes.
- Run the focused equivalence, mutation, coverage, and complete-module source
  suites.

Gate: the implementation-to-IR matrix has no `partial`, `implicit`, or `absent`
entry; all review checks are machine-enforced.

Status: complete. A declaration-level lineage manifest binds 120 semantic fork
declarations to the pinned `Main`, `Rewrite`, `Types`, `Simproc`, and
`Transform` implementations. A separate digest covers 105 controlled
declarations, and hashes lock the manually reviewed fork, IR, runtime,
fingerprinting, record/replay, source, inventory, reference adapter, and
coverage contract. The
review fixed every discrepancy it found before rerunning the complete local
gate; section 4 has 54 machine-bound rows and no partial, implicit, or absent
schema-18 representation.

### E6. Full cloud closure

- Run the syntax inventory once at the committed SHA.
- Shard modules deterministically by stable module hash.
- Record and materialize each module once per shard, with existing
  declaration-group bisection only for compilation failures.
- Upload per-module JSON/logs and merge them in a final reducer job.

Gate: every inventory occurrence has one terminal outcome; every committed
successful non-simproc/non-custom-discharger execution materializes; there are
no coverage, recorder, harness, declaration, aggregate, or unclassified
failures.

Status: validated inventory and parallel Vast.ai infrastructure complete;
corpus result pending. GitHub-hosted execution was rejected after repeated
external runner evictions made useful parallelism and durable results mutually
exclusive; the superseded workflow has been removed rather than retained as a
test path.

The inventory fixes 8,264 module files, 6,319 modules containing 83,425
occurrences, source hashes, and exact byte ranges at the tested commit. It
includes 91 nested occurrences, uses the exact frontend for five modules whose
lightweight parse requires recovery, and collapses one byte-identical duplicate
syntax record. Modules are assigned by `SHA256(module) mod shardCount`.

The run uses 256 deterministic batches distributed across 16 distinct verified
Vast.ai machines. Four shard processes run on each host, so 64 module
executions can proceed concurrently. Every host provides at least 16 effective
CPU cores and 96 GB RAM, or four effective cores and 24 GB RAM per active Lean
process. Those bounds follow a root-cause correction, not an accommodation of
the earlier capacity failures: the recorder had duplicated outer simproc traces
inside recursive premises, expanded shared expression DAGs into trees while
fingerprinting, and allowed observation to change meta-state. Once those bugs
were fixed, the module that previously exceeded a 250 GB worker completed the
normal shard harness at 1.61 GB RSS.

Exit `-9` or `137` is still classified as worker-capacity failure and never
triggers semantic materialization bisection. Each batch records a module once
and, when it has accepted executions, compiles one copied module with all
accepted occurrences materialized. A batch stops after its first semantic
failure. Diagnostic group bisection runs only after a materialization failure
and never changes the gate. The reducer requires every batch, module,
occurrence, and replay count before it can pass.

## 11. Cloud execution design

`Experiment/simp_engine_vast.py` is the local controller. It:

- requires a clean exact commit that is the tip of a remote ref;
- builds the immutable syntax inventory once locally;
- queries the live Vast.ai marketplace and selects distinct verified machines
  under reliability, effective-vCPU, RAM, disk, network, per-offer, aggregate
  hourly, and maximum-runtime guards;
- launches 16 Ubuntu 24.04 hosts and explicitly attaches the configured SSH
  key to every contract;
- retains only candidates that pass the real SSH handshake, destroys rejects,
  and fills their slots from distinct fallback offers without exceeding the
  aggregate hourly guard; every concurrent process requires four effective
  cores and 24 GB RAM, and the controller refreshes an exhausted fallback
  snapshot from the live market a bounded number of times;
- installs the pinned Lean toolchain on all hosts concurrently, checks out the
  exact commit, raises and verifies a 65,536 file-descriptor limit, restores
  Mathlib artifacts, and builds the engine and shared library before starting
  work; cache extraction failure rejects the host instead of silently compiling
  a partial dependency graph;
- compiles every copied module with Mathlib's semantic package options,
  including `autoImplicit=false` and `maxSynthPendingDepth=3`, while disabling
  only non-semantic linter noise;
- compresses the immutable inventory for transfer, retries bounded transfers,
  and replaces a setup-failed host in the same worker slot while other workers
  continue;
- partitions all 256 batches exactly once across the hosts and runs four shard
  processes per host;
- copies atomic worker state, reports, logs, and failing sources back to the
  controller every 30 seconds, excluding transient per-module `work/` trees and
  including checkpoints while slower hosts are still setting up;
- stops the fleet after the first semantic failure set or the three-hour cost
  bound;
- runs the existing strict reducer only after collection; and
- destroys all rented instances on every terminal path unless explicitly kept
  for diagnosis.

At the launch defaults, 64 module executions can be active concurrently on 16
independent machines. Every offer must provide 16 effective CPU cores and 96 GB
RAM for its four active Lean processes. The controller refuses a plan above
$4.00/hour or three hours; the actual plan and its compute exposure are
recomputed before rental.

The terminal taxonomy is deliberately closed:

- `materialized`: at least one successful execution, with exactly the same
  number of source replays;
- `deferred_simproc`, `deferred_custom_discharger`, or their combination: at
  least one successful execution at that source occurrence crosses a
  separately designed boundary, so the occurrence as a whole remains
  unmaterialized;
- `unsuccessful_execution`: the occurrence ran, upstream `simp` failed, and no
  successful execution was recorded; and
- `not_executed`: neither the success nor upstream-failure observer ran.

`capacity_failure`, `recording_failure`, `materialization_failure`,
`harness_failure`, and `unclassified` are reportable
diagnostics but failing gate outcomes. A capacity failure means the batch must
be rerun on a larger worker; it says nothing about certificate semantics.

The fleet is launched only from a clean committed implementation after E5.
Atomic remote reports become durable locally at every collection interval.
Cloud parallelism is the final closure run, not a substitute for the finite
completeness review.

## 12. Decisions

- Schema 15 remains only in Git history and is not a simplifier IR dependency.
- Schema 18 is the current certificate format; in addition to schema 17's
  bounded DAG fingerprinting and lossless simproc dictionary encoding, it
  records the exact extra-argument count selected by theorem indexing.
- E1 through E5 and the E6 cloud infrastructure are complete; the full E6
  corpus result is pending.
- The correctness boundary is a pinned source fork with record and replay
  modes.
- Structural traversal and dsimp are first-class certificate semantics.
- Congruence selection is explicit; replay never reads the ambient congruence
  extension.
- Rule variants and match assignments are validated, not inferred from a final
  proof.
- Simprocs are detected exactly and deferred pending their separate design.
- The full corpus runs in cloud shards only after the finite branch matrix is
  completely covered and mutation-tested.
