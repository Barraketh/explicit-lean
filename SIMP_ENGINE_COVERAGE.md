# Pinned `simp` engine coverage and certificate architecture

Status: implementation specification; E1 through E4 complete

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

Structural traversal recursively calls either `simp` or `dsimp`. `dsimp` is a
different state machine based on `transformWithCache`: it has `dpre` and
`dpost`, skips selected instance arguments, introduces locals for telescopes,
and runs repeated definitional reduction after `dpost`.

This means that a flat list of successful `pre`/`post` callbacks is not an
execution model. It is only one projection of the execution.

## 4. Implementation-to-IR coverage matrix

The `Required representation` column is normative for certificate schema 16.

| Upstream site | Committed behavior | Required representation | Schema 15 |
| --- | --- | --- | --- |
| `simpImpl` call boundary | Recursive calls may share the same semantic child path, and proofs stop before `simpLoop` | `simpCall` identity and an explicit `proofSkip` terminal | absent |
| `dsimpImpl` call boundary | Recursive definitional calls may share the same semantic child path | `dsimpCall` identity | absent |
| `simpLoop` cache | Reuses a prior result and can suppress a second traversal | call-qualified structural `cacheHit` with the producing path | implicit |
| `pre` step | `done`, `visit`, `continue none`, and `continue some` have different control flow even without a changing operation | exact `phaseOutcome` for every invocation | partial |
| `post` step | May finish or restart the entire node | exact `phaseOutcome` plus the call-qualified restart edge | partial |
| `simpStep`: unassigned mvar | Stops structurally when instantiation makes no progress | explicit `unassignedMVarStop` terminal | absent |
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
| user congruence | Selects a named `[congr]` theorem and simplifies designated hypotheses | theorem identity, priority/variant, and hypothesis subprograms | absent |
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
| theorem preprocessing | One source rule may produce several actual simp theorems | exact preprocessed variant index and lhs/rule fingerprint | all variants retried under one origin |
| indexed rewrite | Discrimination lookup, priority, erased set, extra args | selected rule plus `index` mode and variant | mostly present |
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
  | forallDomain
  | forallBody
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

structure RuleRef where
  source : String
  origin : RuleOrigin
  inverse : Bool
  phase : Phase
  variant : Nat
  ruleFingerprint : String
  lhsFingerprint : String
  indexMode : Bool

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

inductive Structural where
  | phaseOutcome (phase : Phase) (invocationOrdinal : Nat)
      (disposition : StepDisposition) (outputFingerprint : String)
      (proofPresent : Bool)
  | proofSkip (invocationOrdinal : Nat) (typeFingerprint : String)
  | unassignedMVarStop (simpStepOrdinal : Nat)
  | cacheHit (sourcePath : ExecutionPath)
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
  | dsimpCacheHit (sourcePath : ExecutionPath)
  | dsimpTransform (usedLetOnly skipInstances : Bool)

mutual
  structure PremiseProgram where
    propositionFingerprint : String
    program : Program
    terminal : PremiseTerminal

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

### 5.1 What is and is not source

The schema-16 source payload is compact JSON embedded in a shallow Lean array
of string literals:

```lean
simp_engine_apply "occurrence-id"
  (certificates := #["{...schema-16 certificate...}", ...]) originalSimpArgs
```

The JSON contains the complete path-qualified operations and structural
witnesses. It never contains intermediate expressions; input and output hashes
are validation fields. Every emitted payload is parsed immediately and compared
structurally with the in-memory certificate before it is accepted. At the
replacement site it is parsed again, its engine identity is checked, and closed
replay validates its initial and final states.

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
- simproc candidate loops report the exact selected simproc before returning a
  deferred boundary; and
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
its `Origin`. Replay reconstructs exactly that variant and checks its rule and
lhs fingerprints before matching. Candidate ordering is relevant only while
recording; an explicit replay operation does not consult an ambient theorem
tree.

The match envelope validates ordered binder and instance assignments. Replay
may use Lean's unifier and typeclass synthesis to construct those assignments,
but it must agree with the recorded fingerprints before the operation commits.

### 8.2 Congruence

Ambient `getSimpCongrTheorems` is prohibited during replay. Record mode emits
one of:

- the exact user congruence theorem and hypothesis positions;
- the generated congruence theorem shape and argument kinds; or
- generic congruence with each argument's `simp`, `dsimp`, or fixed mode.

Replay executes that choice directly. A user congruence theorem is resolved and
fingerprinted like an ordinary rule. Generated congruence may use the pinned
generator, but its generated type, proof head, and argument kinds must match
the witness before its child programs run.

Failed user/generated candidates are recorded when they performed recursive or
cache-relevant work. Their failure is replayed before the next candidate. A
candidate with no executable progress is omitted; call frames, phase outcomes,
and certificate-driven cache hits ensure that omitted meta allocation identity
cannot become replay semantics.

### 8.3 Premises

A recursive premise is a complete nested `Program`, including dsimp and
structural witnesses. Default terminal selection remains explicit:
`localAssumption`, `equationHypothesis`, `dischargeRfl`, `isTrue`, or `failed`.

Failed theorem candidates that contain recursive premise work are explicit
`rewriteAttemptFailed` operations with nested premise programs and a `failed`
terminal. A candidate that produced no executable program item is omitted. A
custom source discharger remains `deferred_custom_discharger`.

## 9. Simproc boundary

This design does not decide how a simproc transition will eventually replay.
It does require exact detection, including:

- pre and post simprocs;
- dpre and dpost dsimprocs;
- simprocs invoked by ground/seval; and
- simprocs inside recursive premise programs.

The instrumented candidate loop records the selected declaration name, phase,
input/output fingerprints, step disposition, and nesting path, then classifies
the enclosing execution `deferred_simproc`. No result proof is materialized.
This makes the non-simproc completeness gate honest without prematurely
choosing simproc semantics.

## 10. Implementation obligations and gates

Each stage is committed before the next begins.

### E1. Reference engine

- Add the pinned fork in reference mode.
- Compare upstream and fork results for every existing focused fixture and a
  bounded production module set.
- Compare expression, proof presence, cache flag, used theorems, diagnostics,
  subject closure, and final state.

Gate: zero equivalence mismatches; no certificate or corpus behavior changes.

Status: complete. The fork is pinned by hashes of the complete authoritative
source surface, the focused reference probe covers both `simp` and `dsimp`
branches, and 57 supported calls across two syntax-instrumented Mathlib modules
agree exactly.

### E2. Total structured recorder

- Add schema-16 paths, structural witnesses, all four phases, total reduction
  identities, exact congruence choices, rule variants, match envelopes, and
  full nested premise programs.
- Add exact simproc/dsimproc observation and deferred classification.
- Remove continuity-bridge synthesis from accepted recording.

Gate: branch-focused tests cover every row of section 4. Deleting any observer
call causes its focused test to fail with `unobserved_transition`.

Status: complete. The recorder covers every matrix row, retains stateful failed
candidate attempts, emits nested premise programs, observes all
simproc/dsimproc phases without accepting them, and matches reference-mode
results on the focused probe and 57 bounded production calls.

### E3. Closed structural replay

- Add replay mode to the same engine.
- Empty all ambient simp, congruence, simproc, and discharger dependencies.
- Command-gate every changing branch and validate exact path and hashes.
- Preserve exact proof-presence mode and subject transport.

Gate: every branch-focused certificate replays; mutations of path, phase,
operation, rule variant, congruence choice, config, premise order, or terminal
fail at the mutated item.

Status: complete. The focused suite replays 36 dynamic branch classes and
rejects 15 targeted mutations. The batched bounded gate records each module
once, classifies every execution by occurrence ID, then replays 55 wholly
non-deferred occurrences across 58 executions in one replay compile per module;
two occurrences are explicitly simproc-deferred and none are unclassified.

### E4. Source and materializer migration

- Print and parse the schema-16 source form.
- Include engine id, rule fingerprints, and final-state validation.
- Switch passive recording and context programs to the new engine.
- Keep the source and materializer independent of removed historical bridge
  and selector-discovery implementations.

Gate: all existing non-simproc focused/production fixtures materialize through
schema 16 with zero bridge, generated-proof, presentation, or whole-result
metrics. `Experiment/run.sh` passes.

Status: complete. Each module is instrumented once for all occurrences, every
serialized execution is structurally round-tripped, and complete materialized
copies are compiled. The focused and two bounded production modules contain 62
occurrences: 60 materialize across 64 dynamic executions, while two remain
explicitly simproc-deferred. The focused gate covers private qualified rule
names, recursive premises, multiple executions of one occurrence, authored
locations, and configuration-driven builtins. A source-only engine-schema
mutation is rejected before replay.

### E5. Pre-cloud completeness review

- Mechanically check that every changing return in the pinned fork is paired
  with an event or structural witness.
- Diff the fork against the pinned upstream sources, allowing only namespace,
  recursion, observer, and replay-driver changes.
- Run the bounded equivalence, mutation, coverage, and aggregate suites.

Gate: the implementation-to-IR matrix has no `partial`, `implicit`, or `absent`
entry; all review checks are machine-enforced.

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

## 11. Cloud execution design

The repository currently has no GitHub Actions workflow. Before E6, add a
manual `workflow_dispatch` workflow with inputs for commit SHA, shard count,
timeout, and optional module prefix. It must:

- refuse a dirty or moving ref and check out the exact SHA;
- restore Lean/Mathlib build caches keyed by toolchain, lake manifest, and SHA;
- run a matrix of independent shards;
- use a shared inventory artifact and disjoint shard output directories;
- upload reports even when a shard fails;
- run one reducer that verifies inventory coverage and schema/engine identity;
  and
- retain the merged JSON, Markdown summary, compiler logs, and failing source
  copies.

The workflow is dispatched only from a clean committed implementation after E5.
Local parallelism remains the fast focused gate; cloud parallelism is the final
closure run, not a substitute for the completeness review.

## 12. Decisions

- Schema 15 remains only in Git history and is not a simplifier IR dependency.
- E1 through E4 are complete; the next implementation step is the pre-cloud
  completeness review (E5).
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
