# Legacy schema-27 `simp` engine contract

> **Status: superseded product design; frozen legacy implementation contract.**
> This document specifies the operational recorder/replayer currently present
> in the repository. It is retained for regression review and engineering
> evidence. It is not the correctness contract or roadmap for the active
> boundary-state translator. [PLAN.md](PLAN.md) is authoritative, and
> [README.md](README.md) explains the distinction for new implementers.

Pinned engine: Lean 4.32.2, commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`

Scope: successful `simp` and `simp only` executions. `simpa`, `simp_all`,
`simp_rw`, and `rw` are outside this contract.

## 1. Correctness contract

For an initial proof state `S`, an elaborated simp context `C`, and a generated
certificate `P`, acceptance requires:

1. **Pinned equivalence.** The reference fork and upstream simplifier produce
   the same result and operational state.
2. **Trace totality.** Every committed changing leaf operation and every
   structural choice needed to reach it has exactly one representation. A
   failed candidate is retained when it performed replay-relevant work.
3. **Closed replay.** Replay consults the program, recorded rule terms, checked
   local/input dependencies, and fixed kernel/meta primitives. It does not
   consult ambient simp/congruence sets, simproc registries, or dischargers.
4. **Exact consumption.** Events, structural witnesses, nested programs, and
   subject programs are consumed once and in order at their recorded paths.
5. **Exact result.** Replay reaches the recorded final fingerprints and
   reproduces proof-presence and cache behavior wherever those affect control
   flow or goal/local transport.
6. **Source validity.** Serialized source decodes to the same certificate at
   the replacement site, and the complete materialized module compiles.
7. **Explicit deferral.** An operation outside this model is not covered by its
   result proof. It defers the containing subject.

Before a recording is returned, it is compared with a separate upstream-mode
run from the same saved meta-state. The differential summary includes a
structural result fingerprint, proof presence/proposition, result cache flag,
and complete operational `Simp.State` contents: step count,
simp/congruence/dsimp caches, used theorem origins, and diagnostics. Proof fields
inside state are compared modulo proof irrelevance; independent custom
discharger executions may allocate different extension-local private proof
names. Fresh fvar, mvar, and universe-mvar identities are canonicalized.

## 2. Pinned execution model

The authoritative upstream surface is:

- `Lean/Elab/Tactic/Simp.lean` for context and location handling;
- `Lean/Meta/Tactic/Simp/Main.lean` for recursion and traversal;
- `Lean/Meta/Tactic/Simp/Rewrite.lean` for rules, builtins, and discharge;
- `Lean/Meta/Tactic/Simp/Types.lean` and `Simproc.lean` for state and methods;
- the congruence, transform, and have-telescope helpers reached from that code;
  and
- the separately hash-pinned Lean/Mathlib implementations interpreted by
  semantic simproc descriptors.

At each expression node, `simpLoop` consults the cache and step bound, executes
`pre`, performs a reduction, traverses structure, executes `post`, and possibly
restarts. `done`, `visit`, `continue none`, and `continue some` are distinct
control-flow outcomes even when the expression is unchanged. `dsimp` is a
separate `transformWithCache` traversal with `dpre`, `dpost`, telescope locals,
instance skipping, and repeated definitional reduction.

Each simp/dsimp call and phase invocation has an ordinal-qualified execution
path. Cache hits identify the producer path and producer ordinal; semantic path
alone is insufficient because isolated attempts can repeat it. Nested premise,
conditional, and ground programs reset the appropriate cursors and preserve or
isolate simp state exactly as their recorded policy specifies.

Recording state is transactional. Restoring a failed candidate removes its
program events, structural witnesses, and committed simproc observations.
Runtime diagnostics are append-only and deliberately conservative: they record
what physically ran and may retain a deferral even when the logical candidate
was rolled back.

## 3. Certificate authority

A certificate contains:

- an `EngineId` (`leanVersion`, `leanCommit`, `certificateSchema`);
- the replay configuration and initial/final proof-state fingerprints;
- ordered subject programs for the target and selected hypotheses;
- structural witnesses for traversal, caching, congruence, premises, and
  subject transport;
- executable events for exact rewrites, reductions, builtins, and semantic
  simproc folds; and
- a rollback-aware committed simproc trace used to validate fold coverage.

Rule references pin their origin, selected theorem variant, match envelope,
assignments, lhs/rule fingerprints, priority, direction, and nested premises.
Raw expressions and unstable local identifiers are never serialized as general
authority. Dependencies are restricted to checked input paths, checked local
references, literals, and applications of named declarations with explicit
universe descriptors.

Expression fingerprints erase proof subterms where proof presence is carried
separately. Replay still reconstructs and typechecks every required proof; a
fingerprint is a validation boundary, not permission to synthesize an unknown
operation.

## 4. Implementation-to-IR coverage matrix

This matrix is normative only for the frozen schema-27 legacy implementation.
It does not specify the boundary-state translator.
`Experiment/check_simp_engine_observers.py` binds every row to legacy
implementation text, while the reviewed-source lock detects edits that require
a fresh legacy semantic review.

| Upstream site | Committed behavior | Schema-27 representation |
| --- | --- | --- |
| `simpImpl` call boundary | Recursive calls and proof skipping | `simpCall` identity and `proofSkip` terminal |
| `dsimpImpl` call boundary | Recursive definitional calls | `dsimpCall` identity |
| `simpLoop` cache | Reuses a prior result | producer-qualified `cacheHit` |
| `pre` step | Four step dispositions | exact `phaseOutcome` and visit path |
| `post` step | Stops or restarts a node | exact `phaseOutcome` and `postRestart` |
| `simpStep`: unassigned mvar | Stops when instantiation cannot progress | `unassignedMVarStop` |
| metadata traversal | Recurses through metadata | `metadataBody` path |
| `reduceStep`: mvar head | Instantiates assignments | `instantiateMVars` reduction |
| `reduceStep`: beta | Head beta reduction | `beta` reduction |
| `reduceStep`: native projection | Reduces `.proj` | structure and field projection |
| `reduceStep`: projection function | Chooses requested/class/structure route | projection declaration and branch |
| `reduceStep`: iota | Reduces recursor or matcher | `iota` reduction |
| `reduceStep`: zeta | Expands a used let/have | `zetaUsed` with mode |
| `reduceStep`: unused let | Drops a nondependent unused let | `zetaUnused` |
| `unfold?`: requested | Smart, partial, or ordinary unfolding | declaration and exact strategy |
| `unfold?`: auto | Smart or matcher unfolding | `autoSmart` or `autoMatch` |
| `foldRawNatLit` | Repackages raw Nat literal | fixed builtin reduction |
| `reduceFVar` | Expands a local definition | checked local reference and reason |
| `simpProj` | Simplifies/dsimps projection major | branch and child mode |
| `simpApp` | Selects user/generated/generic congruence | exact `CongruenceChoice` |
| failed congruence candidates | May leave executable work | ordered failed-attempt choice when progressed |
| user congruence | Applies named theorem and premises | theorem/match identity and nested hypotheses |
| generated congruence | Computes argument modes and synthesis | theorem shape, modes, and assignments |
| generic congruence | Chooses simp/dsimp/fixed per argument | explicit argument modes |
| `simpMatch` direct reduction | Iota before ordinary reduction | pre-phase `iota` |
| `simpMatchDiscrs?` | Simplifies selected discriminants | structural choice and child paths |
| failed match-discriminant candidate | Changed state but no matcher result | failed structural terminal |
| `simpMatchCore` | Applies matcher equation theorem | exact theorem rule |
| lambda traversal | Dsimps domains and simps body | telescope and scoped-local paths |
| implication traversal | Optionally adds contextual rule | exact contextual/plain branch |
| forall traversal | Selects transport/dsimp branch | exact forall branch and children |
| dependent let | Converts to have or dsimps | branch and child program |
| have telescope | Drops/fixes/simplifies entries | bitsets, drops, and child programs |
| `dpre`/`dpost` | Rfl rules and dsimprocs | definitional phases and outcomes |
| `dsimpReduce` | Repeats definitional reductions | shared exact reduction vocabulary |
| dsimp transform | Uses separate cache/telescope rules | transform and cache witnesses |
| theorem preprocessing | Produces variants/equations lazily | exact variant and origin fingerprints |
| indexed rewrite | Uses indexed/liberal lookup and extra args | index mode and argument count |
| theorem match | Assigns binders and orientation | `MatchEnvelope` |
| failed theorem candidate | Premises may execute before failure | failed rewrite with nested premises |
| instance arguments | Synthesizes assigned typeclass binders | ordered assignment fingerprints |
| implicit defeq proof | Changes proof presence | explicit proof-presence fact |
| recursive premise simp | Runs complete simplifier recursively | nested full program and terminal |
| default discharge terminals | Assumption/equation/rfl/True/failure | exact terminal |
| custom discharger | Arbitrary user code | explicit deferral |
| `simpUsingDecide` | Fixed decision procedure | `decideTrue` or `decideFalse` builtin |
| `simpArith` | Selects Nat/Int arithmetic handler | exact arithmetic builtin variant |
| `simpGround`/`seval` | Runs isolated nested simplifier | nested `ground` program |
| pre/post simprocs | Executes ordered candidates | committed observation and semantic fold or deferral |
| dsimprocs | Executes definitional candidates | execution-aware observation and fold or deferral |
| target result | Closes or transports target | exact target terminal |
| local result | Closes/replaces/asserts a hypothesis | exact local terminal |
| `simpGoal` batching | Processes authored locations in order | ordered subject programs |
| `failIfUnchanged` | Fails after all subjects | recorded configuration and final check |

## 5. Semantic simproc model

`SimprocObservation` records the actual call protocol: execution path and phase
ordinal, declaration, registry set index, input/output fingerprints, change,
disposition, simp-versus-dsimp kind, extra arguments, execution flag,
proof/cache facts, and optional result size. `executed` means the candidate's
procedure path actually ran; a registry entry of the wrong procedure kind may
be observed as unexecuted. Result size counts both expanded tree nodes and
structurally distinct DAG nodes and saturates the tree counter at a fixed large
bound.

Only rollback-surviving observations are serialized into a subject's
`SimprocTrace`. JSON dictionary-compresses equal observations while preserving
one order index per invocation. No-result calls have no result size and are not
included in result-bearing histograms. Result size and `fieldEqAudit` are
diagnostics: replay validates the semantic/protocol fields of the observation
but does not treat either diagnostic payload as authority.

`SimprocFold` is an ordered nonempty sequence of result-bearing candidates.
Each candidate records its actual declaration protocol and one closed semantic
descriptor. `continue some` feeds the next candidate; `done` and `visit`
terminate. Replay requires:

- the declaration's pinned kind/registry/disposition protocol;
- exact input, peeled-input, extra-argument, procedure-output, and final-output
  fingerprints;
- exact proof/cache facts and final fold disposition;
- a matching committed observation with the same multiplicity and global
  order; and
- successful reconstruction by the semantic interpreter.

Supported descriptors are canonical Nat/Int/Fin values and guards,
constructor disjointness, conditional selection with nested condition programs,
checked vector lookup, canonical `Fin.mk`, and existential-equality elimination.
The declaration is provenance only: replay does not invoke it.

The only accepted executed no-result calls are source-reviewed pure paths:
three Lean WF preprocessing dsimprocs and `ExistsAndEq.existsAndEq`. Unexecuted
wrong-kind entries are also inert. Every other unmodelled executed call causes
deferral. A supported declaration encountered through a different registry,
procedure kind, or disposition remains observable but is not authorized.

The `fieldEqAudit` payload is passive. It records the discharger tree and exact
authoritative/shadow parity, but `validateSimprocObservations` and replay never
consult it as authority.

## 6. State, nesting, and effects

Nested premise and conditional programs carry explicit state/config policies.
`reduceIte` and `reduceDIte` share outer simp state while replaying a scoped
condition program; `reduceDIte` additionally checks the selected proof argument
and head-beta witness. Ground evaluation uses its pinned environment and an
isolated simp cache.

Semantic derivation runs from saved meta-state and restores it. Dependency
reconstruction performs no elaboration or ambient instance search. Instance
witnesses are restricted dependency terms with checked types. Operations that
would take credit for a procedure-created metavariable assignment are rejected;
three measured `ExistsAndEq` results hit that boundary. A fourth result invokes
the declaration from the post registry and remains deferred because schema 27
pins the supported protocol to the pre registry.

The passive `fieldEq` audit is isolated in `ExplicitLeanMathlibAudit` so the
generic shared library has no Mathlib compiled-symbol dependency. Its shadow
runs from the authoritative pre-state and the hook restores the authoritative
post-state before returning.

## 7. Source and production harness

Certificate source is compact schema-27 JSON embedded in a shallow Lean string
array. `Name` values use lossless string/numeric components. The source wrapper
selects certificates by initial proof-state fingerprint and replay config,
rejects unequal duplicates, validates engine identity before replay, and
preserves tactic-head antiquotations and indentation-sensitive trailing syntax.

The syntax inventory records every supported source occurrence with stable byte
ranges and composes nested head rewrites. The production reducer requires a
terminal outcome for every occurrence and rejects missing shards/modules,
source or engine drift, recorder failures, inconsistent deferred reasons,
replay-count mismatches, materialization failures, and capacity exits.

The last full closure predates schema 27 and is retained only as a baseline:
83,425 occurrences across 6,319 modules were totally classified with zero
harness failures. The rollback-aware record-only simproc census is current
evidence for call frequency, not a substitute for a fresh schema-27 closure.

## 8. Legacy review and change policy

The schema-27 review lock hashes every legacy semantic source file, this legacy
contract, the fork-to-upstream declaration lineage, controlled fork
declarations, and the upstream Lean/Mathlib implementations on which its
negative-path or semantic reasoning depends. Active planning, simproc guidance,
and report-storage documents are deliberately outside that legacy hash lock. A
Lean or Mathlib upgrade of the retained implementation must:

1. regenerate the lineage and implementation hashes;
2. re-audit every coverage-matrix row and semantic protocol;
3. change the engine/schema identity when serialized meaning changes;
4. rerun focused differential, replay, mutation, and source gates; and
5. run a fresh full-corpus closure before making corpus-wide completeness
   claims.
