# Simprocs under boundary-state replacement

[HANDOFF.md](HANDOFF.md) is the current entry point; [PLAN.md](PLAN.md) supplies
the boundary design background. This document records simproc-specific evidence
and risks, including historical prototype observations rather than current
coverage counts.
The detailed schema-27 semantic models are historical and are described in
[SIMP_ENGINE_COVERAGE.md](SIMP_ENGINE_COVERAGE.md).

## Design rule

A simproc is opaque code that stock `simp` may run while the translator records
an original source call. The current generated `simp_engine_boundary_select`
prototype (whose production public name is intended to be `simp_engine_apply`)
does not invoke the simproc or reconstruct its algorithm. It applies the checked
result expression and proof returned by stock Lean, plus any
continuation-visible state delta identified by the boundary comparator.

A simproc name or trace may be retained as diagnostic provenance. It is not
apply authority. Candidate order, registry placement, dispositions, rollback,
cache facts, discharger strategy, and internal result histograms do not belong
in the generated artifact unless measurement proves that one changes the
post-call boundary.

## Measured risks

### Pre-existing metavariable assignments

The schema-27 experiment found three committed
`ExistsAndEq.existsAndEq` calls that assigned metavariables which existed before
the simproc ran. These are direct boundary tests. The replacement must either
encode the same assignment delta or elaborate generated proof source that
establishes an equivalent delta. Registry provenance from the old experiment is
irrelevant to apply.

The boundary prototype must also test universe metavariables and postponed
constraints; the legacy census did not establish their absence at the new
boundary.

### Custom dischargers

A custom discharger may return a proof and may also mutate Meta/Core state. The
returned proof is ordinary boundary evidence. Any assignment or other persistent
effect that later tactics can observe must be captured generically or classified
as `external_effect_failure`. The prototype must measure this rather than assume
custom dischargers are pure.

### Large and shared outputs

`reduceDIte`, `fieldEq`, and `Matrix.cons_val` produced large expression trees
with much smaller shared DAGs. They are printer, sharing, memory, and source-size
tests. Their size is not a reason to implement semantic replay. Generated source
must preserve sharing well enough to compile within the production resource
budget.

### Definitional results and unchanged results

Some calls return a definitionally equal expression without an explicit
equality proof. Apply should use a checked definitional change. Other simprocs,
notably many `Fin.isValue` executions, can terminate simplifier search while
leaving the subject unchanged. No simproc operation is needed when the final
boundary is unchanged; the artifact records the whole-call outcome, not the
internal reason.

### Tactic failure

Candidate failure and rollback inside `simp` are internal. Only failure of the
entire source tactic is externally relevant. A recorded failure variant must
leave the pre-call boundary unchanged and fail so that the original surrounding
tactic control flow selects the same alternative.

## Corpus evidence

The frozen record-only census uses Mathlib commit
`905b95818eb32af7874a58b427f50c1711a5e96c` and Lean 4.32.2 commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`. Its local reduced report is:

```text
.lake/simproc-hist-committed-record-only/final/simp-engine-closure.json
```

SHA-256:
`48a23b2661e5c8f72daadb8a4051521547e30f02bcca2f10a376abe6f8ff04ac`.
The durable copy is under the initial snapshot documented in
[REPORTS.md](REPORTS.md).

The census measured 12,731 committed result-bearing calls across 55 simproc
declarations. The ten most frequent declarations account for 12,049 calls
(94.6%): `Fin.isValue`, `reduceIte`, `Nat.reduceAdd`, `reduceDIte`,
`Int.reduceNeg`, `reduceCtorEq`, `fieldEq`, `Matrix.cons_val`,
`Fin.reduceFinMk`, and `ExistsAndEq.existsAndEq`.

This evidence selects stress tests. It is not a completeness claim for
continuation-visible effects, and a new boundary run must produce its own effect
inventory.

## Focused boundary cases

The active boundary gate currently covers equality-producing, proof-free
definitional, unchanged, target-closing, local-`False`, authored-hypothesis,
dependent-context, and source-materialization behavior. An earlier broad
`Mathlib/Data/Fintype/List.lean` round trip covers a committed `ExistsAndEq`
result without a declaration-specific apply model. Its six calls are in
computational declarations; the schema-2 representative gate now replaces all
six, compiles the result, and applies the declaration/environment oracle. The
same gate covers all 17 `AddConstMap`, 33 `EqToHom`, 7 `NonUnitalHom`, and 3
`PosPart` occurrences; all five modules pass with zero remaining executable
calls. The scope-aware
`Mathlib/Analysis/CStarAlgebra/SpecialFunctions/PosPart.lean` round trip covers
all three calls, including a large `Matrix.cons_val` result and one
occurrence with four selected boundary variants. A focused custom discharger
does assign pre-existing expression and universe metavariables; both the
in-memory comparator and serialized source round trip show that elaborating the
checked proof reproduces those assignments without a separate delta. Focused
pending-synthetic and postponed-constraint cases are preserved when stock
`simp` leaves them unchanged.

Scope classification is a separate source-to-source concern: the boundary probe
records only which selected occurrence IDs executed and whether their final
caller declarations are propositions. Under the revised contract this selects
the final declaration comparison rule; it does not determine eligibility. The
probe intentionally does not record simproc order, registry state, or other
simplifier internals. The pinned
diagnostic closes the old 101 scope unknowns, and the regenerated full diagnostic
manifest classifies all 83,425 occurrences with zero unknowns. The schema-2
`AddConstMap/Basic` canary uses manifest schema 2 and has materialized all 17
calls, compiled, and passed the
schema-1 declaration/environment oracle, including computational values,
compiler IR, persistent extensions, and axiom subsets. The current shard report
format is schema 5, adding explicit nested-call coverage. The full five-module
representative gate now supplies the same semantic check for every listed
module. The full diagnostic predates the hardened implementation fingerprint
and must be regenerated with execution-role classification. These results do
not change the simproc stress-test scope or claim full-corpus materialization.

The boundary prototype should include:

1. proof-producing and definitional-only results;
2. a changed result and an unchanged terminating result;
3. a large shared result from `reduceDIte`, `fieldEq`, or `Matrix.cons_val`
   (currently covered by `Matrix.cons_val`);
4. the three measured `ExistsAndEq` pre-existing metavariable assignments;
5. expression and universe metavariables plus postponed constraints;
6. at least one custom discharger with a proof-only result;
7. an instrumented custom discharger with a persistent assignment;
8. an entire `simp` failure inside an unchanged tactic alternative; and
9. a continuation, unchanged except for any required binder alpha-renaming,
   that consumes each recorded effect;
10. transparent and opaque/irreducible computational declarations whose final
    values are definitionally equal;
11. non-`Prop` structures containing proof and computational fields; and
12. declaration-signature/default and generated-command environment effects.

The oracle is a paired stock/apply state comparison using actual definitional
equality, successful elaboration of the continuation, and final declaration
value/environment comparison. Fingerprints are selectors and diagnostics only.
Matching a simproc trace is never an acceptance condition.

## Extension rule

Add declaration-specific code only if measurement demonstrates a persistent
continuation-visible effect that the generic boundary artifact cannot express.
First attempt to extend the generic state delta. If that is impossible, document
the measured case, representation, selector impact, and focused tests before
adding a special model. Otherwise, capture the checked result and let Lean's
kernel validate the generated proof.
