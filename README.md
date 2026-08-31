# Explicit Lean

Explicit Lean is a source-to-source translator for every executed source `simp`
and `simp only` occurrence in the pinned Mathlib corpus, including calls that
contribute to computational data. The production replacement will use the
public name `simp_engine_apply`; the current boundary prototype emits
`simp_engine_boundary_select` with an `apply_encoded` branch after selecting a
recorded variant. It prefers to leave surrounding tactics and binder spellings
intact, but may consistently alpha-rename declaration
parameters when needed; semantic declaration and elaboration-state equivalence
are the hard gates.

The active correctness rule is:

> Reproduce the semantically observable output of each `simp` call, without
> reproducing the internal simplifier execution.

The original `simp` may run while the translator records its result. The
generated replacement must apply checked result expressions, proofs, and
continuation-visible state changes without running `simp`, a simproc, or a
discharger.

## Start here

Read these documents in order:

1. [PLAN.md](PLAN.md) is the authoritative goal, correctness contract, current
   status, prototype specification, and roadmap.
2. [simprocs.md](simprocs.md) explains the few simproc-related boundary risks
   that the prototype must test.
3. [REPORTS.md](REPORTS.md) describes durable validation-report storage.
4. [SIMP_ENGINE_COVERAGE.md](SIMP_ENGINE_COVERAGE.md) is the frozen contract for
   the existing schema-27 operational-replay implementation. It is historical
   engineering evidence, not the active product specification.

If these documents conflict, `PLAN.md` controls the boundary-state project.

## Current state

This branch is the project restart and its own engineering lineage. Do not use
`main` as a baseline for scope, completeness, or project decisions.

The repository retains schema-27 operational recording and replay as legacy
evidence. In particular, the existing
`simp_engine_apply` parser in `ExplicitLean/SimpEngine/Source.lean` still accepts
schema-27 certificates and invokes the replay engine. The shared name must not
be mistaken for completion of the new tactic.

A separate boundary-state prototype now covers target and hypothesis locations,
closed target and local-`False` outcomes, definitional and equality transport,
dependent contexts, inaccessible local names, a custom discharger, declaration
trust, transactional failure, pre-existing metavariable state, reusable tactic
quotations, multi-variant selection, and source round trips. Its focused
seventeen-occurrence source fixture includes one explicitly unobserved reusable
occurrence. The representative gate now transforms all 17 calls in
`Mathlib/Algebra/AddConstMap/Basic.lean`, all 33 in
`Mathlib/CategoryTheory/EqToHom.lean`, all six in
`Mathlib/Data/Fintype/List.lean`, all seven in
`Mathlib/Algebra/Algebra/NonUnitalHom.lean`, and all three in
`Mathlib/Analysis/CStarAlgebra/SpecialFunctions/PosPart.lean`. Every transformed
copy compiles with zero remaining executable calls and passes the mandatory
declaration/environment oracle; the oracle accounts for 141, 134, 10, 165, and
5 declarations respectively under the public/computational and private-proof
rules. The last module records four distinct executions of
one occurrence and exercises a large `Matrix.cons_val` result; the focused
quotation executes both a successful and a failed variant.
The apply module has a checked import closure with no simplifier implementation.
`Mathlib/Algebra/Algebra/NonUnitalHom.lean` guards parser compatibility with
Mathlib commands whose grammar uses the identifier `apply`. These results are
bounded semantic acceptance evidence, not a Mathlib-wide translation claim.

The current scope-classification gate joins syntax ancestry to final
compiled declaration types. Its 13-occurrence fixture separates theorem/proof
definitions, computational definitions, proposition data, proof fields inside
non-proof structures, reusable tactic syntax, retained quotations, irreducible
definition RHSs, declaration-signature tactics, and generated commands. Four
fixture occurrences are resolved by a temporary source probe: anonymous Prop
and Nat examples exercise the temporary rename path, while generated proof and
data declarations exercise final-environment lookup. The probe carries a
stable occurrence ID into a standalone tactic, logs each execution, and emits
sorted evidence only after the original commands finish under probe-only
`set_option Elab.async false` scheduling. It never inspects simplifier internals
or infers that a retained quotation executed. Missing, duplicate, mixed, or
incomplete evidence remains unresolved. The classifier publishes independent
`executionRole`, `declarationKind`, and `action` fields; the fixture contains
11 direct, one reusable, and one retained occurrence. Under the revised contract,
proof/computational status selects how the final declaration is compared; it no
longer determines whether an executed call is translated.

The exact `Mathlib.Tactic.ToDual.«commandTo_dual_insert_cast_:=_»` command path
is a narrow static exception: its command elaborator consumes the RHS as the
proof value of a generated theorem, so its five old diagnostic cases are
classified as `direct_executable`/`generated_proof` even though no active caller
name is available during elaboration. Irreducible, generated, computational,
and signature/default executions are all materialization candidates. Mathlib
sources are parsed in the same pure `Mathlib` grammar
environment as the inventory; the fixture's custom grammar is isolated in a
separate environment.
Earlier broad module round trips remain useful renderer stress tests.

The boundary-native corpus manifest records repository, Lean, Mathlib,
implementation, source, and module identities together with a total
source-backed classification. It counts and collapses only byte-identical raw
syntax records that share one replaceable source range; conflicting records
fail. Multiple scope-tree paths to that range are retained and must agree on
the semantic classification. The implementation hash map is generated from
the complete active boundary, inventory, classifier, and manifest source-file
families rather than a hand-maintained subset. Manifest construction requires
the pinned Mathlib checkout to be clean and rechecks repository identity,
toolchain identity, implementation hashes, and every selected source after the
run, rejecting results when any of those inputs changed. Diagnostic allowances
for a dirty repository or unresolved occurrences are recorded explicitly in
the artifact. Its smoke gate builds
the representative 42-occurrence manifest twice, requires byte-identical output,
and rejects missing, duplicate, and unresolved joins by default. All 42
representative occurrences are marked `materialize`. Policy is checked before
atomic output replacement, so a rejected run cannot leave a new manifest that
looks successful. The existing diagnostic manifest's 101 old unknowns have
since been closed by a bounded 27-module run: 38 static non-proof commands, 3
signature exclusions, 5 generated proof commands, and 55 dynamically observed
proof declarations, with zero unclassified.

The resulting full pinned-corpus diagnostic manifest is
`.lake/boundary-corpus-manifest/manifest-scope-closed-v2.json` (SHA-256
`541a2d71f338e53b55335f76c699b14f8a2f12532b9a8cd865cbbd369e34ff25`).
Across 8,264 module files it inventories 83,425 occurrences: 69,403 eligible,
14,022 excluded, and zero unclassified under the obsolete proof-only rule. The
old exclusions comprise 13,981 occurrences in computational declarations, 38
in special computational commands, and 3 in signatures/defaults. These
categories are no longer excluded; every executable occurrence among them is a
translation candidate. Because the old classifier did not independently
separate executable code from syntax retained only as data, the exact revised
candidate count is not yet known. The old manifest is inventory evidence, not a
valid product partition. It was generated with the explicit `allowDirty: true`
diagnostic policy, so it must not be uploaded or treated as the clean archival
closure report. It also predates the commit-readiness hardening that added the
Lean inventory executable to the implementation fingerprint, so the current
runner intentionally rejects it. Regenerate the full manifest from the
committed code before further corpus materialization.

`Experiment/boundary_materialize_shard.py` consumes a current manifest fail
closed. The one-module canary for
`Mathlib/Algebra/AddConstMap/Basic.lean` transforms all 17 calls under manifest
schema 2. The current schema-5 report format carries artifact
schema 2, selector schema 1, semantic contract
`boundary-observable-v1`, the exact encoding policy, and one ordered
classification result per selected occurrence. The generated report records
the compilation, source-preservation, and declaration/environment checks. Pre-commit
manifests and reports are disposable because the commit changes their repository
identity. This is bounded semantic acceptance evidence, not a Mathlib-wide claim.

Step 6 adds whole-outer-call replacement for nested executable ranges. Report
schema 5 distinguishes `covered_by_ancestor` from independent replacement and
binds each covered call to its source-backed outer root. Nested calls are left
intact during stock recording and disappear with the outer call's arguments;
they are not replayed. Crossing ranges, mixed executable/retained containment,
and reusable tactic dependencies remain fail-closed. See the nested-coverage
contract in `PLAN.md`.
The nested gate checks 16 focused occurrences (seven roots, nine covered calls)
and all ten occurrences in Mathlib's `GroupWithZero/Action` (nine roots, one
covered call), with the declaration/environment oracle on both modules.

## Pinned environment and basic checks

The project uses Mathlib `v4.32.2`, resolved in `lake-manifest.json` to
`905b95818eb32af7874a58b427f50c1711a5e96c`, and Lean 4.32.2 commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`.

From the repository root:

```sh
lake build ExplicitLean ExplicitLeanMathlibAudit
python3 Experiment/check_simp_engine_review.py
python3 Experiment/check_simp_engine_boundary.py
python3 Experiment/check_simp_engine_boundary_source.py
python3 Experiment/check_simp_engine_boundary_nested.py
python3 Experiment/check_simp_engine_declaration_oracle.py
python3 Experiment/check_simp_engine_boundary_scope.py
python3 Experiment/check_simp_engine_boundary_corpus.py
python3 Experiment/check_simp_engine_boundary_mathlib.py
# Bounded diagnostic over the existing pre-probe 101-unknown manifest.
python3 Experiment/check_simp_engine_boundary_scope_unknowns.py
# Current schema-5 canary target: materialize and semantically check all 17 occurrences.
python3 Experiment/simp_engine_boundary_corpus.py manifest \
  --output .lake/boundary-corpus-manifest/add-const-map-canary.json \
  --module-prefix Mathlib/Algebra/AddConstMap/Basic.lean \
  --inventory-batch-size 1 --scope-batch-size 1 --timeout 600
python3 Experiment/boundary_materialize_shard.py \
  --manifest .lake/boundary-corpus-manifest/add-const-map-canary.json \
  --output .lake/boundary-materialization/add-const-map-canary/report.json \
  --module Mathlib/Algebra/AddConstMap/Basic.lean \
  --expect-total 17 --expect-materialize 17
```

The review command checks the frozen schema-27 contract. The boundary commands
check the active focused prototype, its focused source round trip, schema-2
execution-role classification, deterministic manifest construction, and the
representative Mathlib modules. The targeted scope-unknown command probes only
the affected modules from the earlier diagnostic manifest. The shard command
first builds a manifest bound to the current committed implementation and then
reproduces the accepted single-module canary.
`Experiment/run.sh` runs all legacy and active focused checks. None of these is
yet the complete pinned-corpus acceptance gate.

## Repository map

- `ExplicitLean/SimpEngine/Inventory.lean` and
  `Experiment/simp_engine_inventory.py`: syntax-aware occurrence inventory,
  stable source ranges, occurrence IDs, and compositional head rewriting. The
  inventory deliberately over-approximates source occurrences. The scope
  classifier supplies the source-backed execution role independently of
  declaration result kind.
- `ExplicitLean/SimpEngine/Recording.lean`: stock `Meta.simpGoal` oracle and
  goal/hypothesis transport patterns. Its current recorder is coupled to schema
  27 and should be mined, not adopted as the new artifact format.
- `ExplicitLean/SimpEngine/Fingerprint.lean`: legacy schema-27 fingerprint
  components. The active, simplifier-independent selector is
  `ExplicitLean/SimpEngine/Boundary/Selector.lean`.
- `ExplicitLean/SimpEngine/Boundary.lean` and `Boundary/`: active boundary
  oracle/comparator, closed artifacts, canonical selector, non-backtracking
  variant dispatch, simplifier-independent apply path, and temporary
  generated-source elaborator.
- `Experiment/check_simp_engine_boundary.py` and
  `Experiment/check_simp_engine_boundary_source.py`: active focused behavior,
  state, failure, trust, isolation, and source-materialization gates.
- `Experiment/SimpEngineBoundaryScope.lean` and
  `Experiment/check_simp_engine_boundary_scope.py`: conservative syntax-ancestry
  and compiled-declaration kind classification, plus the temporary
  ID-carrying execution probe and final-type evidence join.
- `ExplicitLean/SimpEngine/Boundary/ScopeProbe.lean`: standalone probe tactic
  and appended report command used only in disposable source copies.
- `Experiment/simp_engine_boundary_corpus.py` and
  `Experiment/check_simp_engine_boundary_corpus.py`: deterministic pinned-input
  manifest construction and its bounded fail-closed smoke gate.
- `Experiment/boundary_materialize_shard.py`: manifest-driven bounded recording,
  boundary materialization, exact source-preservation checking, compilation,
  and provenance reporting.
- `Experiment/check_simp_engine_boundary_scope_unknowns.py`: targeted closure
  diagnostic for the pre-execution-evidence 101 unknowns.
- `Experiment/check_simp_engine_boundary_mathlib.py`: scope-aware representative
  Mathlib-module recording, materialization, compilation, retained-syntax
  preservation, and zero-executable-call gate.
- `ExplicitLean/SimpEngine/Source.lean` and
  `ExplicitLean/SimpEngine/Replay.lean`: current schema-27 materialization and
  replay. These are legacy implementation, not the target apply path.
- `Experiment/check_simp_engine_source.py` and
  `Experiment/simp_engine_cloud.py`: complete-module materialization and corpus
  harnesses that can be adapted after the focused prototype works.
- `ExplicitLean/SimpEngine.lean`, `IR.lean`, `Runtime.lean`, and
  `SemanticSimproc.lean`: operational-replay research. Extend them only if a
  measured effect escapes the `simp` boundary and cannot be represented by a
  generic boundary transformation.

## Terminology

- **Source occurrence:** one parsed `simp` or `simp only` tactic node, identified
  by module and stable source range. It may be executable code or syntax retained
  as data.
- **Dynamic execution:** one elaboration-time execution of a source occurrence;
  an occurrence may execute zero, one, or several times.
- **Boundary state:** the continuation-visible tactic/elaboration state
  immediately before or after one dynamic execution.
- **Boundary variant:** the transformation recorded for one distinguishable
  pre-call boundary state and outcome.
- **Boundary artifact:** the closed generated data/source containing all
  variants for one occurrence. Older documents call the schema-27 equivalent a
  *certificate*; new code should prefer boundary terminology.
- **Recording:** running stock `simp` during translation to capture an oracle
  result and boundary delta.
- **Materialization:** rewriting source occurrences to the current
  `simp_engine_boundary_select` prototype and compiling the copied module with
  the original continuation unchanged except, when necessary, for consistent
  declaration-parameter alpha-renaming. The production public form is intended
  to be `simp_engine_apply`.
- **Closed-world closure:** successful translation and compilation of every
  executable occurrence under the pinned corpus, toolchain, and build procedure,
  with retained syntax data preserved separately.

The August 31–September 8 campaign is tracked in `WEEKLY.md` and
`tracking/campaign.json`. A fresh diagnostic inventory accounts for 83,425 calls
across 8,264 modules, including 66 reusable executable calls and five unresolved
quotations. It is not translated coverage. Artifact schema 2 replaces printed
Lean source with raw expression DAGs and captured, kernel-checked theorem
declarations; full-corpus translation and readability work remain in progress.
