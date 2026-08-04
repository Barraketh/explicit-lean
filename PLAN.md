# Explicit Lean

Status: design draft.

## Goal

Build a source-to-source compiler from Lean to a compact, readable, deterministic subset of Lean. The output should:

- compile with a pinned stock Lean toolchain;
- be straightforward to translate into other languages;
- preserve source-level mathematical and program structure useful to people and proof-generating models; and
- contain no proof search, instance search, hidden coercion insertion, holes, or unresolved elaboration choices.

Explicit Lean is not a pretty-printed kernel AST. It eliminates contextual synthesis while retaining syntax-directed compilation.

## Specification map

This document owns the goals, architecture, correctness contract, and compression policy. Five companion specifications own the contractual detail:

- [CAPTURE.md](CAPTURE.md) defines how one source elaboration is observed and which source-correlated facts must be retained.
- [GRAMMAR.md](GRAMMAR.md) defines the exact generated-language grammar and the elaboration audit required for membership in Explicit Lean.
- [LOWERING.md](LOWERING.md) defines how source Lean constructs are transformed into that grammar.
- [MANIFEST.md](MANIFEST.md) defines the deterministic NDJSON correspondence and provenance format shared by lowering, mining, and verification.
- [VERIFICATION.md](VERIFICATION.md) defines quotation format 1, normalization execution, proof checks, and semantic comparison.

Each rule has one owning document. If an overview here appears to conflict with a companion specification, the companion specification controls within its stated area. Such a conflict is still a documentation bug and must be fixed rather than treated as a lasting precedence mechanism.

The non-normative working sequence and current v0 feature set live in [next-steps.md](next-steps.md).

## Source language policy

Preserve meaningful structure:

- namespaces, declaration names, and useful binder names;
- inductive and mutual-inductive blocks;
- pattern matching and the branch and pattern structure of equation-style definitions;
- structural and mutual recursion; and
- well-founded recursive definitions, with their measures and explicit termination certificates.

Make elaboration choices explicit:

- rewrite implicit and instance parameters as ordinary explicit parameters;
- supply every argument selected by elaboration at every call site;
- emit universe parameters and instantiations explicitly;
- resolve overloaded notation, coercions, and global names; and
- replace tactic proofs with checked proof terms.

Lean-generated constructors, recursors, and projections may retain their stock binder styles. References to them expose and supply every hidden argument. The output contains no tactic blocks or tactic-driven termination clauses.

The lowerer may reject a source construct when the captured elaboration artifacts are insufficient to express it in the generated grammar or to validate the required source correspondence. Unsupported lowering is a diagnosed outcome, not permission to emit syntax outside Explicit Lean.

## Output-language summary

Membership in Explicit Lean is determined by the syntactic whitelist in [GRAMMAR.md](GRAMMAR.md) together with its elaboration audit. Merely elaborating to an acceptable kernel expression is not sufficient.

At a high level, a generated module contains imports, the fixed `set_option autoImplicit false` directive, namespaces, and declarations from a small whitelist. Declaration headers expose all source parameters. Terms use explicit universes, applications, typed binders and lets, fully named constants, canonical matches, an audited type-ascribed empty elimination, explicit recursors, and explicit recursion certificates. Tactics, holes, contextual name lookup, type-class search, coercion insertion, notation-driven operations, and user-defined output syntax are absent.

The grammar permits two compact primitive leaves: `nat_lit n` for a raw `Nat` and a canonically escaped string literal for a primitive `String`. All other literals and notation expose the exact operations, dictionaries, proofs, constructors, and evaluation order selected while elaborating the source.

## Correctness contract

The original Lean source is the primary input. Its elaborated environment and source-correlated capture are the semantic oracle. Correctness has two independent requirements.

### Deterministic compilation

Given identical source bytes, imported artifacts, compiler version, configuration, and optimization budget, the compiler must produce identical UTF-8 `.lean` and manifest bytes. Ordering, generated names, layout, line endings, fingerprints, and optimization tie-breaking are therefore canonical. This is a reproducibility requirement for a pinned environment; it does not promise identical output across toolchain or dependency upgrades.

### Per-declaration semantic equivalence

Every declaration in the original module's environment delta, including declarations generated while elaborating the source, has a corresponding Explicit Lean declaration or a documented correspondence to a permitted declaration group. Applying corresponding definitions to the translated arguments—including universe, type, dictionary, coercion, proof, and ordinary arguments inserted by source elaboration—must produce the same result.

The mechanical test is **normalized quotation equality** under [VERIFICATION.md](VERIFICATION.md). The verifier independently elaborates the original and generated modules, quotes corresponding declarations into quotation format 1, normalizes the quotations using only versioned rules authorized by [LOWERING.md](LOWERING.md), and requires literal equality.

The quotation contains the declaration kind, universe parameters, type, value when available, relevant generated declarations, and dependencies. Normalization may only account for documented representation changes. In particular, a rule may:

- discard binder names and binder-style annotations;
- alpha-normalize universe parameters and mapped private or generated names;
- remove the documented `optParam`, `autoParam`, `outParam`, and `semiOutParam` wrappers and the `nondep` let bit after checking retained components;
- translate documented class, instance, registration, recursion, and generated-declaration representations;
- unfold aliases, proof-sharing helpers, and mined abstractions introduced by this compiler; and
- replace proof-irrelevant subterms with a canonical proof marker after the separate proof checks below.

The normalizer may not unfold unrelated source declarations, perform arbitrary reduction or simplification, invoke instance or proof search, or appeal to a general program-equivalence procedure. Every applied rule is recorded in the manifest by its stable lowering-rule identifier.

Before proof-marker normalization, the verifier must:

1. kernel-check the complete unnormalized output term;
2. infer, in its local context, the source and output subterm types and verify that the normalized types are corresponding propositions;
3. compute transitive axiom dependencies; and
4. reject unresolved metavariables, `sorryAx`, unsupported trusted primitives, or any output axiom dependency absent from the corresponding source proof.

Using fewer proof axioms is permitted. Proof normalization does not apply to `Decidable P`, equality-test dictionaries, subtype data, or any other computational value merely because it contains proofs.

For each generated module, verification must:

1. elaborate the source and capture syntax, elaboration information, the declaration delta, persistent environment effects, code-generation metadata, and kernel expressions;
2. generate stock Lean source accepted by the Explicit Lean grammar checker;
3. compile the result with elaboration auditing enabled;
4. compare every source/lowered declaration correspondence by normalized quotation equality; and
5. reject added axioms, holes, unmatched declarations or dependencies, undocumented normalization, forbidden search, or generated metadata whose documented disposition is `reject`.

The generated module may not import the source module or declarations it encodes, embed a compressed artifact in metaprogramming, or rely on a custom output-language plugin.

## Architecture

### Source-correlated lowering input

Lowering receives both source-aligned constructs and their fully elaborated meaning. A transformation keeps source structure when it belongs to Explicit Lean and replaces only its hidden elaboration or search-dependent parts. The implementer owns the internal representation; it is not part of the language or correctness contract. Kernel or NDJSON conversion is a verifier and fallback representation, not the source of presentation.

The capture mechanism is defined by [CAPTURE.md](CAPTURE.md). It uses Lean's pinned stock in-process frontend, completed command snapshots, information trees, environment deltas, and registered effect extractors. Narrow observer-only instrumentation against the pinned Lean source is permitted only when a coverage probe demonstrates that a required transient choice is unavailable through the stock facilities. The output always compiles with stock Lean.

### Two-phase compilation

The compiler has two conceptually separate phases with a valid Explicit Lean program at their boundary.

1. **Lowering:** Resolve every elaboration choice and replace every disallowed construct with syntax described by [GRAMMAR.md](GRAMMAR.md), using [LOWERING.md](LOWERING.md). Phase one is responsible for determinism, semantic preservation, and language membership, not optimal abstraction. It may duplicate terms and expand generated declarations. An elaborated expansion is a valid fallback only when it is representable, preserves every protected source region, and passes verification; otherwise the source construct is unsupported.
2. **Abstraction mining:** Analyze the lowered program for repeated typed structure and replace it with shared permitted abstractions. This includes exact sharing, aliases, reusable helpers, generic datatype descriptions, source-aligned typed abstraction, and typed anti-unification. Each rewrite must preserve phase-one correspondences and remain valid Explicit Lean.

The mining phase operates on the explicit program. Provenance may guide specialized strategies but is never needed to recover a hidden elaboration choice or to compile the phase-one artifact.

### Phase artifacts

Phase one produces:

- a standalone deterministic `.lean` module containing the complete naive lowering; and
- a deterministic NDJSON manifest conforming to [MANIFEST.md](MANIFEST.md).

The `.lean` module is the actual phase boundary. A generic phase-two miner re-elaborates it to recover types. The manifest is an audit trail and optimization aid, not a hidden semantic component.

Phase two produces another standalone deterministic `.lean` module and a phase-two manifest. The updated manifest retains phase-one correspondence by immutable manifest fingerprint, establishes current source-to-phase-two correspondence, and records introduced aliases, helpers, abstractions, their canonical expansions, fingerprints, and the metric and budget that selected them.

Manifests distinguish:

- a **build fingerprint** covering exact source and environment inputs that can affect elaboration or transformation; and
- a **semantic fingerprint** covering a normalized quotation.

These fingerprints support content-addressed incremental compilation. Reuse is always a candidate optimization, never trust: a reused declaration must compile and revalidate in the new pinned environment. Invalidation may begin at module granularity and later become declaration-granular. Under fixed inputs, a clean and incremental build must produce byte-identical artifacts.

### Semantic boundary

The v0 compiler uses a **closed-world** boundary. Every consumer of a translated declaration is assumed to be part of the translated generated-module set. The compiler may therefore erase a registration or other environment effect only after all of its known uses have been materialized explicitly and the verifier rule for that erasure passes. Generated modules are not promised to be drop-in replacements for arbitrary untranslated Lean clients.

A future **drop-in** boundary would additionally require unknown clients importing the generated module to observe the source module's public names, registrations, attributes, coercions, instances, and other supported environment behavior. Selecting closed-world never weakens per-declaration normalized quotation equality or permits an unrecorded effect; it limits which external observations must be reproduced.

## Compression policy

Phase two minimizes a fixed metric, initially UTF-8 bytes, subject to correctness and source-structure protections. Phase one is not judged by this metric beyond avoiding pathologically impractical output.

Apply optimizations in this order:

1. namespace factoring, explicit aliases, and compact generated names;
2. exact sharing within and across declarations;
3. source-aligned typed abstraction of repeated patterns; and
4. broader typed anti-unification only when it preserves protected source structure.

Inductive blocks, canonical recursive matches, mutual groups, patterns, and source-aligned recursion presentations are protected regions. Generated abstractions require measured positive savings and may not replace recognizable structure with opaque compiled fixpoints or arbitrary helpers.

### Deterministic optimization budget

Phase two uses a per-module work budget measured only in candidate evaluations. The default limit is `1000000`; a nonnegative command-line override becomes part of the phase-two header and fingerprints. Wall-clock time, memory pressure, and thread scheduling never affect which successful artifact is selected. An operational resource failure emits no successful manifest.

A candidate receives one work unit when its complete deterministic description is removed from the duplicate set and submitted for type checking and exact rerendering. Valid, invalid, profitable, and unprofitable candidates all consume that unit. Candidate descriptions are enumerated by kind in this exact order: `namespace-factoring`, `alias`, `generated-renaming`, `exact-sharing`, `local-let`, `source-aligned-helper`, `data-description`, and `anti-unification`. Within a kind they are ordered by input declaration names, source paths, and canonical description bytes.

At each iteration, phase two evaluates the deterministic prefix that fits the remaining budget. It selects the candidate with greatest positive UTF-8 byte savings; ties use enumeration order. After accepting one candidate, it rerenders and revalidates the complete module, then starts a new iteration. It stops when the next evaluation would exceed the limit or the evaluated prefix contains no profitable valid candidate. The manifest's `workUsed` is the exact cumulative count.

## Implementation status

The toolchain baseline is pinned by `lean-toolchain` and `lakefile.toml`: Lean `v4.32.2` with the matching Mathlib `v4.32.2` release. `lake-manifest.json` locks Mathlib and its transitive dependencies to exact commits.

The capture architecture, closed-world v0 boundary, quotation format, artifact conventions, initial host, and executable interface are decided. The internal compiler representation remains an implementation choice. The v0 vertical slice, ordered work packages, and completion criteria are maintained in [next-steps.md](next-steps.md).

## Initial non-goals

- Reproducing original formatting or tactic scripts.
- Preserving binder-style metadata or private generated names exactly.
- Defining another Lean-like source language.
- Exposing matcher or equation-compiler artifacts merely because they occur in a kernel export.
- Retaining incidental Lean-specific well-founded-recursion packing when a source-aligned explicit formulation is available.
- Claiming a globally smallest encoding; the objective is the smallest found within the fixed Explicit Lean contract.
