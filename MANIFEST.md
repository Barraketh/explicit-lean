# Explicit Lean Manifest

Status: normative design draft, schema version 1.

Phase one and phase two each produce a deterministic NDJSON manifest. The manifest records correspondence, fingerprints, provenance, protected regions, normalization authority, environment effects, abstractions, and validation. It is an audit and optimization artifact; the generated `.lean` module remains standalone.

[PLAN.md](PLAN.md) defines the architecture and correctness contract. [CAPTURE.md](CAPTURE.md) defines how source-correlated inputs are obtained and stabilized. [LOWERING.md](LOWERING.md) owns lowering-rule meanings. [GRAMMAR.md](GRAMMAR.md) owns generated-language membership. [VERIFICATION.md](VERIFICATION.md) owns quotation format 1 and normalization.

## M1. File encoding and canonical JSON

A manifest is UTF-8 without a byte-order mark. It contains one JSON object per line, every line ends in LF, and there are no blank lines. The final line also ends in LF.

Every object is serialized as canonical JSON:

- object keys are sorted by their unescaped UTF-8 byte sequence;
- arrays preserve schema-defined order;
- only objects, arrays, strings, booleans, and arbitrary-precision nonnegative integers in canonical decimal notation are allowed;
- `null` and floating-point numbers are forbidden; an absent optional field is omitted;
- strings escape quotation mark, reverse solidus, and U+0000–U+001F using JSON's shortest standard escape, preferring `\b`, `\t`, `\n`, `\f`, and `\r` where applicable and lowercase hexadecimal in `\u00xx` otherwise;
- `/` and non-ASCII Unicode scalars are not escaped; and
- no insignificant whitespace occurs within a record.

Unknown top-level fields are forbidden. Extensible data appears only in an explicitly defined `data` object and still obeys canonical JSON.

Examples in this document are pretty-printed for readability. Actual records occupy one line and use canonical key ordering.

## M2. Scalar encodings

### Digests

A `Digest` is the string `sha256:` followed by exactly 64 lowercase hexadecimal digits. SHA-256 always operates on the exact byte sequence named by the fingerprint rule; it never hashes a platform-native string representation.

### Lean names

A Lean `Name` is a JSON array of components from root to leaf. A string component represents `Name.str`; a nonnegative integer represents `Name.num`. The anonymous root is `[]`.

For example, `_root_.List.map` is `["List", "map"]`. Encoding components rather than a dotted string preserves numeric and unusual name components without ambiguity.

Whenever names are sorted, compare the UTF-8 bytes of their canonical JSON encodings lexicographically. Whenever arrays are used as sort keys, compare elements lexicographically and place a proper prefix before the longer array.

### Source spans

A source span is:

```json
{
  "endByte": 42,
  "file": "Example.lean",
  "startByte": 17
}
```

Offsets are zero-based byte offsets into the exact UTF-8 source bytes and form a half-open interval. `file` is a slash-separated path relative to the package root. Absolute paths and `..` components are forbidden. A record omits its span when no meaningful source range exists.

### Stable record IDs

IDs consist of a one-letter record prefix followed by an eight-digit, zero-padded decimal ordinal starting at `00000001` independently for each prefix:

| Record | Prefix |
| --- | --- |
| import | `i` |
| source declaration | `s` |
| lowered declaration | `l` |
| correspondence | `c` |
| environment effect | `e` |
| normalization | `n` |
| provenance | `p` |
| protected region | `r` |
| abstraction | `a` |
| validation | `v` |

IDs are assigned only after records have been put in the canonical order specified by M14. IDs are local to one manifest; cross-build identity uses names and fingerprints.

## M3. Header

The first record is exactly one header:

```json
{
  "compiler": {
    "artifactConventionSet": 1,
    "captureArchitecture": 1,
    "executableFingerprint": "sha256:…",
    "loweringRuleSet": 1,
    "version": "0.1.0"
  },
  "compilerFingerprint": "sha256:…",
  "configuration": {
    "admittedImportedTrustedAxioms": [],
    "semanticBoundary": "closed-world",
    "sourceFeatureSet": "v0"
  },
  "configurationFingerprint": "sha256:…",
  "generatedModule": ["Explicit", "Example"],
  "generatedSourceFingerprint": "sha256:…",
  "normalizer": {
    "executableFingerprint": "sha256:…",
    "quotationFormat": 1,
    "ruleSet": 1,
    "version": "0.1.0"
  },
  "normalizerFingerprint": "sha256:…",
  "phase": 1,
  "quotationFormat": 1,
  "record": "header",
  "schema": "explicit-lean-manifest",
  "schemaVersion": 1,
  "sourceFingerprint": "sha256:…",
  "sourceModule": ["Example"],
  "toolchain": {
    "buildConfiguration": "Release",
    "leanCommit": "f3b06c705e6c85f5314019d5d3baab0fec5b580c",
    "leanExecutableFingerprint": "sha256:…",
    "leanVersion": "4.32.2",
    "targetTriple": "arm64-apple-darwin24.6.0"
  },
  "toolchainFingerprint": "sha256:…"
}
```

Required fields are:

| Field | Type | Meaning |
| --- | --- | --- |
| `compiler` | object | Exact compiler identity object defined below. |
| `compilerFingerprint` | Digest | Compiler executable, artifact conventions, capture architecture, and lowering-rule implementation fingerprint. |
| `configuration` | object | Complete semantic configuration; schema below. |
| `configurationFingerprint` | Digest | M15 fingerprint of `configuration`. |
| `generatedModule` | Name | Generated Lean module name under [L2 module mapping](LOWERING.md#l2-module-mapping). |
| `generatedSourceFingerprint` | Digest | SHA-256 of the exact generated `.lean` bytes. |
| `normalizer` | object | Exact quotation normalizer identity object defined below. |
| `normalizerFingerprint` | Digest | Quotation normalizer executable, rule registry, and version fingerprint. |
| `phase` | integer | `1` or `2`. |
| `quotationFormat` | integer | Canonical quotation encoder version; initially `1`. |
| `record` | string | Exactly `header`. |
| `schema` | string | Exactly `explicit-lean-manifest`. |
| `schemaVersion` | integer | Exactly `1`. |
| `sourceFingerprint` | Digest | SHA-256 of exact source-module bytes under M15. |
| `sourceModule` | Name | Original Lean module name. |
| `toolchain` | object | Exact pinned stock Lean identity object defined below. |
| `toolchainFingerprint` | Digest | Pinned Lean toolchain fingerprint under M15. |

The identity objects have exactly the keys shown in the example. Version strings are informational but exact. `executableFingerprint` and `leanExecutableFingerprint` hash exact executable bytes. The toolchain strings and commit are read from the pinned Lean executable and must match it exactly; `leanCommit` is exactly 40 lowercase hexadecimal digits. `artifactConventionSet` versions L2 module mapping, naming, declaration ordering, and G1 canonical layout, initially `1`. `captureArchitecture` is the architecture version from [CAPTURE.md](CAPTURE.md), initially `1`. `loweringRuleSet`, `ruleSet`, and both copies of `quotationFormat` must match the document versions and one another.

The version-1 `configuration` object has exactly these required keys:

| Key | Type | Values |
| --- | --- | --- |
| `admittedImportedTrustedAxioms` | array of Name | Duplicate-free, canonical-name-sorted allowlist of imported trusted-computation axioms; v0 requires `[]`. |
| `semanticBoundary` | string | `closed-world` or `drop-in` under [PLAN.md](PLAN.md#semantic-boundary). v0 requires `closed-world`. |
| `sourceFeatureSet` | string | Versioned feature-matrix identifier matching `[a-z][a-z0-9-]*`. |

The normalizer carries a versioned exact-`Name` registry of trusted-computation primitives, covered by its executable fingerprint. Every name in `admittedImportedTrustedAxioms` must be in that registry. Ordinary imported logical axioms remain explicit dependencies and are governed by the source-to-output subset checks; `sorryAx` and any forbidden primitive are rejected unconditionally.

A phase-two header additionally requires:

```json
{
  "optimizationBudget": {
    "metric": "utf8-bytes",
    "workLimit": 1000000,
    "workUnit": "candidate-evaluations",
    "workUsed": 750000
  },
  "phaseOneManifestFingerprint": "sha256:…"
}
```

`optimizationBudget.metric` is `utf8-bytes` and `workUnit` is `candidate-evaluations` in schema version 1. `workLimit` is a nonnegative deterministic limit, not elapsed time; it defaults to `1000000`. `workUsed` is the exact count defined by [PLAN.md](PLAN.md#deterministic-optimization-budget) and must not exceed the limit. `phaseOneManifestFingerprint` is the phase-one footer's `contentFingerprint`. Phase-one headers omit both phase-two fields.

## M4. Import records

There is one import record per generated source import, in source order:

```json
{
  "artifactFingerprint": "sha256:…",
  "id": "i00000001",
  "kind": "base",
  "module": ["Init"],
  "ordinal": 0,
  "record": "import"
}
```

Required fields are `artifactFingerprint`, `id`, `kind`, `module`, `ordinal`, and `record`. `kind` is `base` or `generated`. `ordinal` is zero-based and contiguous.

A generated import additionally requires `manifestFingerprint`, identifying the dependency's footer content fingerprint. A base import omits it. `artifactFingerprint` hashes the exact `.olean` bytes loaded for that imported module.

## M5. Source declaration records

There is one source declaration record for every constant in the captured source environment delta, including generated constants:

```json
{
  "axiomDependencies": [],
  "buildFingerprint": "sha256:…",
  "dependencies": [{"kind": "external", "targetName": ["Nat"]}],
  "id": "s00000001",
  "kind": "definition",
  "name": ["Example", "id"],
  "ordinal": 0,
  "portability": "portable",
  "record": "source-declaration",
  "semanticFingerprint": "sha256:…",
  "span": {
    "endByte": 42,
    "file": "Example.lean",
    "startByte": 0
  },
  "valueAvailability": "value"
}
```

Required fields are:

- `axiomDependencies`: canonical-name-sorted array of raw transitive axiom `Name`s from the independently elaborated declaration, before Q7 proof erasure;
- `buildFingerprint`: M15 declaration build fingerprint;
- `dependencies`: exact direct declaration-reference array defined by M10;
- `id`: source-declaration ID;
- `kind`: one of `abbrev`, `axiom`, `constructor`, `definition`, `equation`, `inductive`, `matcher`, `opaque`, `projection`, `recursor`, `structure`, or `theorem`;
- `name`: exact environment name;
- `ordinal`: zero-based declaration-delta order;
- `portability`: `portable` or `uses-imported-trusted-axiom`;
- `record`: exactly `source-declaration`;
- `semanticFingerprint`: M15 fingerprint of the fingerprint-normalized individual declaration quotation defined by [Q10](VERIFICATION.md#q10-equality-and-fingerprints); and
- `valueAvailability`: `none`, `value`, or `opaque-value`.

`span` is optional. A generated constant without its own range omits it and receives provenance under M11.

The M5 and M6 axiom arrays are audit facts, not normalized-equivalence claims, and corresponding arrays need not be identical. The verifier recomputes them, applies Q7's output-proof-axiom subset check, and separately compares every axiom dependency that remains outside proof markers in the normalized correspondence quotation.

## M6. Lowered declaration records

There is one lowered declaration record for every constant in the generated module's environment delta. This includes stock auxiliaries generated while elaborating the output and compiler-introduced helpers:

```json
{
  "axiomDependencies": [],
  "buildFingerprint": "sha256:…",
  "dependencies": [{"kind": "external", "targetName": ["Nat"]}],
  "id": "l00000001",
  "introducedBy": "lowering",
  "kind": "definition",
  "name": ["Example", "id"],
  "ordinal": 0,
  "portability": "portable",
  "record": "lowered-declaration",
  "semanticFingerprint": "sha256:…",
  "valueAvailability": "value"
}
```

Fields match M5, including required `dependencies` and `portability`, except that `introducedBy` is required and is one of `source`, `lowering`, `proof-sharing`, `mining`, or `stock-generated`. An optional `span` refers to the generated `.lean` module using its generated package-relative path. A declaration has `uses-imported-trusted-axiom` exactly when its transitive axiom dependencies contain a name in `admittedImportedTrustedAxioms`; otherwise it is `portable`. An imported trusted-computation axiom absent from that allowlist rejects compilation.

Every lowered declaration participates in at least one M7 correspondence. A compiler-introduced phase-two alias or abstraction corresponds to the source declarations whose quotations contain its expansion; it is never left unaudited.

## M7. Correspondence records

A correspondence is the unit compared by the verifier. It maps one or more source declarations to one or more lowered declarations:

```json
{
  "id": "c00000001",
  "kind": "binder-rewrite",
  "loweredDeclarationIds": ["l00000001"],
  "normalizationIds": ["n00000001"],
  "record": "correspondence",
  "sourceDeclarationIds": ["s00000001"]
}
```

Required fields are `id`, `kind`, `loweredDeclarationIds`, `normalizationIds`, `record`, and `sourceDeclarationIds`. Both declaration-ID arrays are nonempty, duplicate-free, and sorted by numeric ID. `normalizationIds` is duplicate-free and sorted; it may be empty for literal quotation equality.

`kind` is one of:

- `identity`;
- `binder-rewrite`;
- `class-lowering`;
- `instance-lowering`;
- `equation-match`;
- `structural-recursion`;
- `well-founded-fix`;
- `mutual-packing`;
- `local-lift`;
- `proof-sharing`;
- `deriving-expansion`;
- `generated-auxiliary`;
- `alias-expansion`; or
- `mined-abstraction`.

A transformation needing a new correspondence kind requires a schema revision; `other` is deliberately absent.

Every source declaration and every lowered declaration appears in at least one correspondence. Overlap is permitted for a generated group, but the set of correspondences must not authorize two incompatible expansions of the same quotation node.

## M8. Normalization records

A normalization record grants one lowering rule authority within one correspondence:

```json
{
  "correspondenceId": "c00000001",
  "id": "n00000001",
  "occurrences": [
    {
      "loweredPath": "/declarations/0/type/binder",
      "sourcePath": "/declarations/0/type/binder"
    }
  ],
  "record": "normalization",
  "ruleId": "L4"
}
```

Required fields are `correspondenceId`, `id`, `occurrences`, `record`, and `ruleId`. `ruleId` is one of the stable `L` identifiers defined by [LOWERING.md](LOWERING.md). `occurrences` is nonempty, sorted lexicographically by `sourcePath` then `loweredPath`, and contains no duplicates. For sorting, an omitted path precedes every present path.

Paths are RFC 6901 JSON Pointers into the pre-normalization correspondence-bundle quotation defined by [Q9](VERIFICATION.md#q9-paths). An occurrence may omit `sourcePath` when a compiler-introduced quotation node is unfolded away, or omit `loweredPath` when a source-only quotation node is erased, but it may not omit both.

The verifier recomputes the transformation; a normalization record is permission to apply a rule, not evidence that the result is valid. A rule may act only at listed paths and their structurally defined descendants. Broad wildcard paths are forbidden.

## M9. Environment-effect records

Every captured persistent environment, registration, code-generation, or runtime effect has a record:

```json
{
  "action": "erase",
  "effectKind": "instance-registration",
  "extractor": "lean/instance-extension",
  "id": "e00000001",
  "loweredDeclarationIds": ["l00000002"],
  "loweredFingerprint": "sha256:…",
  "record": "environment-effect",
  "ruleId": "L17",
  "sourceDeclarationIds": ["s00000002"],
  "sourceFingerprint": "sha256:…"
}
```

Required fields are `action`, `effectKind`, `extractor`, `id`, `loweredDeclarationIds`, `loweredFingerprint`, `record`, `ruleId`, `sourceDeclarationIds`, and `sourceFingerprint`.

`action` is `erase` or `lower` in a successful schema-version-1 manifest. A `preserve` or `reject` disposition prevents successful artifact emission and belongs in diagnostics rather than this manifest.

`effectKind` is one of `attribute`, `code-generation`, `coercion-registration`, `deriving-hook`, `elaboration-extension`, `foreign-function`, `instance-registration`, `runtime`, or `simp-registration`. `elaboration-extension` includes persistent syntax, notation, macro, command-elaborator, and term-elaborator registrations. A newly inventoried kind requires a schema revision.

`extractor` is the stable registry identifier matching `[a-z][a-z0-9-]*(/[a-z][a-z0-9-]*)*`. Declaration arrays are duplicate-free and ID-sorted; either may be empty when the effect is not owned by a constant or is erased without a replacement. Each present representation hashes the exact M15 environment-effect value `{"effectKind": effectKind, "extractor": extractor, "payload": value}`, where `value` is the extractor's canonical JSON projection. The absent representation uses the M15 empty-effect fingerprint.

## M10. Dependency data

Every declaration record contains a `dependencies` array. Each entry is exactly one of:

```jsonl
{"kind": "source", "targetId": "s00000004"}
{"kind": "lowered", "targetId": "l00000007"}
{"kind": "external", "targetName": ["Nat", "succ"]}
```

A source declaration contains only `source` and `external` dependencies. A lowered declaration contains only `lowered` and `external` dependencies. Entries are duplicate-free and sorted by `kind`, then target ID or encoded name. Dependencies are the exact direct constant references found in the independently elaborated declaration's complete type and value before proof erasure or M8 normalization; same-module names become declaration IDs and imported names remain `external`. Consumers may traverse these explicit edges transitively, while schema-version-1 build fingerprints use the complete containing-artifact hashes defined by M15 and therefore do not recursively hash the graph.

An optional `environmentReads` array contains M15 environment-read digests of captured nondeclaration environment values that affected elaboration or transformation. Each digest hashes `{"extractor": extractor, "key": key, "value": value}`, where `extractor` follows the M9 identifier syntax and `key` and `value` are the extractor's canonical JSON projections. The array is duplicate-free and digest-sorted.

## M11. Provenance records

Provenance relates optional source-correlated capture to declarations without making it executable:

```json
{
  "data": {
    "capturedAlternativeCount": 2
  },
  "dataFingerprint": "sha256:…",
  "id": "p00000001",
  "kind": "match-capture",
  "loweredDeclarationIds": ["l00000001"],
  "record": "provenance",
  "sourceDeclarationIds": ["s00000001"]
}
```

Required fields are `dataFingerprint`, `id`, `kind`, `loweredDeclarationIds`, `record`, and `sourceDeclarationIds`, plus exactly one of `data` or `dataRef`. Declaration arrays are duplicate-free and ID-sorted. `data` is an opaque canonical JSON value: correctness must not depend on a consumer understanding it, while the producing compiler version may use it as an optimization hint. `dataFingerprint` is its M15 tagged fingerprint. Large traces may replace `data` with `dataRef`, but never contain both:

```json
{
  "dataRef": {
    "encoding": "canonical-json",
    "fingerprint": "sha256:…",
    "path": "Explicit/Example.provenance/p00000001.json"
  }
}
```

The sidecar path is relative to the generated output root, follows the same lexical constraints as M2, and lies beneath the module's [L2 provenance directory](LOWERING.md#l2-module-mapping). Its exact bytes hash directly to `fingerprint`; decoding those canonical JSON bytes and applying the M15 provenance domain yields `dataFingerprint`. A standalone `.lean` artifact remains usable if provenance and sidecars are lost.

`kind` is one of `deriving-trace`, `equation-capture`, `generated-auxiliary`, `local-lift`, `match-capture`, `recursion-capture`, `source-syntax`, or `tactic-trace`. A new kind requires a schema revision.

An optional `span` uses M2.

A source-only command, modifier, binder annotation, or notation occurrence that leaves no persistent environment effect is represented by `source-syntax` provenance. If erasing it changes the compared quotation, the same transformation also has an M8 normalization record. Persistent effects always use M9 instead; provenance alone never authorizes erasure.

## M12. Protected-region records

A protected region identifies source structure that mining must retain:

```json
{
  "id": "r00000001",
  "kind": "canonical-recursive-match",
  "loweredRegions": [
    {
      "declarationId": "l00000001",
      "path": "/value/body"
    }
  ],
  "record": "protected-region",
  "sourceRegions": [
    {
      "declarationId": "s00000001",
      "path": "/value/body"
    }
  ]
}
```

Required fields are `id`, `kind`, `loweredRegions`, `record`, and `sourceRegions`. Each region entry has exactly `declarationId` and `path`; its path is relative to that declaration's pre-normalization individual quotation under [Q9](VERIFICATION.md#q9-paths), not to an M8 correspondence bundle. Both arrays are nonempty, contain no duplicate ID/path pair, and are sorted by declaration ID then path. This representation covers both a subterm in one declaration and a protected group spanning several declarations.

`kind` is one of `canonical-match`, `canonical-recursive-match`, `equation-branches`, `inductive-block`, `mutual-group`, `patterns`, `structure`, or `well-founded-presentation`.

## M13. Phase-two abstraction records

Phase-one manifests contain no abstraction records. Each phase-two rewrite has one:

```json
{
  "costAfter": 120,
  "costBefore": 200,
  "expansionFingerprint": "sha256:…",
  "id": "a00000001",
  "inputDeclarations": [
    {
      "name": ["Example", "first"],
      "semanticFingerprint": "sha256:…"
    },
    {
      "name": ["Example", "second"],
      "semanticFingerprint": "sha256:…"
    }
  ],
  "kind": "exact-sharing",
  "outputDeclarationIds": ["l00000001", "l00000002", "l00000003"],
  "record": "abstraction",
  "rewriteOrdinal": 0,
  "workAtAcceptance": 57
}
```

Required fields are `costAfter`, `costBefore`, `expansionFingerprint`, `id`, `inputDeclarations`, `kind`, `outputDeclarationIds`, `record`, `rewriteOrdinal`, and `workAtAcceptance`. `inputDeclarations` identifies phase-one declarations by `name` and `semanticFingerprint`, is nonempty, duplicate-free, and sorted by encoded name then fingerprint. `outputDeclarationIds` identifies current phase-two declarations and is nonempty, duplicate-free, and ID-sorted. `rewriteOrdinal` is zero-based and contiguous and gives the deterministic application order. `costBefore` and `costAfter` are the complete generated-module UTF-8 byte counts immediately before and after that rewrite. `workAtAcceptance` is the cumulative candidate count when the rewrite was accepted; it is strictly increasing and no greater than the header's `workUsed`. All are nonnegative integers, and `costAfter` must be less than `costBefore`.

`kind` is one of `alias`, `anti-unification`, `data-description`, `exact-sharing`, `generated-renaming`, `local-let`, `namespace-factoring`, or `source-aligned-helper`. `expansionFingerprint` hashes a Q2 bundle containing the affected declarations in `outputDeclarationIds` order after every compiler-introduced abstraction created by this rewrite is expanded back to its immediately preceding representation and each declaration is independently fingerprint-normalized under Q10. For namespace factoring or renaming, no expression expansion occurs and this is the unchanged bundle of fingerprint-normalized affected declarations.

The verifier recomputes each expansion fingerprint and byte cost while deterministically replaying abstraction records from the phase-one artifact in `rewriteOrdinal` order. It does not infer an acceptance-time candidate by reversing the final source.

The first rewrite's `costBefore` equals the exact phase-one `.lean` byte length. Each later `costBefore` equals the preceding `costAfter`, and the final `costAfter` equals the phase-two generated source byte length. A phase-two manifest with no rewrites requires byte-identical phase-one and phase-two generated source.

## M14. Validation records, footer, and record order

A successful manifest contains validation records only with `result: "pass"`:

```json
{
  "checker": "normalized-quotation-equality",
  "id": "v00000001",
  "record": "validation",
  "result": "pass",
  "targetId": "c00000001"
}
```

Required fields are `checker`, `id`, `record`, `result`, and `targetId`. `checker` is one of `axiom-dependencies`, `environment-effects`, `grammar`, `kernel`, `normalized-quotation-equality`, `search-audit`, or `structural-recursion`. `targetId` names a correspondence, declaration, protected region, or the literal string `module`.

The final record is exactly one footer:

```json
{
  "contentFingerprint": "sha256:…",
  "record": "footer",
  "recordCount": 27
}
```

`recordCount` counts every preceding record including the header and excluding the footer. `contentFingerprint` is SHA-256 of the exact bytes of all preceding canonical records, including each LF.

Records occur in this order:

1. header;
2. imports by `ordinal`;
3. source declarations by `ordinal`;
4. lowered declarations by `ordinal`;
5. correspondences sorted by source-ID array, then kind, then lowered-ID array;
6. environment effects sorted by `effectKind`, source-ID array, then source fingerprint;
7. normalizations sorted by correspondence ID, rule ID, then occurrence array;
8. provenance sorted by kind, source-ID array, lowered-ID array, then data fingerprint;
9. protected regions sorted by kind, source-region array, then lowered-region array;
10. abstractions by `rewriteOrdinal`;
11. validations sorted by target ID then checker; and
12. footer.

ID assignment is staged: import and declaration IDs follow their ordinals; correspondence and environment-effect IDs follow their specified sorts; records that refer to those IDs are then sorted and assigned. Finally, all records are serialized in the order above. References therefore never depend on discovery order, hash-map iteration, task scheduling, or wall-clock timing.

A successful manifest has exactly these validation records:

- `environment-effects`, `grammar`, `kernel`, and `search-audit` for target `module`;
- `normalized-quotation-equality` and `axiom-dependencies` for every correspondence; and
- `structural-recursion` for every `structural-recursion` correspondence.

No duplicate checker/target pair is permitted.

## M15. Fingerprint domains

Every structured fingerprint hashes:

```text
UTF8(domain) || 0x00 || canonicalJSON(value)
```

where `domain` is the exact ASCII tag below and `value` is the specified canonical JSON value. Raw-file fingerprints are the stated exception.

| Fingerprint | Domain and value |
| --- | --- |
| Source | Raw SHA-256 of the exact source bytes. |
| Generated source | Raw SHA-256 of the exact generated `.lean` bytes. |
| Configuration | `explicit-lean/config/v1`; header `configuration`. |
| Toolchain | `explicit-lean/toolchain/v1`; header `toolchain`. |
| Compiler | `explicit-lean/compiler/v1`; header `compiler`. |
| Normalizer | `explicit-lean/normalizer/v1`; header `normalizer`. |
| Import artifact | Raw SHA-256 of exact imported artifact bytes. |
| Declaration input | `explicit-lean/declaration-input/v1`; exact object defined below. |
| Declaration build | `explicit-lean/declaration-build/v1`; exact object defined below. |
| Semantic quotation | `explicit-lean/quotation/v1`; canonical fingerprint-normalized individual declaration quotation defined by [Q10](VERIFICATION.md#q10-equality-and-fingerprints). |
| Environment effect | `explicit-lean/environment-effect/v1`; canonical captured effect value. |
| Empty environment effect | `explicit-lean/environment-effect/v1`; empty object `{}`. |
| Environment read | `explicit-lean/environment-read/v1`; canonical environment-read value defined by M10. |
| Provenance data | `explicit-lean/provenance/v1`; canonical `data`. |
| Abstraction expansion | `explicit-lean/abstraction-expansion/v1`; Q2 bundle of fingerprint-normalized expanded declarations defined by M13. |

Arrays in fingerprint values retain semantic order unless their schema explicitly says sorted.

The declaration-input value has exactly these keys:

```json
{
  "artifactFingerprint": "sha256:…",
  "kind": "source",
  "name": ["Example", "id"]
}
```

`kind` is `source` or `lowered`. A source input uses the header's `sourceFingerprint`; a lowered input uses `generatedSourceFingerprint`. `name` is the declaration record's exact name. Hashing the complete containing artifact is an intentional module-granular schema-version-1 invalidation policy; a future schema may add independently specified declaration slices.

The declaration-build value has exactly these keys:

```json
{
  "compilerFingerprint": "sha256:…",
  "configurationFingerprint": "sha256:…",
  "declarationInputFingerprint": "sha256:…",
  "environmentReadFingerprints": ["sha256:…"],
  "importArtifactFingerprints": ["sha256:…"],
  "normalizerFingerprint": "sha256:…",
  "phase": 1,
  "toolchainFingerprint": "sha256:…"
}
```

`declarationInputFingerprint` is the declaration-input fingerprint defined above. Import fingerprints retain import order, and environment-read fingerprints are digest-sorted. M10 dependency records remain explicit invalidation and audit edges, but schema version 1 does not recursively embed dependency build fingerprints: the complete source or generated artifact fingerprint and exact import artifacts already cover their contents without a cyclic hash definition.

A phase-two declaration-build value additionally has `optimizationBudget` and `phaseOneManifestFingerprint`, copied exactly from the header. A phase-one value omits them.

## M16. Completeness invariants

A schema-version-1 manifest is valid only if:

- record syntax, ordering, IDs, references, fingerprints, and footer validate;
- the header's generated-source fingerprint matches the accompanying `.lean` artifact;
- every source and lowered declaration appears in at least one correspondence;
- every applied normalization has a record and every normalization record names an authorizing lowering rule;
- every captured environment effect has a successful `erase` or `lower` record;
- every compiler-introduced declaration is covered by correspondence and provenance;
- every protected source region has a lowered counterpart;
- phase-one manifests contain no abstraction records;
- phase-two manifests identify the phase-one manifest and account for every introduced abstraction;
- all required validation records pass; and
- recomputing a clean build under the header inputs produces identical `.lean`, manifest, and provenance-sidecar bytes.

An unsuccessful compilation does not emit a manifest that looks successful. Diagnostics use the separate interface described in [next-steps.md](next-steps.md#diagnostics) and never end with a passing manifest footer.
