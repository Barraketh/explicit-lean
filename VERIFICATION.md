# Verification and Quotations

Status: normative design draft, quotation format 1 and normalizer rule set 1.

This document defines the verifier-owned quotation format, normalization procedure, proof checks, and comparison algorithm used by [PLAN.md](PLAN.md). [LOWERING.md](LOWERING.md) authorizes representation changes. [MANIFEST.md](MANIFEST.md) records their exact occurrences and fingerprints. [GRAMMAR.md](GRAMMAR.md) separately defines generated-language membership and elaboration auditing.

Quotation format 1 is a stable verification and fingerprint boundary, not the compiler's internal IR. An implementation may use any internal representation if it produces exactly the canonical values and results specified here.

## Q1. Independent verification

The verifier elaborates the original and generated modules independently in separate environments constructed from their pinned imports. It does not trust capture records, generated syntax, manifest claims, cached quotations, or the compiler's earlier type checks.

Before quoting a declaration, the verifier requires Lean's kernel to accept its complete type and value when available. It rejects unresolved metavariables, `sorryAx`, unsupported trusted primitives, missing declarations, and a generated environment that imports the source module or an artifact containing the declarations being reproduced.

The source environment supplies the semantic oracle. Capture and provenance identify intended correspondences and normalization authority, but only independently recomputed declarations, types, dependencies, effects, and quotations determine success.

## Q2. Quotation units

Quotation format 1 uses canonical JSON under M1. Examples here are pretty-printed only for readability.

An individual declaration quotation is:

```json
{
  "axiomDependencies": [],
  "dependencies": [{"kind": "external", "name": ["Nat"]}],
  "kind": "definition",
  "type": {
    "levels": [],
    "ref": {"kind": "external", "name": ["Nat"]},
    "tag": "constant"
  },
  "universeParameters": [],
  "value": {"kind": "natural", "tag": "literal", "value": 0},
  "valueAvailability": "value"
}
```

Required fields are `axiomDependencies`, `dependencies`, `kind`, `type`, `universeParameters`, and `valueAvailability`. `kind` and `valueAvailability` use the M5 values. `value` is required exactly when availability is `value` or `opaque-value`.

The declaring constant's own name is not a field. Its identity is supplied by the manifest declaration record, while references are classified under Q4. Omitting the own name allows a renamed, otherwise identical declaration to retain its semantic fingerprint without weakening cross-build identity, which remains the pair of manifest name and semantic fingerprint.

A correspondence quotation is a bundle:

```json
{
  "declarations": [],
  "format": 1
}
```

The source bundle contains the M7 source declarations in source-declaration ID order. The lowered bundle contains the M7 lowered declarations in lowered-declaration ID order. Rule-specific normalization may change bundle structure only when the correspondence kind and an M8 occurrence at the bundle root authorize it.

An M5 or M6 `semanticFingerprint` hashes the fingerprint-normalized individual declaration quotation defined by Q10. That single-declaration operation is deliberately independent of correspondence-bundle rewrites. M7 verification separately compares normalized source and lowered bundles literally.

## Q3. Levels and binders

Levels are encoded after the L3 normalization required by [LOWERING.md](LOWERING.md):

```text
Level ::= {"tag":"zero"}
        | {"index":Nat,"tag":"parameter"}
        | {"amount":PositiveNat,"of":Level,"tag":"successor"}
        | {"items":[Level,Level,...],"tag":"max"}
        | {"left":Level,"right":Level,"tag":"imax"}
```

`parameter.index` is the zero-based position in the declaration's `universeParameters`. A successor combines every consecutive successor into one positive `amount`. A `max` has at least two duplicate-free operands sorted by their canonical JSON bytes. Neutral zero operands are absent. `imax` retains argument order. A level metavariable is forbidden.

`universeParameters` initially contains the exact Lean `Name` of each parameter in environment order, encoded under M2. Normalization replaces those names with their zero-based positions after verifying equal arity and consistent use. Explicitly declared unused parameters therefore remain significant.

A binder is:

```json
{
  "info": "implicit",
  "name": ["x"],
  "type": {"level": {"tag": "zero"}, "tag": "sort"}
}
```

`info` is `explicit`, `implicit`, `strict-implicit`, or `instance`. `name` is the exact user name encoded as an M2 `Name`, with `[]` for anonymous. Bound-variable references use de Bruijn indices, so names are presentation metadata. When L4 or Q10 removes both fields, the normalized binder object is exactly `{"type": Expr}`. L4 does so only at authorized occurrences after comparing binder types.

## Q4. References and expressions

An encoded reference is exactly one of:

```jsonl
{"index":0,"kind":"member"}
{"kind":"source","name":["Example","f"]}
{"kind":"external","name":["Nat","succ"]}
{"kind":"compiler","name":["Example","f","_explicit","aux1"]}
```

`member` addresses a declaration in the current correspondence bundle. `source` is the exact name of a source-module declaration outside the current bundle. A lowered declaration maps to `source` only through an unambiguous M7 correspondence. `external` names an imported declaration shared by both environments. `compiler` is a compiler-introduced declaration without a source identity. It may remain in an individual compiler-introduced declaration fingerprint, but a correspondence bundle cannot compare equal while retaining an unmatched compiler reference on only one side. An ambiguous mapping is a verifier failure.

For the individual fingerprint context in Q10, the target declaration is a one-member bundle and references to it use `member` index zero. Every other reference uses `source`, `external`, or `compiler` by the rules above. This makes the fingerprint context unique even when a declaration participates in more than one M7 correspondence.

Expressions use these canonical objects:

```text
Expr ::= {"index":Nat,"tag":"bvar"}
       | {"level":Level,"tag":"sort"}
       | {"levels":[Level...],"ref":Reference,"tag":"constant"}
       | {"arguments":[Expr...],"function":Expr,"tag":"application"}
       | {"binder":Binder,"body":Expr,"tag":"lambda"}
       | {"binder":Binder,"body":Expr,"tag":"forall"}
       | {"body":Expr,"name":Name,"nondependent":Bool,
          "tag":"let","type":Expr,"value":Expr}
       | {"kind":"natural","tag":"literal","value":Nat}
       | {"kind":"string","tag":"literal","value":String}
       | {"index":Nat,"structure":Reference,"tag":"projection","value":Expr}
       | {"tag":"proof"}
```

An application has at least one argument and is the maximal left-associated application spine. Lambda and `forall` bodies use de Bruijn index zero for the new binder. A `let` body likewise uses index zero for the new local. Projection `index` is Lean's zero-based projection index.

`proof` is never present in a pre-normalization quotation. Q7 introduces it only after the required proof checks.

Closed declaration quotations contain no free-variable or metavariable form. `Expr.mdata` is not encoded because kernel definitional equality ignores it; its body is quoted directly. Capture retains source metadata independently when lowering or provenance needs it.

## Q5. Dependencies and intrinsic canonicalization

Before rule-authorized normalization, the quotation encoder performs only these representation-intrinsic operations:

1. translate bound variables to de Bruijn indices;
2. remove `Expr.mdata` wrappers;
3. flatten each maximal application spine;
4. encode levels in Q3 canonical form;
5. classify constant identities into Q4 references using the independently elaborated environments and M7 mapping; and
6. recompute direct and transitive dependency fields.

These operations define quotation format rather than source-to-output equivalence and need no M8 record. They may not unfold, reduce, simplify, synthesize, or discard a computational expression.

Before normalization, `dependencies` is the duplicate-free array of direct `member`, `source`, `external`, and `compiler` references in `type` and `value`, sorted by canonical JSON bytes. A compiler reference must be eliminated, translated, or present identically on both sides before correspondence equality.

Before normalization, `axiomDependencies` is the duplicate-free array of transitive axiom references, sorted by canonical JSON bytes. It is computed from the independently elaborated environment, not copied from the manifest. These quotation references are distinct from the manifest's raw name arrays, although both originate from the same environment traversal.

After every rule and Q7 proof marker has been applied, the verifier recomputes both arrays from the normalized `type` and `value`. References occurring only beneath a proof marker therefore disappear from literal semantic comparison; their raw axiom dependencies are checked separately under Q7. Computational dependencies and axiom dependencies outside erased proof nodes remain and participate in declaration and bundle equality.

## Q6. Rule-authorized normalization

For one M7 correspondence, the verifier loads its source and lowered pre-normalization bundles plus exactly the M8 records named by that correspondence. It then runs one total, deterministic, pairwise recursive normalization function.

At a mismatching source/lowered node pair, normalization may proceed only when exactly one most-specific listed occurrence and its `ruleId` authorize that shape change. The rule implementation validates its preconditions, recursively normalizes every retained component, and produces canonical replacement nodes. A rule may own descendants only as specified by that rule; overlapping independent occurrences are rejected.

Every listed occurrence must be consumed exactly once. An unused, duplicate, ambiguous, out-of-range, or inapplicable occurrence fails verification. A difference with no applicable occurrence also fails. Literal equality never needs a normalization record.

Normalizer rule set 1 contains one executable implementation for each L2 through L19 transformation that can appear in a successful manifest. L1 is the capture invariant and L20 is failure, so neither rewrites a quotation. The implementation order is structural rather than a free rewrite loop: outer bundle correspondences are handled first, then retained declarations, types, values, and subexpressions from left to right in canonical key and array order. A rule cannot expose a node for an unrelated later heuristic rewrite.

The normalizer does not perform beta, eta, iota, zeta, delta, proof, arithmetic, quotient, simplification, or definitional-equality reduction unless a specific lowering rule defines that exact representation change at a listed occurrence. In particular, it never unfolds an imported or source declaration merely to make quotations equal.

## Q7. Proof normalization

Before replacing a proof subterm, the verifier uses the original Lean expression and local context to infer its type independently on each side. Both types must be propositions, and their normalized quotations must be equal.

The verifier then computes each proof's raw transitive axiom dependencies and rejects unresolved metavariables, `sorryAx`, unsupported trusted primitives, or an output axiom dependency absent from the corresponding source proof. Using fewer proof axioms is permitted. Only after these checks does L16 replace that exact proof-typed node with `{"tag":"proof"}`; Q5 then recomputes the normalized declaration dependency arrays.

A computational parent is never replaced merely because it contains a proof. Thus `Decidable P`, equality-test dictionaries, subtypes, structures, and other data remain computational quotations; only an exact child whose independently inferred type is in `Prop` may become a proof marker.

## Q8. v0 normalization profile

The `v0` feature set exercises this closed subset of normalizer rule set 1:

1. Q5 maps ordinary one-to-one declaration identities through M7. An L2 occurrence is needed only for an additional private or generated-name representation change; v0 admits no compiler helper that needs unfolding.
2. L3 alpha-normalizes universe-parameter names by position after Q3 level canonicalization.
3. L4 verifies binder types, removes binder names and styles, and removes only the documented `optParam`, `autoParam`, `outParam`, and `semiOutParam` wrappers with their retained components checked.
4. Completed applications, projections, coercions, inserted arguments, and primitive literal payloads compare structurally after reference mapping; they authorize no v0 normalization record, search, or reduction.
5. L16 performs Q7 proof normalization.

Only L2, L3, L4, and L16 may appear in a v0 normalization record. Conversely, every v0 difference not removed by Q5 intrinsic encoding or ordinary M7 identity mapping must name one of those rules at its exact bundle path.

## Q9. Paths

An M8 `sourcePath` or `loweredPath` is an RFC 6901 pointer into the corresponding pre-normalization Q2 bundle. For example, the type of the first declaration begins at `/declarations/0/type`. Array indices are canonical decimal without leading zeroes.

Paths in M12 protected-region records are relative to the individual declaration quotation named by that region entry, so `/value/body` refers directly to that declaration's value. All paths are checked before normalization begins.

## Q10. Equality and fingerprints

Verification succeeds for a correspondence only when its normalized source and lowered Q2 bundles are literal canonical-JSON equals and all separate kernel, dependency, axiom, effect, grammar, and elaboration-audit checks pass.

The semantic fingerprint of an individual declaration is the M15 `explicit-lean/quotation/v1` hash of its fingerprint-normalized Q2 declaration object, not of a bundle wrapper. Fingerprint normalization is a single-sided deterministic operation: it applies Q5 intrinsic canonicalization in the one-member context defined by Q4, replaces universe-parameter names by positions under Q3, removes binder names and binder-style metadata, and replaces an independently type-checked `Prop` proof with the Q7 proof marker after computing its raw axiom dependencies. This last step performs only the independent checks available on that declaration; Q7's paired type-equality and output-axiom-subset checks remain mandatory for correspondence verification and do not alter the fingerprint.

Fingerprint normalization does not apply M8 records, remove binder wrapper constants, change bundle structure, or depend on which correspondence is being checked. Consequently, a declaration has exactly one semantic fingerprint even when it participates in multiple correspondences; representation changes authorized only by an M8 record may cause corresponding declarations to have different individual fingerprints.

A correspondence may additionally hash its normalized bundle for internal caching, but that digest is not a schema-version-1 manifest field. Correspondence success is determined by the bundle equality in the preceding paragraph, never by equality of M5 and M6 semantic fingerprints.

Quotation and normalizer implementations are identified by the header's `quotationFormat`, `normalizer.ruleSet`, normalizer executable fingerprint, and normalizer fingerprint. Changing an encoding, intrinsic canonicalization, rule implementation, or proof-checking behavior requires the corresponding version or executable identity to change.
