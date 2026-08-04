# Next steps

Status: working implementation plan.

This file tracks the work we currently intend to do. It is not a language or manifest specification and may change as implementation teaches us more. Normative behavior remains in [PLAN.md](PLAN.md), [CAPTURE.md](CAPTURE.md), [GRAMMAR.md](GRAMMAR.md), [LOWERING.md](LOWERING.md), [MANIFEST.md](MANIFEST.md), and [VERIFICATION.md](VERIFICATION.md).

The implementer owns the compiler's internal data structures and module layout. The work below specifies observable inputs, outputs, tests, and completion criteria rather than an internal IR.

## Immediate objective

Build the smallest end-to-end compiler that proves the architecture:

1. elaborate one source module exactly once;
2. capture the facts required for the v0 declarations below;
3. emit a standalone Explicit Lean module and schema-valid phase-one manifest;
4. compile and audit the generated module with pinned stock Lean;
5. verify normalized quotation equality for every declaration; and
6. reproduce identical generated and manifest bytes on a repeated run.

This thin slice comes before broad Lean or Mathlib inventory work. Corpus inventory becomes useful once the compiler can classify findings with executable positive and negative tests.

## v0 source feature set

The manifest identifier for this initial vertical slice is `v0`.

v0 uses the `closed-world` semantic boundary: generated modules are intended to be consumed with other generated dependencies, not substituted transparently for source modules by arbitrary Lean clients.

### Accepted modules and declarations

v0 accepts:

- one ordinary Lean module using pinned imports;
- namespace, section, `open`, variable, universe, and `set_option autoImplicit false` commands needed to elaborate accepted declarations;
- public, nonrecursive, nonmutual `def`, `abbrev`, `opaque`, and `theorem` declarations;
- explicit universe declarations and universe-polymorphic declarations;
- explicit, implicit, strict-implicit, and instance binders in source;
- term-style declaration bodies without tactic blocks; and
- stock-generated declarations and code-generation metadata intrinsic to the accepted declaration forms, when capture can correlate them and generated elaboration reproduces them.

The generated module retains legal imports conservatively under [L2](LOWERING.md#l2-declaration-inventory-names-namespaces-and-imports), emits `set_option autoImplicit false`, and lowers accepted declarations to the corresponding grammar-v1 declaration forms.

### Accepted completed terms

After source elaboration and metavariable instantiation, v0 accepts declaration types and values composed from Lean's ordinary completed expression forms:

- sorts, bound variables, and global constants;
- universe instantiation and function application;
- `forall`, lambda, and nonrecursive `let` expressions;
- projections and expression metadata whose semantic contents can be lowered;
- raw natural and string literals permitted by [G10](GRAMMAR.md#g10-primitive-literals); and
- imported proof terms and imported recursors used as ordinary fully explicit applications.

Source elaboration may resolve names and the admitted stock syntax and may insert universe arguments, implicit arguments, instance arguments, coercions, defaults, and proofs. v0 must print those recorded choices explicitly. It does not rerun the source mechanism in generated output.

The accepted source term syntax is deliberately small: identifiers, sorts, application, `@`, named arguments, `fun`, `forall`, function arrows, nonrecursive `let`, projections, parentheses, type ascription, `nat_lit`, and primitive strings. Only the stock parser, macros, and elaborators required by those forms are admitted.

Every accepted completed term must be closed relative to its declaration telescope, contain no metavariable, and be printable using the non-matching productions of [G8](GRAMMAR.md#g8-terms) together with [G9](GRAMMAR.md#g9-universes-and-sorts) and [G10](GRAMMAR.md#g10-primitive-literals), without reconstructing source-only structure.

### Rejected in v0

v0 reports a structured unsupported diagnostic for:

- inductive, structure, class, instance, axiom, and custom declaration commands;
- mutual or recursive declarations, equation-style declarations, `where`, and `let rec`;
- `match`, `nomatch`, pattern-matching lambdas, and source constructs whose result requires reconstruction as [G11](GRAMMAR.md#g11-canonical-matches-and-patterns) syntax;
- tactic blocks or tactic-generated local structure;
- `do` notation and mutable or imperative control flow;
- declaration attributes, deriving, initializers, registrations, custom commands, and persistent effects not intrinsic to an accepted declaration form;
- same-module generated auxiliaries that cannot yet be correlated and reproduced;
- user-defined syntax, notation, macros, and custom elaborators; and
- any completed expression, declaration kind, environment effect, or generated metadata outside the accepted set above.

An unsupported construct is a normal diagnosed result. It must not fall through to an approximate lowering.

## Implementation defaults

### Host and package

The initially supported host is Apple-silicon macOS (`arm64-apple-darwin` family). The manifest records the exact target reported by the pinned Lean executable. The implementation should remain portable Lean, but v0 makes no support claim for Intel macOS, Linux, or Windows until the complete suite passes there. The next portability target is x86-64 Linux CI.

The Lake package remains `explicitLean`. It will provide a Lean library named `ExplicitLean` and one executable named `explicit-lean`. Internal library modules and types remain implementer-owned.

### v0 command line and artifacts

The v0 interface has one command:

```text
explicit-lean compile \
  --package-root ROOT \
  --module MODULE \
  --source FILE \
  --output-root OUT \
  [--diagnostic-format human|json]
```

All four path or identity options are required. `ROOT` is the source package root, `FILE` must resolve beneath it, `MODULE` is the exact nonanonymous Lean source-module name, and `OUT` is the generated package root. V0 has no source-directory remapping: the lexical path of `FILE` relative to `ROOT` must be the slash-separated components of `MODULE` followed by `.lean`. Thus module `A.B` is read from `ROOT/A/B.lean`. Symlinks are resolved for access, but stable paths are slash-separated lexical paths relative to their declared root. Inputs that escape a root are rejected.

`ROOT` must be an already-resolved Lake package whose `lean-toolchain` and `lake-manifest.json` select the exact pinned Lean and Mathlib releases. The caller runs `explicit-lean` in the environment produced by `lake env` for that package, with every imported artifact already built. V0 neither downloads dependencies nor invokes a build. It validates the active Lean version and search path, rejects a missing or ambiguous import artifact, and records the exact artifact bytes it loads. Supporting Lake source directories, workspaces, or automatic dependency builds is post-v0 package integration.

The command always performs capture, admission, lowering, grammar checking, generated elaboration audit, quotation verification, and manifest validation. For source module `A.B`, it atomically publishes these artifact-convention-set-1 paths only after every stage succeeds:

```text
OUT/Explicit/A/B.lean
OUT/Explicit/A/B.manifest.ndjson
OUT/Explicit/A/B.provenance/   # only when sidecars exist
```

The generated module is `Explicit.A.B` under [L2 module mapping](LOWERING.md#l2-module-mapping). Temporary files use an implementation-owned directory outside the final artifact paths and never affect bytes or fingerprints. A failed run leaves any previously published successful artifacts unchanged.

Exit status is `0` for success, `2` for command-line or path errors, `3` for source parsing or elaboration failure, `4` for a diagnosed unsupported feature, `5` for lowering, grammar, audit, verification, or manifest failure, and `70` for an internal compiler error. If several diagnostics exist, the status with greatest severity in the order `70`, `5`, `4`, `3`, `2` wins.

### Diagnostics

`--diagnostic-format human` is the default and writes concise messages to standard error. `json` writes one [M1 canonical JSON](MANIFEST.md#m1-file-encoding-and-canonical-json) object per line to standard error with required `code`, `message`, `phase`, and `severity` fields and an optional [M2 source span](MANIFEST.md#source-spans). Phases are `cli`, `source`, `capture`, `admission`, `lowering`, `grammar`, `audit`, `verification`, `manifest`, or `internal`; severity is `error` in v0. Codes are stable uppercase identifiers matching `[A-Z][A-Z0-9-]*`.

Diagnostics are ordered by ranged before unranged, source file, start byte, end byte, phase order above, code, then message UTF-8 bytes. They contain package-relative paths and no stack addresses, timestamps, process IDs, or absolute paths. An internal error may append a noncanonical debugging trace only in human mode. Failure may emit diagnostics but never a successful manifest or partially published generated module.

## Work packages

### 1. Project and test skeleton — done

- Add the documented `ExplicitLean` library and `explicit-lean` executable targets to Lake.
- Establish fixture directories, golden-output tests, negative-diagnostic tests, and a command that runs the complete local test suite.
- Implement command-line parsing, exit statuses, diagnostic modes, and atomic artifact publication exactly as above.
- Validate the matching prebuilt Lake environment, direct module-to-file mapping, and import resolution contract.
- Confirm the complete skeleton on the supported Apple-silicon macOS host.

Exit criterion: a trivial executable and empty fixture suite build and run from a clean checkout with the pinned toolchain.

Status: complete. `lake build` produces the library, `explicit-lean`, and the
`explicit-lean-test` harness; `./test/run.sh` runs the complete suite. The
skeleton implements canonical JSON, diagnostics with the documented ordering and
both output formats, the exit-status severity rule, the module-to-file mapping
and root-escape checks, prebuilt-environment validation, and staged atomic
publication. `runStages` is still a placeholder that reports every module as
unsupported, so no case publishes artifacts yet; the compilation stages arrive in
work packages 2 through 8. Import-artifact resolution and recording is deferred
to the capture spike, which is where imports are first actually loaded.

### 2. Stock capture spike

- Invoke `Lean.Language.Lean.process` in-process for one module with asynchronous elaboration disabled.
- Walk completed command snapshots in source order.
- Extract source syntax and ranges, information-tree correlations, completed declaration values, and the per-command environment delta needed by the v0 fixtures.
- Confirm that compiler imports do not leak into the constructed source environment.
- Let the implementer choose and revise the internal representation while doing this work.

Probe fixtures must cover hidden universe and term arguments, imported instance synthesis, coercion insertion, stock arrow or binder expansion, a term proof, namespace and section context, and a simple generated declaration if stock Lean creates one.

Exit criterion: the spike inventories every declaration in each fixture, completes all captured expressions, correlates them with source, and produces an identical stable debug projection on repeated runs.

### 3. v0 admission and diagnostics

- Implement the v0 declaration and completed-expression checks.
- Reject unsupported source structure before lowering depends on it.
- Assign stable reason codes and source spans to negative results.
- Add explicit checks for unresolved metavariables, unclassified generated declarations, and persistent effects.

Exit criterion: every v0 feature has a positive fixture and every rejected category above has a negative fixture with a stable diagnostic.

### 4. Deterministic phase-one printer

- Emit conservative imports and the required module option.
- Print canonical universes, declaration telescopes, names, binders, applications, lets, projections, and primitive literals.
- Make all source-selected arguments explicit.
- Implement deterministic naming, declaration ordering, whitespace, escaping, and LF output for the v0 subset.

Exit criterion: every positive fixture emits grammar-v1 source that compiles with pinned stock Lean and contains no syntax forbidden for v0 output.

### 5. Grammar checker and elaboration audit

- Implement the grammar-v1 checker needed by the v0 output subset.
- Audit global resolution, application spines, metavariable absence, and forbidden synthesis during output elaboration.
- Distinguish permitted stock checking from source-meaning reconstruction.

Exit criterion: the checker accepts all generated fixtures, rejects targeted mutations, and the audit detects deliberately omitted explicit choices.

### 6. Minimal quotation verifier

- Quote source and generated v0 declarations into [quotation format 1](VERIFICATION.md); any working verifier representation remains implementer-owned.
- Implement only the normalization rules exercised by v0: binder-name and binder-style erasure, universe alpha-normalization, permitted wrapper handling, compiler-introduced name correspondence, and the specified proof checks.
- Compare declaration kind, universes, type, value, dependencies, and required generated declarations.

Exit criterion: corresponding fixtures compare equal, while mutations of a type, computational value, universe instantiation, dependency, or disallowed axiom fail.

### 7. Phase-one manifest

- Emit every schema-version-1 record required for a v0 module.
- Implement canonical NDJSON, record ordering, stable IDs, fingerprints, correspondence, validation records, and footer completeness checks.
- Record `artifactConventionSet: 1`, `captureArchitecture: 1`, and `sourceFeatureSet: "v0"`.

Exit criterion: manifests validate independently, fingerprint recomputation succeeds, and semantically relevant fixture mutations change the required fingerprints.

### 8. End-to-end command

- Connect capture, admission, lowering, grammar checking, output elaboration audit, quotation verification, and manifest generation.
- Write final artifacts only after all checks succeed.
- Run the compiler twice in clean temporary output directories and compare exact bytes.

Exit criterion: one command transforms every positive v0 fixture into independently valid artifacts; negative fixtures fail at the intended stage; repeated runs are byte-identical.

### 9. Post-v0 capture coverage

- Run focused probes for matches, equation compilation, structural recursion, well-founded recursion, tactics, deriving, and environment extensions.
- For each feature, record whether stock snapshots expose all required data.
- Add no Lean instrumentation unless a probe demonstrates a concrete missing artifact.
- If instrumentation is required, begin with the narrowest observer hook and differential-test its final environment and messages against stock Lean.

Exit criterion: each post-v0 feature has a documented stock-capture result and any proposed hook has a fixture demonstrating why it is necessary.

## After the v0 vertical slice

Expand support in this order, preserving an executable positive/negative feature matrix at every step:

1. broader literals, notation, defaults, coercions, and explicitness cases;
2. tactic-produced proof terms and proof sharing;
3. inductives, structures, classes, instances, attributes, deriving, and persistent effects;
4. canonical matches and equation-style declarations;
5. structural, mutual, and well-founded recursion;
6. representative Lean, Std, and Mathlib inventory followed by corpus-driven coverage; and
7. phase-two sharing, generic descriptions, typed abstraction, and compression.

Run the complete suite on x86-64 Linux before claiming that host as supported. Additional hosts require the same clean-build, semantic, diagnostic, and byte-determinism checks; cross-host bytes are not required to match because the exact target is fingerprinted.

Each expansion receives a new immutable `sourceFeatureSet` identifier once artifacts using the previous set exist. A feature is supported only when capture, lowering, diagnostics, grammar checking, semantic verification, manifest coverage, and repeat-build determinism all pass.

## v0 definition of done

v0 is complete when:

- the pinned project builds from a clean checkout;
- every accepted and rejected feature above has an automated fixture;
- the end-to-end command produces a standalone generated module and complete manifest;
- generated modules compile using the pinned stock Lean toolchain without source-module imports;
- the grammar checker and elaboration audit pass;
- normalized quotation equality passes for every corresponding declaration;
- targeted semantic and explicitness mutations fail verification;
- no unresolved metavariable, hole, unmatched declaration, unclassified effect, or undocumented normalization remains; and
- two clean runs with identical inputs produce byte-identical generated source and manifest files.
