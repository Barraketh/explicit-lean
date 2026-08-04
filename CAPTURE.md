# Capturing Source Lean

Status: normative design draft, capture architecture version 1.

This document defines how the compiler observes one source elaboration and which source-correlated facts it makes available to [LOWERING.md](LOWERING.md). [PLAN.md](PLAN.md) owns the overall architecture and correctness contract. [MANIFEST.md](MANIFEST.md) owns the stable serialized projection of capture data. [VERIFICATION.md](VERIFICATION.md) owns the verifier quotation derived from completed declarations. [GRAMMAR.md](GRAMMAR.md) owns the generated language and its separate elaboration audit.

The capture implementation is an observer of source elaboration. It does not define source semantics, and no capture-only component is an execution dependency of a generated module.

## C1. Execution model

Capture is implemented as a Lean executable linked against the pinned Lean libraries. It invokes Lean in-process; it is not an external parser, a trace-log scraper, or an `.olean` decompiler.

Architecture version 1 processes one source module per operating-system process. It constructs the source environment from that module's header and pinned import artifacts, then invokes `Lean.Language.Lean.process` with asynchronous elaboration disabled. Parallelism may occur across module processes, but commands within one module are captured in source order.

The frontend parses, macro-expands, and elaborates the source exactly once. Capture never reruns a macro, command elaborator, term elaborator, tactic, instance search, coercion search, equation compiler, deriving handler, or termination procedure to recover missing information. Re-elaboration of the generated module is a later, independent audit and is not source capture.

The capture executable must not leak its own compile-time imports, namespaces, options, declarations, syntax, attributes, or instances into the constructed source environment. Source initializers and plugins are loaded only as required by the source module's pinned imports and configuration.

## C2. Command snapshots

The driver waits for every frontend snapshot to finish and visits top-level command snapshots in source order. For each command it retains, until extraction completes:

- the parsed `Syntax` and exact source range;
- its `InfoTree`, including nested command, term, tactic, macro-expansion, and custom information;
- the command state immediately before and after the command;
- the environment immediately before and after the command;
- the active options, namespace, open declarations, and command scopes; and
- messages and the command's success or failure status.

Adjacent snapshots define a command-local delta. The environment before the first non-header command is also retained as the imported baseline. The module delta is the union of command-local deltas after that baseline, with command and within-command encounter ordinals preserved.

A frontend error terminates capture for the module. Partial information trees may be used to improve the diagnostic, but they never authorize partial generated output.

## C3. Extraction boundary

The implementer owns the internal data structures, ownership model, and module layout used between capture and lowering. This architecture does not prescribe an IR or Lean type hierarchy.

The implementation must nevertheless extract every fact required by the lowering, manifest, diagnostic, fingerprint, and verification contracts before its frontend context is discarded. Raw `Environment`, `InfoTree`, `Expr`, `LocalContext`, and `MetavarContext` values may be retained internally for as long as useful, but they are not serialized directly.

Pointer identity, task identity, free-variable IDs, metavariable IDs, macro-scope IDs, and internal map order are not stable identities. Any such values that reach a stable artifact must first be replaced by the names, spans, ordering, IDs, and fingerprints specified by [MANIFEST.md](MANIFEST.md).

## C4. Source correlation and completed expressions

Information trees provide correlation, not final declaration authority:

- `TermInfo` relates syntax to an elaborated expression, expected type, and local context;
- its enclosing command context supplies the metavariable context needed to instantiate that expression;
- `MacroExpansionInfo` relates pre-expansion syntax to expanded syntax;
- match elaboration's saved pattern information relates pattern syntax to elaborated constructor patterns; and
- `TacticInfo` supplies tactic provenance and goal-state correlation, while the completed proof expression comes from the containing elaborated term or final declaration.

Extraction runs `instantiateMVars` in the recorded context before that context is discarded. A completed captured expression may contain free variables declared by its captured local context, but it contains no metavariables. An unresolved metavariable is a capture failure, not a hole to be printed or solved later.

The final `ConstantInfo` in the post-command environment is the semantic authority for a completed declaration's kind, universe parameters, type, and value. Information-tree expressions explain how source regions contributed to it. When a transient expression and the completed declaration disagree after the documented Lean processing, capture retains both with their relationship; it never silently substitutes one for the other.

Source spans are half-open UTF-8 byte ranges into the exact input bytes, as specified by M2. Synthetic syntax without a meaningful range is attached to the smallest enclosing ranged owner and a deterministic synthetic ordinal.

Macro expansion chains are retained in order. Capture may discard expansion detail that has no lowering, diagnostic, provenance, fingerprint, or audit use, but it must retain every resolved choice used by lowering.

## C5. Declaration delta

For each successful command, capture enumerates constants present after the command and absent before it. The pinned implementation uses Lean's deterministic new-constant traversal rather than general hash-map iteration. Each new constant is read back from the post-command environment and classified as a source declaration, member of a source group, or generated auxiliary.

The delta includes constructors, recursors, projections, matchers, equation theorems, tactic auxiliaries, deriving output, compiler-generated helpers, and private declarations. A declaration is not ignored merely because it lacks a direct source span.

Capture records dependencies from completed types and values by exact `Name` and universe instantiation. It also records group and provenance metadata supplied by syntax, information trees, or known environment extensions. Final generated declaration ordering is owned by the [L2 declaration-order algorithm](LOWERING.md#l2-declaration-order); capture preserves enough encounter and dependency information to apply that algorithm without consulting source elaboration again.

## C6. Persistent effects and scopes

Declarations alone do not describe all source behavior. Capture therefore maintains a versioned registry of effect extractors. An extractor has:

- a stable extractor and effect-kind identifier;
- a read function for one known Lean environment extension or code-generation registry;
- a canonical comparison and projection function;
- a list of source features for which it is required; and
- the permitted `preserve`, `lower`, `erase`, or `reject` dispositions.

The driver applies the relevant extractors to the pre-command and post-command environments and records the normalized delta. Attribute registrations, instance and coercion registrations, deriving state, code-generation metadata, runtime initialization, and other persistent extensions require an extractor before the corresponding source feature can be accepted.

Namespace, `open`, section, and option changes live in command scopes rather than the persistent environment. Their pre-command and post-command states are captured so that source name resolution and configuration are auditable, even when those commands disappear from generated output.

The versioned source-feature matrix in [next-steps.md](next-steps.md) names every command, modifier, attribute, plugin facility, and custom elaborator it admits and the extractors or capture events required for it. If an admitted construct may cause a semantic effect that the registry cannot classify, the module is unsupported. A successful environment diff is not evidence that an unknown effect is irrelevant.

## C7. Instrumentation escape hatch

The default backend uses only the pinned stock frontend, command snapshots, information trees, completed environments, and public extension queries. No instrumented Lean build is required for features whose fixtures are completely represented by those facilities.

When a coverage probe demonstrates that required transient data is unavailable, the implementation may add a narrow observer hook to the exact pinned Lean source. A hook must:

- record a typed event at the point where Lean has made the relevant choice;
- preserve rollback and command ownership, so abandoned elaboration branches emit no committed event;
- perform no search, elaboration, environment mutation visible to source code, or choice modification;
- avoid parsing human-readable traces or pretty-printer output;
- be disabled when capture is not active; and
- be covered by differential tests showing that stock and instrumented elaboration produce identical final environments and messages for the fixture corpus.

Instrumentation is part of the compiler implementation and therefore of its executable and compiler fingerprints. It does not change the pinned stock toolchain used to compile and audit generated output. Adding a hook does not relax the elaborate-once rule.

Lowering consumes one capture interface regardless of whether a field came from a public snapshot or an observer hook. A missing event yields a structured unsupported diagnostic; lowering never probes Lean internals a second time.

## C8. Isolation and determinism

Architecture version 1 deliberately favors isolation over throughput:

- one source module is captured per process;
- intra-module asynchronous elaboration is disabled;
- all frontend tasks are awaited before extraction;
- source commands and capture events receive deterministic ordinals;
- absolute paths are converted to package-relative slash-separated paths before stable projection; and
- timestamps, process IDs, thread schedules, addresses, random values, and host map iteration never enter output or fingerprints.

The build fingerprint includes the exact source bytes, import artifacts, pinned toolchain, compiler and instrumentation identity, source-feature matrix, semantic configuration, and every captured environment read that can influence elaboration or lowering. Clean and repeated capture with identical inputs must yield byte-identical stable capture projections, generated source, and manifests.

A long-lived capture daemon, intra-module parallel capture, or incremental snapshot reuse is a later optimization. It must reproduce the architecture-version-1 artifacts byte for byte before it can replace the isolated path.

## C9. Failure classes

Capture reports a structured failure before lowering when any of the following occurs:

- source parsing, macro expansion, elaboration, kernel checking, or command execution fails;
- an elaborated expression retains an unresolved metavariable after contextual instantiation;
- a new declaration cannot be inventoried or assigned to a deterministic owner;
- required source-to-expression, match, equation, recursion, or generated-declaration correlation is absent or contradictory;
- a persistent effect lacks a registered extractor or permitted disposition;
- a required observer event is absent, duplicated, abandoned, or associated with the wrong command; or
- capture observes nondeterministic ordering or unstable identity in data that affects output.

Diagnostics identify the owning command or declaration, source span when available, capture component, required feature, and stable reason code. Raw internal IDs and pretty-printed expressions may appear only as supplemental debugging information, not as reason-code identity.

## C10. Coverage probes and acceptance

Before relying on stock capture for a feature, a probe fixture must demonstrate all artifacts needed by its lowering rule. The working probe sequence is maintained in [next-steps.md](next-steps.md).

For every fixture, the test inventories the complete environment delta and required persistent effects, checks that all captured expressions are completed, validates source correlations, and repeats the run to test determinism. Instrumented fixtures additionally compare their final environment and messages with stock Lean.

A feature enters a supported source-feature set only after its probe passes and its required capture facts, effect extractors, diagnostics, and lowering consumer are covered by tests.
