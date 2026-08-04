# Lowering Source Lean

Status: normative design draft, lowering-rule set version 1.

This document defines how source Lean constructs that are not in [GRAMMAR.md](GRAMMAR.md) become Explicit Lean. [CAPTURE.md](CAPTURE.md) defines how their elaboration artifacts are obtained. [PLAN.md](PLAN.md) owns the correctness and architecture contract. [MANIFEST.md](MANIFEST.md) records every correspondence, transformation, erasure, and audit result. [VERIFICATION.md](VERIFICATION.md) executes the authorized quotation normalizations.

The stable identifiers `L1` through `L20` name normalization authorities. A manifest records the most specific applicable rule IDs; it does not use a broad rule to conceal an undocumented transformation.

## L1. Capture once, lower recorded choices

The source is parsed, macro-expanded, and elaborated exactly once under [C1](CAPTURE.md#c1-execution-model) in the pinned source environment. The capture layer retains:

- source syntax and spans before and after macro expansion;
- resolved names, universe instantiations, application spines, expected and inferred types, inserted coercions, synthesized dictionaries, defaults, and proofs;
- final match motives, discriminants, pattern matrices, branches, equality binders, and matcher metadata;
- equation-compiler and recursive-definition data before it is erased or repacked;
- completed tactic proof expressions and generated auxiliaries;
- every declaration added to the environment delta; and
- persistent environment-extension, code-generation, runtime, deriving, and registration effects.

Lowering prints these recorded choices. It must not rerun name resolution, type-class search, coercion search, tactic search, termination search, deriving, a macro, or a user elaborator to reconstruct output.

Capture records may contain implementation-specific Lean data, but every semantic choice needed by the standalone phase-one `.lean` module must be materialized in that module. The manifest is not an execution dependency.

## L2. Declaration inventory, names, namespaces, and imports

The source declaration delta is the ordered sequence of constants added after the imported environment, including constructors, recursors, projections, equation theorems, matcher declarations, tactic auxiliaries, and deriving output. Persistent effects that do not add constants are inventoried separately.

The printable inventory is distinct from that semantic inventory. A stock-generated source constant is not printed as a second declaration when elaborating its printed owner under the pinned toolchain is required to reproduce the corresponding lowered constant. Both constants still receive declaration records and correspondence. A generated constant that is neither reproducible this way nor independently expressible as a permitted declaration is unsupported. Stock-generated constants discovered while elaborating output are likewise recorded after elaboration; they are never appended to the source text as an order-dependent repair.

The lowerer preserves stable source declaration names and namespace structure. Phase one prints every ordinary global reference with its rooted canonical name. It discards source `open` commands and namespace aliases after recording their effect on source resolution.

Source section boundaries are not printed. Their variables and configuration have already been materialized in complete declaration telescopes and captured choices, so retaining an empty output section would add no meaning. Source-aligned section ranges may remain as provenance.

There are two stock-Lean necessities documented by G1:

- a reference to a member of the definition or inductive predeclaration group currently being elaborated uses the spelling recognized by the group elaborator; and
- a reference to a same-module private declaration uses its deterministic surface-private name while in scope.

The manifest maps either spelling to the exact canonical source and lowered declaration identities. No other contextual lookup is permitted.

Input imports become a deterministic ordered list of pinned base modules and previously generated dependencies. Grammar version 1 conservatively retains legal source imports in source order, replacing translated source dependencies with their generated modules and removing any import that would contain the declarations being reproduced. Import minimization is outside lowering-rule set 1; adding it requires a versioned optimization kind and manifest rule. A generated module never imports the source module or an artifact containing the declarations it reproduces.

### L2 module mapping

Artifact-convention set 1 maps a nonanonymous source module `M` to generated module `Explicit.M`. For example, `Mathlib.Data.List.Basic` maps to `Explicit.Mathlib.Data.List.Basic`; a source already beginning with `Explicit` simply receives another leading component. Under the generated output root, module components become directories, so source module `A.B` produces:

```text
Explicit/A/B.lean
Explicit/A/B.manifest.ndjson
```

Optional provenance sidecars for that module live beneath `Explicit/A/B.provenance/`. All three paths are slash-separated relative paths in stable artifacts. The generated module name changes no declaration namespace by itself: ordinary source declaration names and namespace structure remain as specified below.

An import of a translated source dependency uses its `Explicit.` mapping and is marked `generated` in M4. An untranslated pinned dependency retains its exact module name and is marked `base`. If a mapped name or artifact path is already occupied by a distinct pinned input or another mapped source module, compilation rejects the package rather than choosing an order-dependent alternate name.

### L2 canonical names

A meaningful, safely printable source declaration, namespace, universe, binder, field, constructor, or pattern name is retained when it creates no collision at its output scope. Escaped identifiers count as safely printable. Source `private` declarations retain their surface identifier and modifier; the manifest maps Lean's source and generated internal private identities.

When a local name must be synthesized, the printer chooses a role base—`u` for a universe, `inst` for an instance, `h` for a proof, `rec` for a recursive callback, and `x` otherwise—followed by the least positive decimal integer whose spelling is not forbidden at that binding site. Thus the first anonymous ordinary binder is `x1`. A retained name that collides is replaced using its identifier text as the base when possible and the role base otherwise. Forbidden names include every visible local, declaration name reserved by the current predeclaration group, Lean keyword, and name already selected in that binder sequence.

A compiler-introduced global helper is private and is placed below its source owner using the surface suffix `_explicit.<kind><n>`, where `kind` is one of `alias`, `aux`, `lift`, `match`, `pack`, `proof`, `share`, or `unpack`, and `n` is the least positive ordinal available for that owner and kind. For example, a first lifted helper owned by `Example.f` is surfaced as `Example.f._explicit.lift1`. The ordinal follows the captured lexical or candidate-enumeration order, never hash-map discovery. A helper shared by multiple owners uses the canonically first owner name. If the complete name collides with a retained source name, the ordinal increases until unused.

Phase two may propose a `generated-renaming` candidate for a private compiler-introduced helper. Its compact target is `_e<n>` in the helper's enclosing retained source namespace, where `n` is the least positive integer unused by a retained or already accepted generated name. Candidates are enumerated in current output-declaration order and accepted only by the deterministic budget algorithm in [PLAN.md](PLAN.md#deterministic-optimization-budget). Source and stock-generated declarations are never eligible.

Adding a new role base or generated-helper kind changes the artifact-convention set. Stock-generated declarations keep the names chosen by the pinned generated-module elaboration and are mapped to their source counterparts in the manifest; the lowerer does not rename them after elaboration.

### L2 declaration order

The printer forms atomic output nodes for individual declarations and for protected mutual, inductive, structure, or recursive groups. It adds an edge from node `A` to node `B` when a completed type or value in `B` directly references a same-module declaration emitted by `A`. Imported references create no node.

Permitted captured recursive components are collapsed to their required atomic group. Any remaining cycle, or a cycle that would merge incompatible protected groups, is unsupported. The printer then performs Kahn topological sorting. Among ready nodes it chooses the smallest key:

1. owning source-command ordinal;
2. origin rank: source-aligned, lowering, proof-sharing, then mining;
3. deterministic within-owner ordinal; and
4. canonical output name under M2.

A compiler-introduced node must have an owner; a module-level node uses an ordinal one greater than the last source command. Dependencies always precede consumers regardless of keys. Members of an atomic group retain captured source order unless the owning lowering rule specifies a canonical packing order. M5 source ordinals remain capture-delta order. M6 lowered ordinals are the actual post-elaboration generated-environment delta order, including stock auxiliaries, and therefore need not equal output-item ordinals.

After item ordering, the printer maintains a stack of retained namespace components. Before each item it closes components not shared with that item's namespace and opens the remaining components in order; after the last item it closes the stack. This longest-common-prefix procedure may reopen a namespace and uniquely determines G2 namespace blocks. A protected atomic group whose members cannot be printed under one namespace stack is unsupported.

Phase two may propose `namespace-factoring` candidates that reorder a contiguous set of dependency-independent, nonprotected nodes to increase shared namespace prefixes. A candidate's node order is canonical-name order, and it is accepted only by the deterministic budget algorithm. The same longest-common-prefix renderer then determines its exact byte savings.

Phase two may introduce a private explicit `abbrev` for a repeatedly used global or a typed local `let` for a repeated term. An alias carries complete universes, binders, type, and fully explicit body. The verifier unfolds only compiler-introduced aliases recorded under L2.

## L3. Universes and sorts

The lowerer reads the complete ordered universe-parameter list from each elaborated declaration. It preserves source names when unambiguous and otherwise assigns deterministic fresh names. Explicitly declared but unused parameters remain.

Every completed polymorphic global or same-module-private reference prints all universe arguments in the referenced declaration's environment order. Monomorphic references print no empty instantiation. A reference to a member of the definition or inductive group currently being elaborated is Lean-local syntax and cannot carry an explicit universe suffix; its universe vector is fixed by the surrounding group and checked against capture. Universe metavariables must be fully assigned before lowering.

Elaborated `Level` values are converted by G9's pinned `Lean.Level.normalize` and canonical reconstruction: successors are combined, `max` is flattened/deduplicated/sorted, neutral operands are removed, and surviving `imax` argument order is retained. The verifier applies the same level normalization and alpha-normalizes bound universe names; it never equates distinct instantiations.

Sorts use the canonical G9 spellings `Prop`, `Type u`, and `Sort u`.

## L4. Declaration telescopes and binder annotations

The complete source parameter telescope comes from the elaborated declaration, in environment order. This includes section variables, automatic implicit parameters, and source explicit, implicit, strict-implicit, instance, optional, or automatic parameters. Each becomes a named, typed, ordinary explicit binder.

Meaningful source and section names are retained. Anonymous, inaccessible, duplicate, or conflicting names receive deterministic fresh names such as `x1` or `inst1`, and all dependent types and bodies are renamed consistently.

Binder wrappers are lowered as follows:

- `{x : A}`, `⦃x : A⦄`, and `[x : A]` become `(x : A)`;
- `(x : A := default)` and its `optParam` wrapper become `(x : A)`;
- an `autoParam` becomes `(x : A)` and its tactic syntax disappears; and
- `outParam` and `semiOutParam` wrappers disappear after dictionary uses are explicit.

Every call prints the exact default or automatic value selected during source elaboration. The verifier may erase only the listed wrappers and binder-style metadata, after comparing their retained types, defaults, tactics or proof provenance, and replacement arguments.

Every declaration states its complete elaborated result. A source-inferred binder type or result is printed explicitly. The lowerer retains the boundary between declaration parameters and a function-valued result; it does not move arbitrary leading `forall` binders into the header. L13 is the equation-style exception.

## L5. Inductives, structures, applications, and projections

An ordinary source inductive retains its parameters, indices, constructors, recursive occurrences, result sorts, and mutual grouping. Constructor arguments and results lower recursively, and the manifest correlates the stock constructor, recursor, matcher, and generated declarations on both sides. Inductive and mutual-inductive blocks are protected regions.

An ordinary source structure retains its parameters, result sort, meaningful constructor and field names, dependent field order, defaults, and `extends` parent order. Every parent is printed as the exact resolved explicit application, including a meaningful parent-projection name. Capture records the flattened parent layout and the generated constructor, recursor, field projections, and parent projections for verification. Structure declarations are protected regions. Field defaults remain allowed terms, but no generated construction relies on default insertion.

The lowerer recursively prints the captured elaborated expression application spine:

- the head constant has its exact resolved identity and universe instantiation;
- `@` exposes stock implicit or instance binders when required by G8;
- every captured argument appears in order; and
- no new argument is invented after the captured spine ends.

This rule naturally preserves intentional partial application: hidden arguments already selected by elaboration are visible, while later unapplied function arguments remain unapplied.

Every inserted or requested coercion becomes the exact coercion-function application selected in the source, with its universes, types, dictionaries, receiver, and proofs explicit. Field notation, generalized dot notation, numeric projections, and leading-dot constructors become recorded fully named function, projection, or constructor applications.

Anonymous constructors and structure instances become fully named constructor applications supplying every field. A structure update evaluates its source expression exactly once using a typed `let`, then calls the constructor with recorded projections for retained fields and lowered replacement terms for changed fields.

## L6. Literals and elementary notation

There are two compact output leaves. A raw natural payload becomes `nat_lit n`; a primitive string becomes the canonical G10 quoted string. Every other literal exposes its source elaboration:

- a numeral at type `A` becomes the captured fully explicit `_root_.OfNat.ofNat` application to `A`, `nat_lit n`, and its `OfNat` dictionary;
- a scientific literal becomes the captured `_root_.OfScientific.ofScientific` application with raw-natural payloads, a fully qualified Boolean constructor, and dictionary;
- a negative literal additionally applies the captured `_root_.Neg.neg` operation and dictionary;
- a character literal becomes the captured character-construction function applied to the raw natural Unicode scalar;
- interpolation becomes the captured append and conversion applications, with every conversion dictionary explicit and only constant string segments retained as primitive strings;
- list, array, tuple, unit, Boolean, and similar syntax becomes the recorded fully named constructors or builders; and
- placeholder sections such as `(· + ·)` become typed lambdas.

Application conveniences such as `<|` and `|>` disappear after their association is recorded. No literal or notation elaborator runs in the output.

## L7. Operators, indexing, and conditionals

Every overloaded or notation-driven operator becomes the exact captured function application with all universes, types, dictionaries, operands, inserted arguments, and proofs. This includes arithmetic, comparisons, Boolean and monadic operators, equality, composition, and user-defined notation.

An indexing form exposes the selected `GetElem` operation, dictionary, index, collection, exact bounds proof, and any captured fallback behavior. The output never resynthesizes a bounds proof.

Conditional syntax lowers as follows:

- a nondependent `if` becomes the captured fully explicit `_root_.ite`, including its exact `Decidable` value;
- a dependent `if h : p` becomes `_root_.dite` with typed branch lambdas for `h : p` and `h : _root_.Not p`;
- a Boolean `bif` becomes the captured `_root_.cond`; and
- `if let` and `matches` become canonical matches under L11.

A `Decidable` is computational data. Its constructor and non-proof fields remain exact; proof irrelevance does not erase the dictionary as a whole.

## L8. Local definitions and source configuration forms

A nonrecursive source local function becomes a typed single-name `let` whose value is a fully typed lambda. For example, `let g (x : A) : B := v; body` becomes `let g : A → B := fun (x : A) => v; body` after recursive lowering.

Source `let` and `have` options such as `+nondep`, `+zeta`, `+usedOnly`, `+postponeValue`, and `+generalize` never appear in output. Lowering retains the elaborated result: removed or inlined bindings stay removed or inlined, while generalization and equality effects become explicit lets, lambdas, equality terms, or matches. The verifier may erase Lean's `nondep` let bit only after type, value, and body agree.

A source `have h : P := p; q` is an ordinary typed `let`. `show P from p` is an explicit type ascription.

## L9. Pattern lambdas, pattern lets, `where`, and `let rec`

A pattern-matching lambda becomes one typed explicit lambda per argument followed by a canonical match. Argument types, motive, discriminants, compiled pattern matrix, and branch functions come from capture.

A pattern `let` becomes a canonical match on its value, including when it is source-irrefutable. Equality-binding variants use the named-discriminant transformation in L12. If the pattern is an empty elimination, lowering uses the type-ascribed G8 `nomatch` form because G11 requires at least one match branch.

`where` and `let rec` are source-only. Their local declarations are lifted to permitted top-level declarations:

- every captured local and transitive dependency needed by its type becomes an explicit parameter, ordered by the captured local context;
- a source-named, source-addressable `where` helper keeps its stable qualified name and visibility;
- a lexically local helper gets a deterministic private name derived from its containing declaration and lexical path;
- acyclic helpers appear in dependency order before users; and
- each recursive strongly connected component becomes a singleton or mutual group processed by L14 or L15.

If a helper is mutually recursive with its enclosing declaration, every member occurs in the same explicit group. Calls to a completed lifted helper supply all captured universes, dictionaries, locals, and ordinary arguments; calls within its current recursive group use L14's fixed-universe exception. The manifest records source-local identity, lift name, captures and ordering, dependency edges, recursive component, and termination strategy.

## L10. `do`, mutable control flow, macros, and elaborators

`do` and mutable-do syntax become the fully elaborated functional expansion. Bindings and sequencing use the exact captured `Bind.bind`, `Pure.pure`, `Seq`, `Alternative`, or other operations. Returned values flow through typed lambdas; dictionaries and laziness thunks are explicit; operation and evaluation order are unchanged.

The same rule applies to monadic pattern bindings, `return`, `for`, `while`, `break`, `continue`, early return, exceptions and recovery, `let mut`, and assignment. Captured closures, immutable state passing, control-state constructors, matches, join points, and helpers are recursively lowered. Introduced local recursion follows L9, L14, and L15. No monad or applicative law is used to simplify the result.

Source macros, notation extensions, and custom elaborators may run only in the pinned source environment. Phase one recursively lowers the declarations and terms they produced and records provenance. If the final elaborated result contains a primitive or transient choice not representable by [GRAMMAR.md](GRAMMAR.md), lowering rejects it under L20 instead of retaining or rerunning the extension.

## L11. Canonical pattern matching

Every nonempty source match becomes a G11 canonical match. Capture occurs after term elaboration and before recursive-definition processing can discard or alter source-aligned match data. It records the final motive, discriminants, pattern matrix, branch functions, equality binders, generated matcher, and matcher metadata.

The lowerer prints:

- an explicit dependent motive with one typed binder per final discriminant;
- every final discriminant, including indices or contextual values introduced by refinement or generalization;
- one branch per compiled alternative, in captured order;
- canonical constructor patterns with every surface-expressible field; and
- recursively lowered branch bodies.

Literal, notation, structure, macro, custom, default, ellipsis, and leading-dot patterns expand to the captured constructor pattern. Shared-right-hand-side alternatives may initially duplicate their bodies.

Pattern syntax cannot state constructor universe arguments, datatype parameters, indices, or pattern-variable types. These are the narrow G11 exceptions and must be determined uniquely by typed discriminants, motive, and constructor signature. The audit compares the choices.

An elimination with no alternatives cannot be printed as a stock Lean `match`, and a direct empty recursor is rejected by stock code generation for some computable definitions. It becomes a G8 `nomatch` with an explicit result-type ascription. The lowerer prints every discriminant and lowers the ascribed type; the audit compares the motive and empty pattern matrix captured from source elaboration. Source `nomatch` uses this form. Source `nofun` first becomes typed explicit lambdas and then the corresponding ascribed empty elimination.

Generated matcher applications and `MatcherInfo` are capture and verification artifacts, not output fallbacks. Failure to reconstruct the canonical match or audited empty elimination is unsupported.

## L12. Named discriminants, named patterns, and generalization

Lean does not permit a named discriminant together with the explicit motive required by G11. A source `match h : e with ...` therefore becomes a canonical match returning a function that accepts the captured `Eq` or `HEq` proof. Every branch binds the proof explicitly, and the whole match is applied to the fully explicit captured reflexivity proof. Multiple named discriminants produce multiple proof parameters and arguments.

A named pattern `whole@p` becomes `p` plus a typed local `let` in the branch that reconstructs `whole` using the fully explicit constructor application. A named-pattern equality similarly becomes the recorded explicit equality proof.

Source `generalizing := true` does not survive. The generalized values already occur among captured discriminants and in the explicit motive. Plain contextual generalization is likewise represented by those final captured discriminants. Output contains no `generalizing` option.

Recompilation must reproduce the captured motive, discriminants, pattern matrix, branch bodies, and matcher correspondence after the documented equality transformation.

## L13. Equation-style declarations

Equation-style declarations are source-only. Equation arguments become explicitly named and typed declaration parameters, while parameters recorded by the equation compiler as fixed remain fixed header parameters. The body is a canonical match over the final equation discriminants.

The motive, discriminants, matrix, branches, recursive calls, and generated equation declarations come from captured equation compilation. Multiple equation arguments become multiple parameters and match discriminants. Every component is then recursively lowered under the other rules.

The source equation clauses, their match expansion, fixed/varying parameter decision, and auxiliary correspondence are protected manifest regions. Phase two may share repeated bodies but may not reintroduce equation syntax.

## L14. Structural recursion

A structurally recursive source declaration retains its declaration kind, explicit header, canonical match body, visible recursive calls, and a mandatory `termination_by structural x` clause. If the source omitted termination syntax, the captured parameter actually selected by Lean is printed.

Every member of a mutual structural group names its own decreasing parameter. Partial annotation is forbidden. The group is exactly the captured recursive strongly connected component and preserves source grouping, fixed parameters, constructor branches, and recursive calls.

Each recursive call is an ordinary fully explicit application using the G1 predeclaration-name exception. Its universes are fixed by the surrounding group because stock syntax cannot attach a universe suffix to the recursive local; it supplies every type argument, fixed argument, dictionary, captured local, and varying argument present in source elaboration. Stock Lean must accept the recursive argument as a subterm of the named parameter under the emitted matches.

No candidate search, `termination_by?`, inferred output annotation, `decreasing_by`, tactic, measure search, relation search, or instance synthesis is permitted. Recompilation audits that Lean used structural recursion on exactly the recorded parameter. If that presentation fails, the source declaration may use L15 only when source capture recorded well-founded recursion; the compiler does not silently change strategies.

## L15. Well-founded recursion

Source measure syntax and `decreasing_by` are not output forms. For every source definition elaborated by well-founded recursion, capture retains:

- the elaborated measure and its argument and result types;
- the exact `WellFoundedRelation` dictionary selected for the result type;
- the induced relation on varying arguments, including `invImage` construction;
- the explicit well-foundedness proof;
- the decrease proof for every recursive call; and
- fixed-parameter, packing, unpacking, and mutual-recursion correspondence.

Phase one emits an ordinary nonrecursive definition whose body is a fully explicit application of `_root_.WellFounded.fix`. Schematically:

```lean
def f (x : A) : B x :=
  @_root_.WellFounded.fix.{u, v}
    A
    (fun (x : A) => B x)
    relation
    wellFoundedProof
    (fun (x : A)
         (recur : (y : A) → relation y x → B y) =>
      bodyWithExplicitCallbacks)
    x
```

The actual output applies every grammar and lowering rule. A source call `f y` becomes the local callback applied to `y` and its captured decrease proof. The measure, relation, branch structure, and meaningful local names remain recognizable.

Mutual well-founded recursion lowers to one explicit fixpoint over a deterministic sum or dependent-sum packing plus nonrecursive wrappers with the original names and types. The manifest records tags, packed arguments, wrappers, callbacks, proofs, and generated equation correspondence. No ordering, relation, packing, or proof is inferred in output.

Verification uses normalized quotation equality under the recorded fixpoint and packing correspondence. Phase two may factor repeated explicit relation or packing structure but may not reintroduce termination elaboration.

## L16. Proof terms and proof sharing

A proof is lowered as an ordinary Explicit Lean term. Common source forms become:

- `rfl`: the captured fully explicit `_root_.Eq.refl` or other reflexivity term;
- anonymous constructors or the `constructor` tactic: fully named constructor applications;
- `show`: type ascription;
- `have`: typed `let`;
- `calc`: the captured relation, transitivity, congruence, and proof applications;
- rewriting: captured equality eliminators, congruence applications, and proof arguments; and
- case analysis or induction: a canonical source-term match, or the fully explicit recursor application constructed by a tactic.

Tactics run only while elaborating source. Phase one requires a closed, fully assigned completed proof expression, captures generated auxiliaries, and lowers it recursively. It never reruns `simp`, `omega`, `aesop`, `grind`, `decide`, induction, rewriting, or another tactic in output. A tactic auxiliary becomes a permitted declaration with deterministic name and provenance.

An unresolved metavariable, incomplete goal, `sorry`, `admit`, or `sorryAx` dependency rejects the source proof. When the manifest configuration permits it, a source proof already using an imported trusted-computation axiom such as `Lean.trustCompiler` may retain that explicit dependency and is marked nonportable. The compiler never introduces such a dependency.

Phase one retains tactic auxiliaries and may introduce deterministic typed local lets or private helper theorems for repeated proof-DAG nodes that would otherwise make output impractical. Each helper expansion is recorded and checked. Phase two may name propositions, extract subproofs, group transports, or use source tactic traces as hints; correctness still comes solely from compilation, axiom checks, and normalized quotation equality.

Proof-irrelevance normalization follows the checks in [Q7](VERIFICATION.md#q7-proof-normalization). It never erases a computational proof-carrying value.

## L17. Classes and instances

A structure-like `class` becomes an ordinary `structure`; a class inductive becomes an ordinary `inductive`. Class methods, laws, defaults, constructor data, and meaningful names are preserved. Instance-implicit self and parent parameters become explicit dictionary parameters. Parent dictionaries and projections are explicit, and `outParam` and `semiOutParam` wrappers disappear under L4.

A class abbrev is expanded to an explicit ordinary dictionary representation captured from its elaborated target. If the representation cannot be expressed as permitted structures, inductives, definitions, and applications with a documented normalized correspondence, the declaration is unsupported.

An `instance` declaration becomes a named `def` containing the same dictionary value without registration. Anonymous instances receive deterministic names. Every use passes the exact recorded dictionary definition or parameter explicitly.

The verifier accounts for class flags, binder-style changes, instance registration, parent projections, and generated dictionary helpers only through the specific recorded L17 correspondence. Dictionary values themselves remain computationally exact.

## L18. Deriving

Neither a deriving clause nor command appears in output. Source deriving runs in the pinned environment. Phase one captures every generated declaration as part of the source oracle and lowers it independently to ordinary permitted declarations. This explicit expansion is a successful lowering; phase one need not reconstruct the hook.

Phase two may recognize repeated deriving output and replace it with an ordinary portable datatype-description library. A provisional `DataDescription` and its interpreters may describe equality, comparison, hashing, representation, size, and laws. The library must itself be Explicit Lean: no metaprogramming, deriving, instance search, or tactics. It preserves the original datatype and receives field capabilities as explicit arguments.

An interpreter representation is accepted only when unfolding compiler-introduced library definitions under the recorded normalization reproduces phase-one declarations. Failure to mine a description leaves the explicit expansion unchanged.

As an optional research aid, capture may instrument a deriving hook's environment reads, resolved dependencies, generated syntax, and delta. Such traces are hints recorded in the manifest, never executable output or correctness evidence.

## L19. Modifiers, attributes, registrations, and runtime metadata

Grammar version 1 retains only `private`, `public` when nondefault, and `protected`. `nonrec` is resolved into exact reference identities and erased. Documentation, attributes, and every other modifier are initially captured and assigned a disposition:

- `erase`: the effect is irrelevant under the chosen closed-world output contract and has a verifier rule;
- `lower`: ordinary declarations or terms reproduce the effect;
- `preserve`: requires a future grammar-version addition; or
- `reject`: the source module is outside the current supported matrix.

Attributes that generate declarations are handled by lowering their captured delta rather than rerunning the attribute. Search registrations such as instance, simp, and coercion metadata may be erased only after every generated dependency has made the selected result explicit and the chosen semantic boundary permits erasure.

`noncomputable`, `partial`, `unsafe`, `meta`, `extern`, `implemented_by`, foreign-function data, code-generation directives, and runtime attributes require explicit feature-matrix dispositions. A report of lost runtime or persistent metadata is not by itself a correctness proof. Until a disposition and verifier rule are committed, the occurrence is rejected.

Every erased or translated effect has a manifest environment-effect record and its authorizing L19 subtype. The verifier separately compares kernel declarations, generated declaration sets, persistent extensions, and code/runtime metadata according to the selected semantic boundary.

## L20. Unsupported lowering

Lowering rejects a source module, with a stable diagnostic and source span when available, if any of the following holds:

- source elaboration fails, leaves a metavariable, or uses `sorryAx`;
- required transient elaboration information was not captured;
- an expression, declaration, primitive, environment effect, or runtime behavior has no permitted representation and committed disposition;
- a protected source region cannot be reconstructed;
- emitted syntax fails the grammar or elaboration audit;
- structural recursion is not accepted on the captured parameter;
- a canonical match or audited empty elimination cannot reproduce captured matching data;
- a generated declaration or dependency is unmatched;
- the output adds an axiom or trusted primitive; or
- normalized quotation equality requires an undocumented rewrite.

Diagnostics distinguish unsupported source features from compiler bugs and verifier failures. An unfamiliar source syntax whose completed elaborated result is wholly representable may use the general expansion rules above. “Expanded fallback” never means printing a matcher artifact, kernel encoding, macro, or arbitrary opaque declaration merely to avoid rejection.
