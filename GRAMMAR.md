# Explicit Lean Grammar

Status: normative design draft, grammar version 1.

This document defines the surface language that a generated `.lean` module may contain. [PLAN.md](PLAN.md) defines the project and correctness contract. [LOWERING.md](LOWERING.md) defines how source constructs reach this language. [MANIFEST.md](MANIFEST.md) defines the accompanying audit artifact. [VERIFICATION.md](VERIFICATION.md) defines semantic comparison after elaboration.

Explicit Lean membership has two parts:

1. the source text must satisfy the grammar and static restrictions in this document; and
2. elaborating it with the pinned stock Lean toolchain must satisfy the audit in [Elaboration audit](#elaboration-audit).

A compiler implementation must provide a checker for both parts. Successful Lean elaboration by itself is not a membership test.

## G1. Notation and lexical layer

The productions below describe syntax trees, not a replacement lexer. `ident`, escaped identifiers, module names, whitespace, and ordinary comments are recognized by the pinned Lean lexer. Documentation comments are declaration syntax and are rejected. The generated printer emits UTF-8 with LF line endings, no byte-order mark, no tabs, no comments, and no trailing whitespace. A checker may accept arbitrary insignificant whitespace and ordinary comments, but the compiler never generates comments.

The EBNF conventions are:

- `x?` means zero or one `x`;
- `x*` means zero or more `x`;
- `x+` means one or more `x`;
- parentheses group grammar expressions; and
- quoted text is a literal token.

A `localName` is a Lean identifier chosen so that it does not shadow or collide with another name visible at that binding site. A `declName` or namespace component is a Lean identifier. If the retained source name is not safely printable as an ordinary identifier, the printer uses Lean's escaped-identifier token. Anonymous, inaccessible, duplicate, numeric, or conflicting internal names are replaced deterministically and recorded in the manifest.

### G1 canonical layout

Artifact-convention set 1 uses a deterministic grouped document renderer with a maximum width of 100 Unicode scalar columns and two spaces per nesting level. A hard line always breaks. A soft line renders as one ASCII space when its complete enclosing group fits in the remaining columns through the next hard line; otherwise every soft line in that group breaks. Fitting and rendering scan left to right, never consult terminal width or locale, and permit an indivisible token to exceed 100 columns.

Imports occupy consecutive single lines. When imports exist, exactly one empty line follows the import block. Exactly one empty line follows the `autoImplicitGuard` when an item follows it, and exactly one empty line separates sibling items. A namespace places its opening and closing commands on their own lines and nests its items by one level. Inductive constructors, structure fields, mutual members, and match alternatives each begin on their own nested line.

A declaration header and each maximal application spine form a group. Binder lists may soft-break between complete binders but never inside an identifier, universe suffix, or primitive literal. A declaration body has a soft break after `:=`; a broken body is nested one level. Tokens on one line have exactly one ASCII space where token separation is required and otherwise no added whitespace.

The printer inserts only parentheses required by the pinned Lean parser's precedence and associativity for the grammar production being printed. It never emits redundant parentheses. The file has one final LF and no additional empty line at end. Changes to group construction, width, indentation, blank-line policy, or parenthesization require a new artifact-convention set.

`namespaceComponent`, `universeName`, and each component of a `moduleName` are Lean identifiers. Universe names are unique in their declaration binder. `qualName` is one or more identifier components separated by `.`. A normal global reference is rooted:

```ebnf
globalName ::= "_root_." qualName
```

The `_root_.` prefix is mandatory even when a shorter name would resolve uniquely. There are exactly three exceptions:

1. a local variable or local `let` uses its `localName`;
2. a reference to a member of the definition or inductive predeclaration group currently being elaborated uses the member spelling recognized by Lean's group elaborator; and
3. a reference to a `private` declaration emitted in the same module uses its deterministic surface-private name while that name is in scope.

The latter two exceptions are not contextual searches: the checker resolves them to the declaration identity recorded in the manifest and rejects any other resolution. A group-predeclaration reference has no universe suffix because stock Lean represents the group member as a local variable whose universes are fixed by the surrounding declaration. This is a syntax-forced omission and the audit checks the fixed universe vector. A same-module private reference may carry its explicit universe suffix normally.

## G2. Modules and commands

```ebnf
module          ::= importCommand* autoImplicitGuard item*
importCommand   ::= "import" moduleName
autoImplicitGuard ::= "set_option" "autoImplicit" "false"

item ::= namespaceBlock
       | declaration
       | mutualDefBlock
       | mutualInductiveBlock

namespaceBlock ::= "namespace" namespaceComponent item* "end" namespaceComponent
```

Imports precede every other command and retain dependency order. An import may name a pinned base module or a previously generated dependency. It may not import the source module being encoded or any artifact that already contains the source declarations being reproduced.

There is exactly one `autoImplicitGuard`, immediately after the last import. No other option command is permitted.

A generated namespace block opens one identifier component, and its `end` repeats that component. Qualified source namespaces are represented by nesting. Namespace blocks affect declaration names only; every ordinary reference in a body remains rooted.

No other command is admitted. In particular, output may not contain `open`, `universe`, `variable`, `include`, `omit`, `export`, `local`, syntax, macro, notation, elaborator, deriving, attribute, or arbitrary option commands.

## G3. Declaration modifiers and names

```ebnf
declaration ::= modifierPrefix? defDecl
              | modifierPrefix? abbrevDecl
              | modifierPrefix? opaqueDecl
              | modifierPrefix? theoremDecl
              | modifierPrefix? axiomDecl
              | modifierPrefix? inductiveDecl
              | modifierPrefix? structureDecl

modifierPrefix ::= visibility protection? | protection
visibility     ::= "private" | "public"
protection     ::= "protected"

declHead ::= declName universeBinder?
universeBinder ::= ".{" universeName ("," universeName)* "}"
```

Modifiers appear only in the order shown. At most one visibility modifier and at most one `protected` modifier are permitted. A protected declaration must be inside a namespace, as required by stock Lean. A `private` declaration is referred to only through the same-module exception in G1. The generated printer does not emit `public` when it is the default.

Every universe parameter in the elaborated declaration environment occurs in `universeBinder`, in environment order. An empty universe binder is forbidden. Explicitly declared but unused universe parameters are retained. Universe parameter names are unique within the declaration.

No `nonrec`, `noncomputable`, `partial`, `unsafe`, `meta`, `extern`, `implemented_by`, documentation, attribute, or other modifier is part of grammar version 1.

## G4. Binders and declaration headers

```ebnf
explicitBinder ::= "(" localName+ ":" term ")"
binderList     ::= explicitBinder*
```

Every declared source parameter uses an ordinary explicit binder. Implicit `{x : A}`, strict-implicit `⦃x : A⦄`, instance `[x : A]`, untyped, optional, and automatic binders are forbidden. Constructor arguments use the same `explicitBinder` production. Structure fields use G6.

The printer may group adjacent names in one binder only when their normalized types are equal in the context before the group and no grouped name's type depends on an earlier name in that group. Grouping is presentation only.

The declaration header retains the distinction between source declaration parameters and a function-valued result. A leading `forall` in the declared result is not moved into `binderList`, except that equation arguments lowered under L13 in [LOWERING.md](LOWERING.md) become header parameters.

## G5. Definitions, theorems, axioms, and aliases

```ebnf
defDecl     ::= "def" declHead binderList ":" term ":=" term structuralClause?
abbrevDecl  ::= "abbrev" declHead binderList ":" term ":=" term structuralClause?
opaqueDecl  ::= "opaque" declHead binderList ":" term ":=" term structuralClause?
theoremDecl ::= "theorem" declHead binderList ":" term ":=" term structuralClause?
axiomDecl   ::= "axiom" declHead binderList ":" term

structuralClause ::= "termination_by" "structural" localName
```

Every declaration states its result type or sort. Equation clauses, `where`, `let rec`, tactic bodies, `by`, `termination_by?`, measure syntax, `decreasing_by`, and omitted bodies or types are forbidden.

Only a structurally recursive `def`, `abbrev`, `opaque`, or `theorem` has `structuralClause`. The named decreasing parameter is an explicit header parameter. A nonrecursive declaration has no termination clause.

An `axiom` is legal only when its manifest correspondence identifies an axiom in the source module's declaration delta. Neither lowering nor mining may introduce an axiom as an implementation or proof device.

Phase-two aliases are `private abbrev` declarations with complete universes, binders, result type, and body. Phase-one mechanically lifted helpers may be private `def`, `opaque`, or `theorem` declarations as authorized by [LOWERING.md](LOWERING.md).

## G6. Inductives and structures

```ebnf
inductiveDecl ::= "inductive" declHead binderList ":" sort "where" constructor*
constructor   ::= "|" declName explicitBinder* ":" term

structureDecl ::= "structure" declHead binderList ":" sort extendsClause? "where"
                  structureCtor? structureField*
extendsClause ::= "extends" parentSpec ("," parentSpec)*
parentSpec    ::= (declName ":")? term
structureCtor ::= declName "::"
structureField ::= declName ":" term (":=" term)?

mutualInductiveBlock ::= "mutual" inductiveMember inductiveMember+ "end"
inductiveMember ::= modifierPrefix? inductiveDecl
```

Each constructor states its complete result type, including datatype parameters and indices. Each constructor argument is explicitly named and typed. Constructor result types and recursive occurrences obey the stock positivity and universe checks.

References to an inductive member within its own mutual predeclaration group use G1's bare predeclaration form; the group's universe vector is fixed by the surrounding declarations and audited even though stock Lean does not accept a universe suffix on that local reference.

A structure states its result sort, every field type, and any retained field default as an Explicit Lean term. Empty structures and structures containing only inherited fields are permitted. If the source constructor name is meaningful and differs from Lean's default, `structureCtor` preserves it; otherwise the printer omits `structureCtor`. A parent specification is a fully explicit global application satisfying G8; its optional leading name preserves a meaningful generated parent-projection name. Parent order follows the source declaration and every generated construction still supplies every final field explicitly.

A mutual-inductive block contains at least two inductive declarations and no other items. Its members retain source order and grouping. A singleton is printed as an ordinary `inductiveDecl`.

Class, class-inductive, class-abbrev, and instance declarations are not grammar members; L17 in [LOWERING.md](LOWERING.md) translates their data to declarations above.

## G7. Mutual structural definitions

```ebnf
mutualDefBlock ::= "mutual" defLikeMember defLikeMember+ "end"
defLikeMember  ::= modifierPrefix? (defDecl | abbrevDecl | opaqueDecl | theoremDecl)
```

A mutual block represents exactly one recursive strongly connected component and contains at least two definition-like declarations. Every member has its own `termination_by structural` clause naming its captured decreasing parameter. References among members use the predeclaration-name exception in G1 and supply all captured and ordinary arguments. A singleton recursive component is an ordinary definition-like declaration with a structural clause.

Mutual well-founded recursion is not emitted as a recursive block. L15 lowers it to one nonrecursive explicit fixpoint definition plus nonrecursive wrapper definitions.

## G8. Terms

The term grammar is intentionally small. Parentheses may be inserted wherever required by Lean precedence; redundant parentheses do not change membership, although the generated printer uses one canonical precedence policy.

```ebnf
term ::= sort
       | localRef
       | globalRef
       | scopedDeclRef
       | application
       | lambda
       | forallTerm
       | arrowTerm
       | letTerm
       | ascription
       | rawNat
       | stringLiteral
       | matchTerm
       | emptyMatch

localRef    ::= localName
globalRef   ::= atSign? globalName universeInst?
scopedDeclRef ::= atSign? qualName universeInst?
atSign      ::= "@"
universeInst ::= ".{" level ("," level)* "}"

application ::= functionTerm argumentTerm+
lambda      ::= "fun" explicitBinder+ "=>" term
forallTerm  ::= "forall" explicitBinder+ "," term
arrowTerm   ::= term "→" term
letTerm     ::= "let" localName ":" term ":=" term ";" term
ascription  ::= "(" term ":" term ")"
emptyMatch  ::= "(" "nomatch" term ("," term)* ":" term ")"

rawNat      ::= "nat_lit" canonicalDecimal
sort        ::= "Prop" | "Type" sortLevel | "Sort" sortLevel
sortLevel   ::= canonicalDecimal | universeName | "(" level ")"
```

`functionTerm` and `argumentTerm` are terms parenthesized as needed to make the application spine unambiguous. Named arguments, including named universe arguments, are forbidden.

`scopedDeclRef` is accepted only for the predeclaration and same-module-private exceptions in G1. A predeclaration reference is bare—without `@` or `universeInst`—because all of its output binders are explicit and its universe vector is fixed by the group. For a normal global or same-module-private reference:

- `universeInst` is present with exactly all universe arguments when the declaration is polymorphic and absent when it is monomorphic;
- `@` is present exactly when exposing a non-explicit binder is necessary to print the recorded application spine without insertion; and
- the application contains exactly the term arguments present in the captured elaborated expression, in order.

Consequently intentional partial application is legal. The result may still have a function type, but no universe, implicit, strict-implicit, instance, optional, automatic, coercion, or ordinary argument already selected by source elaboration is omitted. The audit compares the entire application spine rather than guessing intent from arity.

All lambda and dependent-function binders are typed and explicit. A nondependent arrow is used only when its result does not depend on the domain binder. The only local definition form is the typed, nonrecursive, single-name `let` above.

The following are forbidden: holes, `_` as a term, `sorry`, `admit`, implicit binders, field or generalized dot notation, numeric projections, leading-dot resolution, anonymous constructors, structure instances or updates, coercion syntax, ordinary numerals, scientific or negative literals, character literals, interpolated or raw strings, collection literals, operators, equality notation, `if`, `do`, mutable-do syntax, quotations, macros, and user elaborators. `nomatch` is permitted only in the fully type-ascribed `emptyMatch` production.

A dotted rooted global identifier is not dot notation. The checker distinguishes `_root_.Point.x` from a projection selected using the inferred type of a receiver.

## G9. Universes and sorts

```ebnf
level ::= levelAtom | offsetBase "+" positiveDecimal
levelAtom ::= canonicalDecimal
            | universeName
            | "max" levelArgument levelArgument
            | "imax" levelArgument levelArgument
levelArgument ::= canonicalDecimal | universeName | "(" level ")"
offsetBase ::= universeName | "(" levelAtom ")"
```

The printer inserts parentheses around a level exactly when required by this precedence: an offset binds less tightly than a level atom, and a `max` or `imax` operand that is an offset is parenthesized. A composite level used after `Type` or `Sort` is parenthesized by `sortLevel`; the braces of `universeInst` provide the outer delimiter there. Natural numbers and `+` in a level are dedicated universe syntax, not term notation. A level contains no metavariable, `_`, inferred argument, or named argument.

Before printing, levels are canonicalized:

1. apply the pinned toolchain's `Lean.Level.normalize` to a fixed point;
2. combine any remaining nested successors into one positive offset;
3. recursively flatten `max` operands;
4. remove duplicate and neutral `0` operands;
5. sort remaining `max` operands by their canonical serialized level; and
6. rebuild a right-associated `max` tree while preserving the argument order of any `imax` that survived `Lean.Level.normalize`.

Sort spelling is canonical:

- `Sort 0` is `Prop`;
- `Sort (u + 1)` is `Type u`; and
- every other sort is `Sort u`.

Thus the ordinary type universe is `Type 0`, never bare `Type`.

## G10. Primitive literals

`canonicalDecimal` is `0` or an ASCII digit from `1` through `9` followed by zero or more ASCII digits. `positiveDecimal` is the latter nonzero case. Neither has a sign, separators, or leading zeroes.

`nat_lit n` is Lean's built-in raw-natural syntax and always has type `Nat`. It is not an overloaded numeral.

A `stringLiteral` is a Lean quoted string with this canonical scalar-by-scalar encoding:

- `"` becomes `\"` and `\` becomes `\\`;
- carriage return, line feed, and tab become `\r`, `\n`, and `\t`;
- every other scalar in U+0000–U+001F or U+007F–U+009F becomes `\uNNNN`, using exactly four uppercase hexadecimal digits; and
- every other Unicode scalar is emitted directly in UTF-8, without Unicode normalization.

Surrogate code points are not Unicode scalars and cannot occur in a Lean `String`. The audit compares the resulting scalar sequence exactly.

## G11. Canonical matches and patterns

```ebnf
matchTerm ::= "match" "(" "motive" ":=" term ")"
              term ("," term)* "with" matchBranch+
matchBranch ::= "|" pattern ("," pattern)* "=>" term

pattern ::= localName
          | "_"
          | constructorPattern
          | inaccessiblePattern
constructorPattern ::= globalConstructor pattern*
globalConstructor  ::= globalName
inaccessiblePattern ::= ".(" term ")"
```

The motive is always present and is an Explicit Lean dependent-function type with one typed binder for each discriminant. The number of patterns in every branch equals the number of discriminants. Branches occur in the captured compiled-alternative order.

A constructor pattern uses its rooted canonical name and recursively contains every constructor field that Lean's pattern grammar can state. Pattern variables are the sole untyped-binder exception because Lean pattern syntax has no annotation position. Constructor universe arguments, datatype parameters, and indices are the sole omitted-argument exception because pattern syntax has no position for them. The typed discriminants, explicit motive, constructor signature, and audit must determine all of these uniquely.

No literal, notation, structure, default-argument, ellipsis, leading-dot, named, `@`, or custom match pattern is permitted. An inaccessible pattern contains an Explicit Lean term.

A match has at least one branch because stock Lean's `match` syntax requires one. Elimination from an inductive with no constructors uses G8's type-ascribed `emptyMatch`, not a zero-branch match. Stock Lean provides no explicit-motive `nomatch` syntax and rejects a direct empty-recursion recursor in some computable definitions, so this is a narrow syntax-forced exception: the ascribed result type, typed discriminants, local context, and elaboration audit must reproduce the captured motive and empty pattern matrix exactly.

Named discriminants and named patterns are absent. L12 in [LOWERING.md](LOWERING.md) materializes their equalities, reconstructions, and reflexivity arguments explicitly. The `generalizing` option is forbidden.

## G12. Proofs and recursion terms

There is no separate proof grammar. A proof is any G8 term whose independently inferred type is in `Prop`. A theorem body is introduced directly by `:=`; no `by exact` wrapper is admitted.

Well-founded recursion is not declaration syntax in Explicit Lean. It is a nonrecursive definition whose body is a fully explicit application of `_root_.WellFounded.fix` under L15, containing the relation, well-foundedness proof, callback, decrease proofs, and final argument. These are all ordinary G8 terms.

Structural recursion is the only recursive declaration form. Recursive calls use ordinary applications and the predeclaration-name exception in G1. The audit requires stock Lean to accept exactly the decreasing parameter named by the structural clause; candidate inference and fallback are failures.

## Elaboration audit

After the syntax checker accepts a module, the compiler elaborates it with the pinned stock Lean toolchain and records the audit result in the manifest. Acceptance requires all of the following:

1. Every syntactic global reference resolves to the exact canonical declaration or recorded predeclaration/private identity.
2. Every universe and term application spine equals the captured lowered spine. Lean inserts no omitted argument except the pattern data, fixed predeclaration universe vector, and audited empty-elimination motive for which stock syntax has no explicit position.
3. No metavariable remains and no `sorryAx` dependency exists.
4. No coercion, overloaded operation, literal conversion, named-argument recovery, instance search, tactic, termination search, macro, user elaborator, or deriving hook supplies output meaning. The two G10 primitive leaves, G8's audited empty elimination, and Lean's stock parsing/elaboration of grammar productions are the only syntax-directed exceptions.
5. Every canonical match or empty elimination reproduces its recorded motive, discriminants, pattern matrix, branch functions, and generated matcher correspondence.
6. Every structural definition is accepted on exactly its named decreasing parameter. Every well-founded fixpoint is nonrecursive syntax with explicit proof arguments.
7. Every source and lowered declaration or generated auxiliary has the correspondence required by [PLAN.md](PLAN.md), [CAPTURE.md](CAPTURE.md), [LOWERING.md](LOWERING.md), and [MANIFEST.md](MANIFEST.md).
8. Every declaration type and body is kernel-checked before quotation normalization.

The audit mechanism must distinguish forbidden synthesis from ordinary deterministic work performed by Lean when checking primitive declarations, inductives, structures, matches, and recursors. Its implementation follows the stock-first, narrow-instrumentation policy in [CAPTURE.md](CAPTURE.md#c7-instrumentation-escape-hatch), while remaining independent of source capture; its event classification is versioned with the compiler and manifest.
