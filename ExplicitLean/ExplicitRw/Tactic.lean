module
prelude

public meta import ExplicitLean.ExplicitRw.Basic
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Elab.Term
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.Intro
public meta import Lean.Parser.Tactic
public meta import Lean.Meta.CongrTheorems
public meta import Lean.Meta.Tactic.Simp.Rewrite
public meta import Lean.Util.CollectFVars

public meta section

/-!
# The `explicit_rw` tactic

`explicit_rw` replays a recorded simp trace positionally, with no search.

```
explicit_rw [foo at [1, 1], ← bar at [], baz a b at [0, 1, 1],
             unfold f at [1], beta at [1, 1], eq (2 + 3 = 5) by rfl at [1]] at h
```

Each step names a position (a `SubExpr.Pos` child-index list, see
`tracking/SIMP-TRACE-SPEC.md`), navigates to exactly that subterm, and replaces
it. Steps apply in order; each position is relative to the result of the
previous step. There is no fallback, no search and no retry at other positions:
every failure names the step index and the reason.

## Step forms — the complete list

Every step kind `tracking/SIMP-TRACE-SPEC.md` defines has exactly one rendering
here. A generator author should not need to read the parser; if a construct is
not in this table, it has no form (see "Not expressible" below).

| Form                                   | Spec kind / field                       |
| -------------------------------------- | --------------------------------------- |
| `e at [..]`                            | `rw`, `dir: "fwd"`                      |
| `← e at [..]`                          | `rw`, `dir: "rev"`                      |
| `e a b at [..]`                        | `rw` with `args: ["a", "b"]`            |
| `e at [..] with [p, ...]`              | `rw` with `side`: one side proof per    |
|                                        | hypothesis, **in order**                |
| `eq_true h at [..]`                    | `rw` with `prop: "true"`                |
| `eq_false h at [..]`                   | `rw` with `prop: "false"`               |
| `prop_true h at [..]`                  | proposition proof `h : p`, yielding `p = True` |
| `prop_false h at [..]`                 | proposition proof `h : ¬p`, yielding `p = False` |
| `unfold c at [..]`                     | `unfold`                                |
| `beta at [..]`                         | `beta`                                  |
| `eta at [..]`                          | `eta`                                   |
| `proj at [..]`                         | `proj`                                  |
| `zeta at [..]`                         | `zeta` (the only step that kills a `let`)|
| `iota at [..]`                         | `iota` (**one** matcher/recursor step)  |
| `change t at [..]`                     | `change`, from its `to` field           |
| `eq (lhs = rhs) by rfl at [..]`        | `eq`, `by: "rfl"`                       |
| `eq (lhs = rhs) by decide at [..]`     | `eq`, `by: "decide"`                    |
| `congr i [nested steps] at [..]`       | `congr` with `arg: i` and its `steps`   |
| `transport forall h [domain] body [body] at [..]` | explicit dependent-forall domain transport |
| `intro_ctx h domain at [d] deps [..] scope s enter at [e] exit at [x] with [steps] at [..]` | contextual arrow scope with `introduced_ref h` |
| `... at h`                             | location `{"hyp": "h"}`                 |
| `... then <side proof>`                | the location's `close`                  |

### Side proofs — `with [...]` and `then`

Both take the same closed, **recursive** grammar:

| Side proof                | Spec `close.by` / use                              |
| ------------------------- | -------------------------------------------------- |
| `rfl`                     | `"rfl"`                                            |
| `decide`                  | `"decide"`                                         |
| `omega`                   | `"omega"` (a decision procedure, not simp family)  |
| `nofun`                   | `"nofun"` (impossible constructor equation)        |
| `close [t]`               | self-delimiting exact proof term; generated for       |
|                           | `true_intro`, `assumption:n` and `absurd:h`           |
| `exact t`                 | retained for backwards compatibility                  |
| `intro x y ; <side proof>` | a side trace with `intros` — needed whenever the   |
|                           | hypothesis is implication-shaped, as `ite_congr`   |
|                           | and `dite_congr` produce                            |
| `explicit_rw [...] (then <side proof>)?` | a side trace with its own `steps`     |

`then` applies to the goal, so a trace that rewrites a hypothesis puts its
closer on the next line — which is where `absurd:<hyp>` lands.

### Naming an inaccessible hypothesis

The spec's `local` field may report `inaccessible: true` with a `ctxIndex`; the
recorded `name` is then a display form such as `a✝`, which cannot be written.
The convention is **ordinary Lean**: emit `rename_i` on the line before
`explicit_rw`. `rename_i` names the last *n* inaccessible hypotheses in context
order, so a generator names every inaccessible up to and including the one it
needs, and then uses its chosen name:

```
rename_i h₁ h₂        -- two inaccessibles; h₁ is the earlier
explicit_rw [h₁ at [0, 1, 0, 1]]
```

This needs no `explicit_rw` syntax and is why none exists.

### Not expressible, deliberately

| Construct            | Why                                                 |
| -------------------- | --------------------------------------------------- |
| `intro_ctx` without recorder metadata | The consumer requires the stable handle and explicit domain/dependency/scope fields. |
| `at *`               | Positions are relative to one location. Emit one     |
|                      | `explicit_rw` per location.                          |

`e` is an ordinary term, so explicit arguments (`baz a b`), local hypotheses and
side-condition proofs are written as usual and elaborated as usual: implicits,
universes and instances are recovered by elaboration and unification. Common
terms use the structural grammar below; generated terms outside that grammar
use the fully delimited `lean_term(...)` form, which delegates parsing to Lean
in the caller's notation scope. A stale `pp.all` term (`nat_lit`) remains
invalid recorder output.

Positions are raw child indices, *not* `conv`'s `arg n` numbering: `conv`'s
`arg` counts explicit arguments, while `0`/`1` here are the `fn`/`arg` children
of `Expr.app`, so `f a b` has `b` at `[1]` and `a` at `[0, 1]`.

## Closing form

`explicit_rw [...] then rfl` runs `rfl` on the remaining goal after the last
step. The closer is a **closed enumeration** — `rfl`, `decide`, and
`close [<term>]` (`exact <term>` remains accepted for compatibility) —
and `eq ... by` likewise accepts only `rfl` or `decide`. Omit the clause to leave
the goal open. `trivial` and bare `assumption` are excluded because both search
where the spec recorded an exact choice; the spec's `true_intro`,
`assumption:<name>` and `absurd:<hyp>` all render as `close [<term>]`. `rfl` is
ordinary `rfl` tactic (`Eq`/`Iff`/`HEq` reflexivity and `@[refl]` lemmas), not a
simp-backed one.

The `then` clause applies to the goal. A trace that rewrites a hypothesis leaves
the closer to the goal; the renderer emits an empty `explicit_rw [] then ...`
after that hypothesis rewrite so the generated close stays in the closed
grammar.
Generated exact-term closes use `close [t]`: the brackets delimit the term so
the following tactic in an unbulleted tactic sequence cannot be parsed as an
additional term argument. `exact t` remains accepted for existing source.

Neither slot is a `tacticSeq`, deliberately. A free `tacticSeq` would let a
generated trace carry `simp` (or any forbidden tactic) *inside* the product
tactic, where a lint scanning `ExplicitLean/ExplicitRw*` could never see it,
because the offending text lives at the generated call site. For the same
reason every term this tactic elaborates — a lemma, a `change` target, an `eq`
equation, an `exact` closer — is rejected if it contains a `by` block.

## No simp

Nothing in this tactic calls, imports for use, or expands to `Lean.Meta.Simp` or
any simp-family tactic; `Experiment/check_no_simp_family.py` enforces that.

For what a *trace* can introduce, the guarantee is deliberately stated as a
conditional, because that is what is true. The two tactic slots are closed
enumerations. Every term slot is parsed in `explicitRwTerm`; its fully
parenthesized Lean-term form is checked for tactic blocks before and after
elaboration. What the grammar cannot see is an identifier bound to a custom
term elaborator, which is indistinguishable from an ordinary constant at parse
time and can run the simplifier in `MetaM` without producing any `by` syntax.
So:

> No trace written in this syntax can introduce a simp-family tactic, **provided
> the file it lives in declares no term elaborators** (`elab`, `macro`,
> `syntax`, `@[term_elab]`).

That proviso holds for generated Mathlib files by construction — a translated
file has no business declaring elaborators — and is to be enforced generator-side
by a lint (T4), not from inside this tactic. The macro-expanded syntax check in
`checkNoTacticBlock` and the synthetic-metavariable check in
`checkNoPendingTactic` enforce the restriction on tactic blocks for both term
forms.
-/

namespace ExplicitLean.ExplicitRw

open Lean Elab Tactic Meta

/-!
## The term grammar

Every term a trace hands to `explicit_rw` — a rewrite lemma with its explicit
arguments, an `eq` equation, a `change` target, an `exact` closer — is parsed in
the `explicitRwTerm` category below. The structural productions make common
forms explicit. A fully parenthesized Lean `term` production also admits
notation from the caller's scope and makes its boundary unambiguous to the
enclosing step grammar.

Parenthesization does not bypass the tactic guard. Before elaboration, every
term slot expands macros and rejects `by`/tactic-sequence syntax; after
elaboration, the synthetic-metavariable check catches tactic blocks introduced
indirectly. A custom term elaborator that invokes the simplifier directly can
still be indistinguishable from an ordinary constant, so the generator-side
restriction against local elaborator declarations remains necessary.

The structural grammar admits identifiers (dotted, optionally `@`-prefixed,
including projection suffixes such as `h.elim`), application, `_`, literals,
parentheses, ascriptions, binders, and the operators used by the trace format.
The parenthesized ordinary-term production covers notation and term forms not
enumerated there. `by` blocks and tactic sequences are refused by the checks
described above.

**Residual hole, stated honestly.** A bare identifier can be bound to a custom
term elaborator via `@[term_elab]`, and that is indistinguishable from an
ordinary constant at parse time. `explicit_rw` cannot close this from the
inside. It is closed generator-side, by the simp-family lint together with a ban
on `elab`/`macro`/`syntax` declarations inside generated regions — a T4 concern,
not implemented here. So the guarantee this tactic offers is: no trace written
in this syntax can introduce a simp-family tactic, *provided* the file it lives
in declares no term elaborators.
-/

/--
A trace term. One category covers terms and types alike: in dependent type
theory they are the same syntactic class, and splitting them only duplicated
every production.
-/
declare_syntax_cat explicitRwTerm

/-- Types use the same trace-term category; the alias keeps step syntax readable. -/
syntax explicitRwType := explicitRwTerm

/-! ### Atoms -/

/-- An identifier, optionally `@`-prefixed; dotted names included. -/
syntax:max (name := explicitRwTermIdent) ("@")? ident : explicitRwTerm
/-- A placeholder for an argument the position determines. -/
syntax:max (name := explicitRwTermHole) "_" : explicitRwTerm
/-- A numeric literal. -/
syntax:max (name := explicitRwTermNum) num : explicitRwTerm
/-!
`local_ref` and `introduced_ref` are deliberately syntax in this private
trace category, rather than ordinary Lean terms. Their term elaborators
in the companion `ExplicitRw.LocalHandles` module are therefore reachable only
after `explicit_rw` has accepted the DSL term; source code cannot write either
spelling as a normal term.
-/
declare_syntax_cat localRefSuffix
syntax:max ("." num)+ : localRefSuffix
syntax:max (name := explicitRwLocalRefTerm) "local_ref " num (localRefSuffix)? : explicitRwTerm
syntax:max (name := explicitRwIntroducedRefTerm) "introduced_ref " num : explicitRwTerm
/-- A string literal. -/
syntax:max (name := explicitRwTermStr) str : explicitRwTerm
/-- `Type`, `Type u`, `Sort u`. -/
syntax:max (name := explicitRwTermSort)
  ("Type" <|> "Sort") (ident <|> num)? : explicitRwTerm
/-- `Type*` and `Sort*`, which Lean lexes as single tokens. -/
syntax:max (name := explicitRwTermSortStar) ("Type*" <|> "Sort*") : explicitRwTerm
/-- `Prop`. -/
syntax:max (name := explicitRwTermProp) "Prop" : explicitRwTerm
/-- Mathlib's numeric type notations. These are declared as notation *tokens*,
not identifiers, so the lexer stops before the category sees them unless they are
listed here — and `(2 : ℝ)` is exactly how the pretty printer spells an ascribed
literal, so a generator holds these constantly. -/
syntax:max (name := explicitRwTermNumType)
  ("ℕ" <|> "ℤ" <|> "ℚ" <|> "ℝ" <|> "ℂ") : explicitRwTerm

/-! ### Grouping, application, projection -/

/-- Application, left-associated as usual. -/
syntax:10 (name := explicitRwTermApp) explicitRwTerm:10 explicitRwTerm:max : explicitRwTerm
/--
One named argument in an application, preserved as Lean's own named-argument
syntax.  This is intentionally the only simp-source syntax admitted here:
T22 supplies the authenticated source span, and the value is still checked by
the ordinary explicit term grammar before it is lowered to Lean's
`namedArgument` node.  It is not a general argument serializer.
-/
syntax:max (name := explicitRwTermNamedArg) "(" ident " := " explicitRwTerm ")" : explicitRwTerm
/-- Parentheses. -/
syntax:max (name := explicitRwTermParen) "(" explicitRwTerm ")" : explicitRwTerm
/--
An ordinary Lean term behind an explicit delimiter. The recorder sometimes
prints notation that the structural grammar above does not spell out (for
example `⊥`, a user-defined lattice operator, or a linear-map arrow). The
`lean_term(...)` delimiters make the extent explicit to the `explicit_rw`
parser; Lean's ordinary term parser handles the interior in the caller's scope.
`toTermCore` removes this wrapper and returns the parsed term syntax. Tactic
blocks are still rejected by the per-step macro and synthetic-mvar checks
before the term can be used.
-/
syntax:max (name := explicitRwTermLean) "lean_term(" term ")" : explicitRwTerm
/-- A type ascription, whose type is itself whitelisted. -/
syntax:max (name := explicitRwTermAscr) "(" explicitRwTerm " : " explicitRwTerm ")" : explicitRwTerm
/-- A pair, as the pretty printer writes it. -/
syntax:max (name := explicitRwTermPair) "(" explicitRwTerm ", " explicitRwTerm ")" : explicitRwTerm
/-- A projection on any whitelisted term: `(f x).1`, `(hp q).elim`. This admits
no new *shape*, only a projection on an operand that is already whitelisted. -/
syntax:max (name := explicitRwTermProj) explicitRwTerm:max "." (ident <|> num) : explicitRwTerm

/-! ### Binders

Both the typed and the untyped spellings, because the pretty printer omits the
type when it is inferable. Pattern-matching lambdas are *not* admitted: `fun` is
followed by plain identifiers only.
-/

/-- `fun x => t`, `fun x y => t`, `fun (x : α) => t`. -/
syntax:max (name := explicitRwTermFun)
  "fun " (ident)+ (" : " explicitRwTerm)? " => " explicitRwTerm : explicitRwTerm
/-- `fun (x : α) => t`, the parenthesised spelling. -/
syntax:max (name := explicitRwTermFunParen)
  "fun " "(" (ident)+ " : " explicitRwTerm ")" " => " explicitRwTerm : explicitRwTerm
/-- `∀ x, p`, `∀ x : α, p`, `∀ x y, p`. -/
syntax:max (name := explicitRwTermForall)
  "∀ " (ident)+ (" : " explicitRwTerm)? ", " explicitRwTerm : explicitRwTerm
/-- `∀ (x : α), p`, the parenthesised spelling. -/
syntax:max (name := explicitRwTermForallParen)
  "∀ " "(" (ident)+ " : " explicitRwTerm ")" ", " explicitRwTerm : explicitRwTerm
/-- `∃ x, p`, `∃ x : α, p`. -/
syntax:max (name := explicitRwTermExists)
  "∃ " (ident)+ (" : " explicitRwTerm)? ", " explicitRwTerm : explicitRwTerm
/-- `∃ (x : α), p`, the parenthesised spelling. -/
syntax:max (name := explicitRwTermExistsParen)
  "∃ " "(" (ident)+ " : " explicitRwTerm ")" ", " explicitRwTerm : explicitRwTerm
/-- Set-builder `{x | p}` and `{x : α | p}`. -/
syntax:max (name := explicitRwTermSetOf)
  "{" ident (" : " explicitRwTerm)? " | " explicitRwTerm "}" : explicitRwTerm

/-! ### Conditionals -/

/-- `if c then a else b`. T1's `reduceIte` simproc emits this spelling. -/
syntax:max (name := explicitRwTermIte)
  "if " explicitRwTerm " then " explicitRwTerm " else " explicitRwTerm : explicitRwTerm
/-- `if h : c then a else b`, the dependent spelling. -/
syntax:max (name := explicitRwTermDIte)
  "if " ident " : " explicitRwTerm " then " explicitRwTerm " else " explicitRwTerm : explicitRwTerm

/-! ### Prefix and postfix operators

The spellings Mathlib's pretty printer emits. Each takes whitelisted operands,
so none of them admits a new term shape.
-/

/-- Negation of a proposition. -/
syntax:max (name := explicitRwTermNot) "¬" explicitRwTerm:40 : explicitRwTerm
/-- Arithmetic negation. -/
syntax:75 (name := explicitRwTermNeg) "-" explicitRwTerm:75 : explicitRwTerm
/-- A coercion arrow, as the pretty printer writes one. -/
syntax:max (name := explicitRwTermUp) "↑" explicitRwTerm:max : explicitRwTerm
@[inherit_doc explicitRwTermUp]
syntax:max (name := explicitRwTermFunCoe) "⇑" explicitRwTerm:max : explicitRwTerm
@[inherit_doc explicitRwTermUp]
syntax:max (name := explicitRwTermSetCoe) "↥" explicitRwTerm:max : explicitRwTerm
/-- Inverse. -/
syntax:max (name := explicitRwTermInv) explicitRwTerm:max "⁻¹" : explicitRwTerm

/-! ### Binary operators

Arithmetic and order, the algebraic and set-theoretic operators Mathlib's pretty
printer emits, and the logical connectives needed to state an equation.
-/

/-- Arithmetic. -/
syntax:65 (name := explicitRwTermAdd) explicitRwTerm:65 " + " explicitRwTerm:66 : explicitRwTerm
@[inherit_doc explicitRwTermAdd]
syntax:65 (name := explicitRwTermSub) explicitRwTerm:65 " - " explicitRwTerm:66 : explicitRwTerm
@[inherit_doc explicitRwTermAdd]
syntax:70 (name := explicitRwTermMul) explicitRwTerm:70 " * " explicitRwTerm:71 : explicitRwTerm
@[inherit_doc explicitRwTermAdd]
syntax:70 (name := explicitRwTermDiv) explicitRwTerm:70 " / " explicitRwTerm:71 : explicitRwTerm
@[inherit_doc explicitRwTermAdd]
syntax:70 (name := explicitRwTermMod) explicitRwTerm:70 " % " explicitRwTerm:71 : explicitRwTerm
@[inherit_doc explicitRwTermAdd]
syntax:75 (name := explicitRwTermPow) explicitRwTerm:76 " ^ " explicitRwTerm:75 : explicitRwTerm
/-- Scalar multiplication. -/
syntax:73 (name := explicitRwTermSMul) explicitRwTerm:74 " • " explicitRwTerm:73 : explicitRwTerm
/-- Function composition. -/
syntax:90 (name := explicitRwTermComp) explicitRwTerm:91 " ∘ " explicitRwTerm:90 : explicitRwTerm
/-- Divisibility. -/
syntax:50 (name := explicitRwTermDvd) explicitRwTerm:51 " ∣ " explicitRwTerm:51 : explicitRwTerm
/-- Product of types. -/
syntax:35 (name := explicitRwTermProd) explicitRwTerm:36 " × " explicitRwTerm:35 : explicitRwTerm

/-- Set membership and inclusion. -/
syntax:50 (name := explicitRwTermMem) explicitRwTerm:51 " ∈ " explicitRwTerm:51 : explicitRwTerm
@[inherit_doc explicitRwTermMem]
syntax:50 (name := explicitRwTermNotMem) explicitRwTerm:51 " ∉ " explicitRwTerm:51 : explicitRwTerm
@[inherit_doc explicitRwTermMem]
syntax:50 (name := explicitRwTermSubset) explicitRwTerm:51 " ⊆ " explicitRwTerm:51 : explicitRwTerm
@[inherit_doc explicitRwTermMem]
syntax:50 (name := explicitRwTermSSubset) explicitRwTerm:51 " ⊂ " explicitRwTerm:51 : explicitRwTerm
@[inherit_doc explicitRwTermMem]
syntax:65 (name := explicitRwTermUnion) explicitRwTerm:65 " ∪ " explicitRwTerm:66 : explicitRwTerm
@[inherit_doc explicitRwTermMem]
syntax:70 (name := explicitRwTermInter) explicitRwTerm:70 " ∩ " explicitRwTerm:71 : explicitRwTerm
@[inherit_doc explicitRwTermMem]
syntax:70 (name := explicitRwTermSDiff) explicitRwTerm:70 " \\ " explicitRwTerm:71 : explicitRwTerm

/-- Order and equality. -/
syntax:50 (name := explicitRwTermLe) explicitRwTerm:51 " ≤ " explicitRwTerm:51 : explicitRwTerm
@[inherit_doc explicitRwTermLe]
syntax:50 (name := explicitRwTermLt) explicitRwTerm:51 " < " explicitRwTerm:51 : explicitRwTerm
@[inherit_doc explicitRwTermLe]
syntax:50 (name := explicitRwTermGe) explicitRwTerm:51 " ≥ " explicitRwTerm:51 : explicitRwTerm
@[inherit_doc explicitRwTermLe]
syntax:50 (name := explicitRwTermGt) explicitRwTerm:51 " > " explicitRwTerm:51 : explicitRwTerm
@[inherit_doc explicitRwTermLe]
syntax:50 (name := explicitRwTermEq) explicitRwTerm:51 " = " explicitRwTerm:51 : explicitRwTerm
@[inherit_doc explicitRwTermLe]
syntax:50 (name := explicitRwTermNe) explicitRwTerm:51 " ≠ " explicitRwTerm:51 : explicitRwTerm

/-- Logical connectives. -/
syntax:20 (name := explicitRwTermIff) explicitRwTerm:21 " ↔ " explicitRwTerm:21 : explicitRwTerm
@[inherit_doc explicitRwTermIff]
syntax:35 (name := explicitRwTermAnd) explicitRwTerm:36 " ∧ " explicitRwTerm:35 : explicitRwTerm
@[inherit_doc explicitRwTermIff]
syntax:30 (name := explicitRwTermOr) explicitRwTerm:31 " ∨ " explicitRwTerm:30 : explicitRwTerm
@[inherit_doc explicitRwTermIff]
syntax:25 (name := explicitRwTermArrow) explicitRwTerm:26 " → " explicitRwTerm:25 : explicitRwTerm

/-! ## Step syntax -/

/-- `at [0, 1, 1]` — the position a step applies at. `at []` is the whole location. -/
syntax explicitRwPos := " at " "[" num,* "]"

/-! The operational v2 syntax is declared in this shared parser module so a
closed v2 program can recursively discharge a rewrite premise. Its evaluator
remains in `ExplicitRw.Operational`; this section defines syntax only. -/

declare_syntax_cat explicitRwOperationalStep
declare_syntax_cat explicitRwOperationalProof

/- Parse closed proof atoms as identifiers instead of reserving `rfl` (or
future atom names) globally. Reserving `rfl` here changes ordinary Lean parsing
in every module that imports `ExplicitRw`. The evaluator accepts only the two
enumerated spellings. -/
syntax (name := explicitRwOperationalProofAtom) ident : explicitRwOperationalProof
syntax (name := explicitRwOperationalProofAssumptionRef)
  "assumption " "local_ref " num : explicitRwOperationalProof
syntax (name := explicitRwOperationalProofAssumption)
  "assumption " ident : explicitRwOperationalProof
syntax (name := explicitRwOperationalProofIntro)
  "intro " num " ; " explicitRwOperationalProof : explicitRwOperationalProof

syntax explicitRwOperationalWith := " with " "[" explicitRwOperationalProof,* "]"

syntax (name := explicitRwOperationalRule)
  "rule " ident " variant " num " phase " ident ("fwd" <|> "rev")
  &"extra" num explicitRwPos explicitRwOperationalWith : explicitRwOperationalStep

syntax (name := explicitRwOperationalSource)
  "source_rule " explicitRwTerm " variant " num " phase " ident ("fwd" <|> "rev")
  &"extra" num explicitRwPos explicitRwOperationalWith : explicitRwOperationalStep

syntax (name := explicitRwOperationalEquation)
  "equation " ident &"index" num " variant " num " phase " ident ("fwd" <|> "rev")
  &"extra" num explicitRwPos explicitRwOperationalWith : explicitRwOperationalStep

syntax (name := explicitRwOperationalLocal)
  "local " ident " variant " num " phase " ident ("fwd" <|> "rev")
  &"extra" num explicitRwPos explicitRwOperationalWith : explicitRwOperationalStep

syntax (name := explicitRwOperationalLocalRef)
  &"local" "local_ref " num " variant " num " phase " ident ("fwd" <|> "rev")
  &"extra" num explicitRwPos explicitRwOperationalWith : explicitRwOperationalStep

syntax (name := explicitRwOperationalBeta)
  "beta " explicitRwPos : explicitRwOperationalStep
syntax (name := explicitRwOperationalInstantiate)
  "instantiate " explicitRwPos : explicitRwOperationalStep
syntax (name := explicitRwOperationalIota)
  "iota " explicitRwPos : explicitRwOperationalStep
syntax (name := explicitRwOperationalProj)
  "proj " explicitRwPos : explicitRwOperationalStep
syntax (name := explicitRwOperationalZeta)
  "zeta " explicitRwPos : explicitRwOperationalStep
syntax (name := explicitRwOperationalZetaLocal)
  "zeta_local " "local_ref " num ident explicitRwPos : explicitRwOperationalStep
syntax (name := explicitRwOperationalFoldNatLit)
  "fold_nat_lit " explicitRwPos : explicitRwOperationalStep
syntax (name := explicitRwOperationalUnfold)
  "unfold " ident explicitRwPos : explicitRwOperationalStep
syntax (name := explicitRwOperationalSimproc)
  &"simproc" ident explicitRwPos : explicitRwOperationalStep
syntax (name := explicitRwOperationalCached)
  "cached" "[" explicitRwOperationalStep,* "]" explicitRwPos : explicitRwOperationalStep

declare_syntax_cat explicitRwOperationalCongruenceArg
syntax (name := explicitRwOperationalCongruenceArg)
  "arg " num explicitRwOperationalProof : explicitRwOperationalCongruenceArg
syntax (name := explicitRwOperationalCongruence)
  "congr_rule " ident explicitRwPos " with "
    "[" explicitRwOperationalCongruenceArg,* "]" : explicitRwOperationalStep

declare_syntax_cat explicitRwOperationalAutoCongruenceArg
syntax (name := explicitRwOperationalAutoCongruenceArg)
  "arg " num "[" explicitRwOperationalStep,* "]" : explicitRwOperationalAutoCongruenceArg
syntax (name := explicitRwOperationalAutoCongruence)
  "auto_congr " explicitRwPos " with "
    "[" explicitRwOperationalAutoCongruenceArg,* "]" : explicitRwOperationalStep

syntax (name := explicitRwOperationalForallCongruence)
  "forall_congr " explicitRwPos
    &" domain " "[" explicitRwOperationalStep,* "]"
    &" body " "[" explicitRwOperationalStep,* "]" : explicitRwOperationalStep

declare_syntax_cat explicitRwOperationalClose
syntax (name := explicitRwOperationalClose)
  " then " explicitRwOperationalProof : explicitRwOperationalClose
syntax (name := explicitRwOperationalCloseFalseElim)
  " then " &"false_elim" : explicitRwOperationalClose

syntax (name := explicitRwOperationalProofNested)
  "explicit_rw_v2 " "[" explicitRwOperationalStep,* "]"
  (explicitRwOperationalClose)? : explicitRwOperationalProof

declare_syntax_cat explicitRwOperationalLocation
syntax (name := explicitRwOperationalLocationIdent)
  " at " ident : explicitRwOperationalLocation
syntax (name := explicitRwOperationalLocationRef)
  &" at " &"local_ref " num : explicitRwOperationalLocation

syntax (name := explicitRwOperational)
  "explicit_rw_v2 " "[" explicitRwOperationalStep,* "]"
  (explicitRwOperationalLocation)? (explicitRwOperationalClose)? : tactic

/-- Replay one recorded `explicit_rw_v2` program per current goal, in order. -/
syntax (name := explicitRwOperationalGoals)
  "explicit_rw_v2_goals " "[" explicitRwOperationalProof,* "]" : tactic

/-- Run one ordinary source tactic, then replay one recorded v2 program for
each goal it produced, in exact order. -/
syntax (name := explicitRwOperationalGoalsAfter)
  "explicit_rw_v2_goals_after " "[" explicitRwOperationalProof,* "]" " by " tacticSeq : tactic

/--
A **side proof**: the closed, recursive grammar for discharging a side condition
or closing a goal.

The recursion matters. A conditional lemma's hypothesis is often
implication-shaped — `ite_congr` and `dite_congr` produce `c → x = u` — so
proving it needs to introduce the antecedent and then replay a nested trace. That
is `intro h; explicit_rw [...] then rfl`, which no flat enumeration can express.

It stays closed: `rfl`, `decide`, `omega`, `nofun`, `close [<whitelisted term>]`,
`exact <whitelisted term>`,
`intro <ident>+ ; <sideProof>`, and a nested `explicit_rw` with its own optional
closer. `omega` is a decision procedure, not simp family. Nothing else is
admitted, so a side proof can no more introduce a forbidden tactic than a closer
can.
-/
declare_syntax_cat explicitRwSideProof (behavior := symbol)

/-- Reflexivity. -/
syntax (name := explicitRwSideRfl) &"rfl" : explicitRwSideProof
/-- Decision by evaluation. -/
syntax (name := explicitRwSideDecide) &"decide" : explicitRwSideProof
/-- Linear arithmetic. -/
syntax (name := explicitRwSideOmega) &"omega" : explicitRwSideProof
/-- An impossible constructor equation. -/
syntax (name := explicitRwSideNofun) &"nofun" : explicitRwSideProof
/-- A closing term. -/
syntax (name := explicitRwSideExact) &"exact " explicitRwTerm : explicitRwSideProof
/-- A delimiter-bearing exact proof term for generated source. -/
syntax (name := explicitRwSideClose) &"close " "[" explicitRwTerm "]" : explicitRwSideProof
/-- Introduce the antecedents of an implication-shaped side condition. -/
/- A recorder-issued handle introduces exactly one binder.  The continuation is
   recursive, so nested side proofs can introduce further handles in order. -/
syntax (name := explicitRwSideIntroRef)
  &"intro_ref " num " ; " explicitRwSideProof : explicitRwSideProof
/-- Introduce the antecedents of an implication-shaped side condition. -/
syntax (name := explicitRwSideIntro)
  &"intro " (ident)+ " ; " explicitRwSideProof : explicitRwSideProof

/-- Retained name for the entries of a `with [...]` clause. -/
syntax explicitRwSideTac := explicitRwSideProof

/-- The optional side-condition clause of a rewrite step. -/
syntax explicitRwWith := " with " "[" explicitRwSideTac,* "]"

/-- A lemma rewrite, forwards or backwards: `foo a b at [1]`, `← bar at []`. -/
syntax explicitRwRw := ("← ")? explicitRwTerm explicitRwPos (explicitRwWith)?

/-- A proposition-valued rule application, whose proof is supplied after the
selected redex has fixed the rule's ordinary and instance arguments. -/
syntax explicitRwProp := (&"prop_true" <|> &"prop_false") explicitRwTerm explicitRwPos
  (explicitRwWith)?

/-- `unfold f at [1]` — delta-unfold one constant, definitionally. -/
syntax explicitRwUnfold := "unfold " ident explicitRwPos

/--
`beta at [1]`, `eta at [1]`, `proj at [1]`, `zeta at [1]`, `iota at [1]` — the
silent definitional reductions of the spec's `beta|eta|proj|zeta|iota` kinds.

`zeta` is the only step that destroys a `let`. `iota` reduces one matcher or
recursor application whose major premise is a constructor.
-/
syntax explicitRwRed :=
  (&"beta" <|> &"eta" <|> &"proj" <|> &"zeta" <|> &"iota") explicitRwPos

/--
`zeta_local local_ref n at [..]` unfolds exactly one authenticated local
let-declaration. Unlike plain `zeta`, whose selected subterm must be a `letE`,
this is the source form for simp's zeta-delta reduction of a local free
variable. The context index is recorder evidence; no name lookup is performed.
-/
syntax explicitRwZetaLocal := &"zeta_local " &"local_ref " num explicitRwPos

/-- `change t at [1]` — last-resort definitional replacement, checked by defeq. -/
syntax explicitRwChange := "change " explicitRwTerm explicitRwPos

/--
The closers a trace may use, as a **closed enumeration**. `explicit_rw` is
product code, so it must not embed a free `tacticSeq`. The spec's `close` field
maps onto `rfl` and `decide`, plus self-delimiting `close [<term>]` for forms
that name something: `true_intro` is `close [True.intro]`,
`assumption:<name>` is `close [<name>]`, and `absurd:<hyp>` is
`close [<hyp>.elim]`. Existing `exact <term>` source remains accepted, but
generated terms use brackets so a following unbulleted tactic cannot be
swallowed as another application argument.

Two tactics are deliberately **not** offered, both because they search where the
spec recorded an exact choice: `trivial` is a macro that tries several tactics in
turn, and bare `assumption` scans the whole local context, so it can succeed by
finding a *different* hypothesis than the one the trace recorded.

`rfl` here is the ordinary `rfl` tactic — `Eq`/`Iff`/`HEq` reflexivity and
`@[refl]` lemmas. It is not `simp`-backed and performs no simplification.
-/
syntax explicitRwCloser := explicitRwSideProof

/--
`eq (2 + 3 = 5) by rfl at [1]` — a simproc-computed equation, proved by an
ordinary tactic. The spec's `by` field is exactly `rfl | decide`, so only those
two are accepted; see `explicitRwCloser` for why this is not a `tacticSeq`.
-/
syntax explicitRwEq := &"eq " explicitRwType " by " (&"rfl" <|> &"decide") explicitRwPos

/-- The innermost nesting level: no further `congr`. -/
syntax explicitRwInnerStep0 :=
  explicitRwUnfold <|> explicitRwRed <|> explicitRwZetaLocal <|>
  explicitRwChange <|> explicitRwEq <|>
  explicitRwProp <|> explicitRwRw

/- A closed contextual scope. The recorder supplies the stable introduced
   handle, exact domain position, local-declaration dependencies, and explicit
   enter/exit scope positions. Nested ordinary steps run while the handle is
   in scope; `introduced_ref` is the only way they can refer to it. -/
syntax explicitRwIntroCtx :=
  &"intro_ctx " num
  " domain " explicitRwPos
  " deps " "[" num,* "]"
  " scope " num
  " enter " explicitRwPos
  " exit " explicitRwPos
  " with " "[" explicitRwInnerStep0,* "]"
  explicitRwPos

/-- A `congr` whose nested steps are innermost. -/
syntax explicitRwCongr0 :=
  &"congr " num " [" explicitRwInnerStep0,* "]" explicitRwPos

/-- One nesting level up, so a `congr` may nest a `congr` — which T1's
`congr_nested_cast` trace does, transporting two levels of type equality. -/
syntax explicitRwInnerStep :=
  explicitRwUnfold <|> explicitRwRed <|> explicitRwZetaLocal <|>
  explicitRwChange <|> explicitRwEq <|>
  explicitRwCongr0 <|> explicitRwProp <|> explicitRwRw

/--
`congr <i> [nested steps] at [pos]` — the spec's `congr` step kind.

At `pos` the subterm must be an application. The auto-generated congruence
theorem for its head is obtained with `Lean.Meta.mkCongrSimp?`; the equation for
argument `i` is proved by replaying the nested steps as a sub-replay rooted at
that argument; and the theorem is then applied, which transports the arguments
that depend on it. This is what a plain `congrArg` cannot do, and it is why a
dependent position that `explicit_rw` otherwise refuses becomes replayable.

`Lean.Meta.CongrTheorems` is ordinary congruence-lemma generation, not the
simplifier: it lives outside `Lean.Meta.Tactic.Simp`, and
`Experiment/check_no_simp_family.py` accepts the import.
-/
syntax explicitRwCongr :=
  &"congr " num " [" explicitRwInnerStep,* "]" explicitRwPos

/- A recorder-issued dependent-forall transport.  The first step list rewrites
the domain; the second (under the stable binder handle) rewrites its body. -/
syntax explicitRwTransport :=
  &"transport " &"forall " num " [" explicitRwInnerStep,* "]" &" body " "[" explicitRwInnerStep,* "]" explicitRwPos

/-- One step of an `explicit_rw` trace. The keyword-led forms are tried before
the bare-term rewrite, so `beta at [...]` is the reduction rather than a lemma
named `beta`. -/
syntax explicitRwStep :=
  explicitRwUnfold <|> explicitRwRed <|> explicitRwZetaLocal <|>
  explicitRwIntroCtx <|> explicitRwChange <|>
  explicitRwEq <|> explicitRwCongr <|> explicitRwTransport <|> explicitRwProp <|> explicitRwRw

/-- Optional closing tactic: `explicit_rw [...] then rfl`. -/
syntax explicitRwClose := " then " explicitRwSideProof

/-- A nested trace, so an implication-shaped side condition can be discharged by
replaying its own recorded steps. -/
syntax (name := explicitRwSideNested)
  "explicit_rw " "[" explicitRwStep,* "]" (explicitRwClose)? : explicitRwSideProof

/--
Replay a recorded simp trace positionally, with no search.

Each step names a `SubExpr.Pos` child-index path and the rewrite to perform
there. See the module documentation for the step forms.
-/
syntax (name := explicitRw) "explicit_rw " "[" explicitRwStep,* "]"
  (Lean.Parser.Tactic.location)? (explicitRwClose)? : tactic

namespace Impl

/-! ### Indexed local references

The recorder's local reference carries the declaration's `LocalDecl.index`, not
its pretty-printed name.  Keep the lookup here deliberately boring: one direct
`PersistentArray` access followed by declaration and projection checks.  In
particular, do not use `getLocalDeclFromUserName`, `findLocalDeclWithType?`, or
any other context search.
-/

abbrev IntroducedHandles := Std.HashMap Nat FVarId

def natLiteral? (text : String) : Option Nat :=
  if text.isEmpty || !text.toList.all (fun c => 48 ≤ c.toNat && c.toNat ≤ 57) then none
  else some (text.toList.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)

partial def natLiterals (stx : Syntax) : Array Nat :=
  if let some n := natLiteral? (stx.getKind.toString false) then #[n]
  else stx.getArgs.foldl (init := #[]) fun out child => out ++ natLiterals child

def localRefIndex (stx : Syntax) : TermElabM Nat := do
  let values := natLiterals stx[1]
  if values.size != 1 then
    throwError "explicit_rw: local_ref requires a canonical decimal index"
  return values[0]!

def localRefProjectionIndices (stx : Syntax) : TermElabM (Array (Nat × Nat)) := do
  if stx[2].isNone then return #[]
  else
    let values := natLiterals stx[2][0]
    if values.isEmpty then
      throwError "explicit_rw: local_ref projection requires canonical decimal indices"
    return values.map fun surface =>
      (surface, if surface == 0 then 0 else surface - 1)

def checkedHandle (stx : Syntax) (what : String) : TacticM Nat := do
  let values := natLiterals stx
  if values.size != 1 then
    throwError "explicit_rw: {what} requires a canonical decimal numeral"
  return values[0]!

def indexedLocalDecl (index : Nat) : TermElabM LocalDecl := do
  let lctx ← getLCtx
  if index >= lctx.decls.size then
    throwError "explicit_rw: local_ref {index} is outside the current local context"
  let slot := lctx.decls.get! index
  let some decl := slot
    | throwError "explicit_rw: local_ref {index} does not name a declaration in the current local context"
  -- A PersistentArray slot is normally exactly its declaration index.  Keep
  -- this check explicit so malformed or stale contexts fail closed rather than
  -- accidentally resolving a neighbouring declaration.
  unless decl.index == index do
    throwError "explicit_rw: local_ref {index} resolved to a declaration with index {decl.index}"
  -- Auxiliary declarations are implementation details of the elaborator, not
  -- source hypotheses.  Ordinary implementation-detail declarations (including
  -- inaccessible `h✝`/`a✝` binders) remain valid and are addressed by index.
  if decl.isAuxDecl then
    throwError "explicit_rw: local_ref {index} names an auxiliary declaration, not a local hypothesis"
  return decl

def resolveIndexedLocal (stx : Syntax) : TermElabM Expr := do
  let index ← localRefIndex stx
  let decl ← indexedLocalDecl index
  let mut value := mkFVar decl.fvarId
  for (surface, projection) in (← localRefProjectionIndices stx) do
    if surface == 0 then
      throwError "explicit_rw: local_ref {index}: projection `.0` is invalid; projections are numbered from `.1`"
    let ty ← whnf (← inferType value)
    let .const structName _ := ty.getAppFn
      | throwError "explicit_rw: local_ref {index}: projection .{surface} requires a structure-valued local"
    let some info := getStructureInfo? (← getEnv) structName
      | throwError "explicit_rw: local_ref {index}: projection .{surface} is not a structure projection"
    if projection >= info.fieldNames.size then
      throwError "explicit_rw: local_ref {index}: projection .{surface} is out of bounds for {structName}"
    let fieldName := info.fieldNames[projection]!
    value ← try mkProjection value fieldName catch _ =>
      throwError "explicit_rw: local_ref {index}: invalid projection .{surface} for {structName}"
  return value

def elabIndexedLocalCore (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let value ← resolveIndexedLocal stx
  Term.ensureHasType expectedType? value

/- Resolve every `introduced_ref` before ordinary term elaboration.  This maps a
   handle to the indexed local declaration it denotes, preserving the same
   closed local-ref syntax and therefore the same direct lookup path. -/
partial def materializeIntroducedRefs (handles : IntroducedHandles) (stx : Syntax) : TacticM Syntax := do
  if stx.getKind == ``explicitRwIntroducedRefTerm then
    let raw := stx
    let handle ← checkedHandle raw[1] "introduced_ref handle"
    let some fvarId := handles.get? handle
      | throwError "explicit_rw: introduced_ref {handle} is unknown in this side proof"
    let decl ← FVarId.getDecl fvarId
    let indexed := raw.setArg 1 (Syntax.mkNumLit (toString decl.index))
    return indexed.setKind ``explicitRwLocalRefTerm
  let oldArgs := stx.getArgs
  let args ← oldArgs.mapM (materializeIntroducedRefs handles)
  if args == oldArgs then
    return stx
  return Syntax.node stx.getHeadInfo stx.getKind args

/--
Is this syntax node an antiquotation (`$x`)?

Antiquotations are admitted by every category's parser but mean nothing in a
trace, so each dispatch fallthrough checks for one and says so plainly. Round 6
fixed this in the term and step slots; round 7 found the recursive side-proof
slots added in the same round had re-introduced the "internal error" wording, so
the test now lives in one place.
-/
def isAntiquot (k : Name) : Bool :=
  let s := k.toString
  s.endsWith "antiquot" || s.endsWith "antiquot" || s == "«$»"


/-- `fun (x : α) => ... => body`: a typed binder group, desugared to nested
single binders so it can be built with ordinary quotations. -/
def mkTypedFun (xs : Array Ident) (ty body : Term) : TermElabM Term := do
  let mut r := body
  for x in xs.reverse do
    r ← `(fun ($x : $ty) => $r)
  return r

/-- `∀ (x : α), ... , body`, nested the same way. -/
def mkTypedForall (xs : Array Ident) (ty body : Term) : TermElabM Term := do
  let mut r := body
  for x in xs.reverse do
    r ← `(∀ ($x : $ty), $r)
  return r

/-- `∃ (x : α), ... , body`, nested the same way. -/
def mkTypedExists (xs : Array Ident) (ty body : Term) : TermElabM Term := do
  let mut r := body
  for x in xs.reverse do
    let b : TSyntax ``Lean.binderIdent := ⟨x.raw⟩
    r ← `(∃ ($b : $ty), $r)
  return r

/--
Collect an application whose head was written with `@` in the trace term.

The ordinary term parser gives `@foo a b` one application spine, so the
explicit marker controls insertion for the whole spine.  The whitelist parser
has an atom production for `@foo`, however, and its recursive quotation path
would elaborate `(@foo) a b`: the marker then applies only to the parenthesised
atom and the following arguments are elaborated as an ordinary application.
That silently reinserts implicit binders and is observably wrong for source
arguments such as `@xor_not_left _ b`.  Keep the source application's head and
arguments as syntax, then rebuild one ordinary Lean application spine with the
marker attached to its head.  No term text is parsed or reconstructed here;
the children are the already-validated whitelist syntax nodes.
-/
partial def explicitAppParts? (stx : Syntax) : Option (Syntax × Array Syntax) :=
  match stx.getKind with
  | ``explicitRwTermApp =>
    match explicitAppParts? stx[0] with
    | some (head, args) => some (head, args.push stx[1])
    | none => none
  | ``explicitRwTermIdent =>
    if stx[0].isNone then none else some (stx[1], #[])
  | _ => none

def mkExplicitApplication (head : Syntax) (args : Array Term) : Term := Id.run do
  let explicitHead := (Lean.mkNode ``Lean.Parser.Term.explicit
    #[Lean.mkAtom "@", head]).raw
  return ⟨(Lean.mkNode ``Lean.Parser.Term.app
    #[explicitHead, Lean.mkNullNode (args.map (·.raw))]).raw⟩

/--
Translate a trace term or type into ordinary Lean syntax.

Structural terms are rebuilt here; `lean_term(...)` passes its ordinary Lean
term syntax through. Both forms elaborate as ordinary terms, so implicits,
universes, instances and coercions behave as in any Lean proof. An unrecognised
structural node is an internal error, never a silent pass-through.
-/
partial def toTermCore (stx : Syntax) : TermElabM Term := do
  match stx.getKind with
  -- Atoms
  | ``explicitRwTermIdent =>
    let id : Term := ⟨stx[1]⟩
    if stx[0].isNone then return id else `(@$id)
  | ``explicitRwTermHole => `(_)
  | ``explicitRwTermNum => return ⟨stx[0]⟩
  | ``explicitRwLocalRefTerm | ``explicitRwIntroducedRefTerm =>
    -- Keep these syntax nodes intact.  Their dedicated term elaborator below
    -- resolves the fvar by LocalDecl.index, so turning them into an `ident`
    -- would reintroduce name lookup and make inaccessible declarations
    -- dependent on pretty-printed names.
    return ⟨stx⟩
  | ``explicitRwTermStr => return ⟨stx[0]⟩
  | ``explicitRwTermProp => `(Prop)
  | ``explicitRwTermNumType =>
    -- Rebuild the *notation node* rather than mapping the token to a name.
    -- This module is a `prelude` importing only `Lean.*`, so a hygienic
    -- quotation such as `(Real)` would resolve in this module's scope, where
    -- that constant does not exist; `ℕ ℤ ℚ` only appeared to work because
    -- `Nat`/`Int`/`Rat` are Lean core. Mathlib declares each of these as a
    -- notation whose syntax kind is `term<token>`, so reconstructing that node
    -- lets Mathlib's own elaborator resolve it in the caller's scope.
    let atom := stx[0][0]
    let tok := atom.getAtomVal
    return ⟨Syntax.node .none (Name.mkSimple s!"term{tok}") #[atom]⟩
  | ``explicitRwTermSortStar =>
    -- The alternation wraps its atom one node deeper, as every other
    -- alternation in this file does.
    if stx[0][0].getAtomVal == "Type*" then `(Type _) else `(Sort _)
  | ``explicitRwTermSort =>
    let isType := stx[0][0].getAtomVal == "Type"
    if stx[1].isNone then
      -- Bare `Sort` is `Sort _`; bare `Type` is `Type`, which must *not*
      -- unify with `Prop`.
      if isType then `(Type) else `(Sort _)
    else
      -- A named or numeric universe: `Type u`, `Sort 1`.
      let u : TSyntax `level := ⟨stx[1][0]⟩
      if isType then `(Type $u) else `(Sort $u)
  -- Grouping, application, projection
  | ``explicitRwTermApp => do
    match explicitAppParts? stx with
    | some (head, rawArgs) =>
      let args ← rawArgs.mapM toTermCore
      return mkExplicitApplication head args
    | none =>
      let f ← toTermCore stx[0]; let a ← toTermCore stx[1]; `($f $a)
  | ``explicitRwTermNamedArg => do
    -- The surrounding application is elaborated by Lean's normal term
    -- elaborator.  Preserve this one source-level named binder by changing
    -- only the syntax kind and recursively lowering its value; no expression
    -- payload is serialized or inspected here.
    let value ← toTermCore stx[3]
    let args := stx.getArgs.set! 3 value.raw
    return ⟨Syntax.node stx.getHeadInfo ``Lean.Parser.Term.namedArgument args⟩
  | ``explicitRwTermParen => do let t ← toTermCore stx[1]; `(($t))
  | ``explicitRwTermLean => return ⟨stx[1]⟩
  | ``explicitRwTermAscr => do
    let t ← toTermCore stx[1]; let ty ← toTermCore stx[3]; `(($t : $ty))
  | ``explicitRwTermPair => do
    let a ← toTermCore stx[1]; let b ← toTermCore stx[3]; `(($a, $b))
  | ``explicitRwTermProj => do
    let t ← toTermCore stx[0]
    let field := stx[2]
    if field.isOfKind ``Lean.Parser.Term.ident || field.getKind == `ident then
      let f : Ident := ⟨field⟩
      `($t.$f:ident)
    else
      let n : Syntax := field
      return ⟨Syntax.node .none ``Lean.Parser.Term.proj #[t.raw, Syntax.atom .none ".", n]⟩
  -- Binders
  | ``explicitRwTermFun => do
    let xs : Array Ident := stx[1].getArgs.map (⟨·⟩)
    let body ← toTermCore stx[4]
    if stx[2].isNone then
      `(fun $xs* => $body)
    else
      mkTypedFun xs (← toTermCore stx[2][1]) body
  | ``explicitRwTermFunParen => do
    let xs : Array Ident := stx[2].getArgs.map (⟨·⟩)
    mkTypedFun xs (← toTermCore stx[4]) (← toTermCore stx[7])
  | ``explicitRwTermForall => do
    let xs : Array Ident := stx[1].getArgs.map (⟨·⟩)
    let body ← toTermCore stx[4]
    if stx[2].isNone then
      `(∀ $xs*, $body)
    else
      mkTypedForall xs (← toTermCore stx[2][1]) body
  | ``explicitRwTermForallParen => do
    let xs : Array Ident := stx[2].getArgs.map (⟨·⟩)
    mkTypedForall xs (← toTermCore stx[4]) (← toTermCore stx[7])
  | ``explicitRwTermExists => do
    let body ← toTermCore stx[4]
    if stx[2].isNone then
      let mut r := body
      for a in stx[1].getArgs.reverse do
        let b : Ident := ⟨a⟩
        r ← `(∃ $b:ident, $r)
      return r
    else
      mkTypedExists (stx[1].getArgs.map (fun a => (⟨a⟩ : Ident))) (← toTermCore stx[2][1]) body
  | ``explicitRwTermExistsParen => do
    mkTypedExists (stx[2].getArgs.map (fun a => (⟨a⟩ : Ident))) (← toTermCore stx[4]) (← toTermCore stx[7])
  | ``explicitRwTermSetOf => do
    -- `{x | p}` is `setOf fun x => p`; building the application avoids depending
    -- on the set-builder notation being in scope.
    let x : Ident := ⟨stx[1]⟩
    let body ← toTermCore stx[4]
    if stx[2].isNone then
      `(setOf fun $x => $body)
    else
      let ty ← toTermCore stx[2][1]
      `(setOf fun ($x : $ty) => $body)
  -- Conditionals
  | ``explicitRwTermIte => do
    let c ← toTermCore stx[1]; let a ← toTermCore stx[3]; let b ← toTermCore stx[5]
    `(if $c then $a else $b)
  | ``explicitRwTermDIte => do
    -- Build `dite` directly: the surface `if h : c then …` notation expects a
    -- binder node this grammar does not produce.
    let h : Ident := ⟨stx[1]⟩
    let c ← toTermCore stx[3]; let a ← toTermCore stx[5]; let b ← toTermCore stx[7]
    `(dite $c (fun $h => $a) (fun $h => $b))
  -- Prefix and postfix
  | ``explicitRwTermNot => do let a ← toTermCore stx[1]; `(¬ $a)
  | ``explicitRwTermNeg => do let a ← toTermCore stx[1]; `(-$a)
  | ``explicitRwTermUp => do let a ← toTermCore stx[1]; `(↑$a)
  | ``explicitRwTermFunCoe => do let a ← toTermCore stx[1]; `(⇑$a)
  | ``explicitRwTermSetCoe => do let a ← toTermCore stx[1]; `(↥$a)
  | ``explicitRwTermInv => do let a ← toTermCore stx[0]; `($a⁻¹)
  -- Binary operators
  | ``explicitRwTermAdd => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a + $b)
  | ``explicitRwTermSub => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a - $b)
  | ``explicitRwTermMul => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a * $b)
  | ``explicitRwTermDiv => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a / $b)
  | ``explicitRwTermMod => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a % $b)
  | ``explicitRwTermPow => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ^ $b)
  | ``explicitRwTermSMul => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a • $b)
  | ``explicitRwTermComp => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ∘ $b)
  | ``explicitRwTermDvd => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ∣ $b)
  | ``explicitRwTermProd => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a × $b)
  | ``explicitRwTermMem => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ∈ $b)
  | ``explicitRwTermNotMem => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ∉ $b)
  | ``explicitRwTermSubset => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ⊆ $b)
  | ``explicitRwTermSSubset => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ⊂ $b)
  | ``explicitRwTermUnion => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ∪ $b)
  | ``explicitRwTermInter => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ∩ $b)
  | ``explicitRwTermSDiff => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a \ $b)
  | ``explicitRwTermLe => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ≤ $b)
  | ``explicitRwTermLt => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a < $b)
  | ``explicitRwTermGe => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ≥ $b)
  | ``explicitRwTermGt => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a > $b)
  | ``explicitRwTermEq => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a = $b)
  | ``explicitRwTermNe => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ≠ $b)
  | ``explicitRwTermIff => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ↔ $b)
  | ``explicitRwTermAnd => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ∧ $b)
  | ``explicitRwTermOr => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a ∨ $b)
  | ``explicitRwTermArrow => do let a ← toTermCore stx[0]; let b ← toTermCore stx[2]; `($a → $b)
  | ``explicitRwType => toTermCore stx[0]
  | k =>
    if isAntiquot k then
      throwError "explicit_rw: antiquotations are not admitted in a trace term."
    else
      throwError "explicit_rw: internal error: unhandled whitelisted node `{k}`"

/-- `toTermCore` in `TacticM`, which is where the step elaborators run. -/
def toTerm (stx : Syntax) (handles : IntroducedHandles := {}) : TacticM Term := do
  toTermCore (← materializeIntroducedRefs handles stx)



/-- Parse the child-index list out of an `explicitRwPos` node. -/
def parsePos (stx : Syntax) : Pos :=
  stx[2].getSepArgs.toList.map fun s => (s.isNatLit?.getD 0)

/-- Which location a step sequence applies to: the goal, or one hypothesis. -/
abbrev Target := Option FVarId

/-- The synthetic metavariables that exist right now, to diff against later. -/
def syntheticMVarSnapshot : TacticM (Std.HashSet MVarId) := do
  return (← getThe Term.State).syntheticMVars.toList.foldl (fun acc (m, _) => acc.insert m) {}

/--
Refuse a term that elaborated a tactic block.

This is the authoritative check, and it is *semantic*: every `by ...`, however
it got there — written directly, produced by a macro, by `notation`, or by a
custom term elaborator that calls `elabTerm` on it — registers a synthetic
metavariable whose `stx` *is* that `by` block. Matching on the recorded syntax
rather than on the kind is what makes this robust: a nested `elabTerm` can
register the block as `.postponed` instead of `.tactic`, so the kind alone
misses it, while the recorded syntax is the block either way.

`before` is a `syntheticMVarSnapshot` taken before the term was elaborated,
excluding metavariables that already existed — in particular the `by` block of
the proof that invoked `explicit_rw` itself.

Call this after elaborating and before synthetic metavariables are synthesized,
i.e. inside `Term.withSynthesize`'s body rather than after it.
-/
def checkNoPendingTactic (what : String) (idx? : Option Nat)
    (before : Std.HashSet MVarId) : TacticM Unit := do
  for (mvarId, decl) in (← getThe Term.State).syntheticMVars.toList do
    if before.contains mvarId then
      continue
    let isTactic :=
      match decl.kind with
      | .tactic .. => true
      | _ => decl.stx.getKind == ``Lean.Parser.Term.byTactic
    if isTactic then
      let msg := m!"{what} elaborates a tactic block. `explicit_rw` is product \
        code, so a trace may not run tactics inside a term: that would let a \
        tactic forbidden by the governing rule run where a lint over this module \
        could not see it. Write a closed term, or prove the lemma separately and \
        name it."
      match idx? with
      | some idx => stepError idx msg
      | none => throwError "explicit_rw: {msg}"

/--
Syntactic pre-check for a tactic block, kept as a second line of defence in
front of `checkNoPendingTactic`. It runs on macro-expanded syntax, so a macro
whose expansion is `by ...` is caught here too, and it gives a better message
because it names the offending node.
-/
partial def checkNoTacticBlock (what : String) (idx? : Option Nat) (stx : Syntax) :
    TacticM Unit := do
  -- Expand macros first: the written syntax of `SM` carries no `by` node, but
  -- its expansion does.
  let expanded ← try Elab.liftMacroM (expandMacros stx) catch _ => pure stx
  let offending? := find? stx <|> find? expanded
  if let some kind := offending? then
    let msg := m!"{what} contains a `{kind}` block. `explicit_rw` is product code, so a \
      trace may not embed a tactic block: it would let a tactic forbidden by the \
      governing rule run inside the product tactic, where a lint over this module \
      could not see it. Write a closed term, or prove the lemma separately and \
      name it."
    match idx? with
    | some idx => stepError idx msg
    | none => throwError "explicit_rw: {msg}"
where
  /-- The first `by`/tactic-sequence node in the tree, if any. -/
  find? (s : Syntax) : Option String := Id.run do
    let k := s.getKind
    if k == ``Lean.Parser.Term.byTactic then
      return some "by"
    if k == ``Lean.Parser.Tactic.tacticSeq || k == ``Lean.Parser.Tactic.tacticSeq1Indented then
      return some "tactic sequence"
    for child in s.getArgs do
      if let some r := find? child then
        return some r
    return none

/--
Resolve `stx` when it is a bare global constant, and `none` otherwise.

Used so that a class-polymorphic lemma's instance arguments stay open until the
position fixes them; anything with explicit arguments elaborates normally,
because those arguments usually pin the instance themselves.
-/
def resolveBareConst? (stx : Term) : TacticM (Option Name) := do
  let .ident _ _ _ _ := stx.raw | return none
  try
    let cs ← realizeGlobalConst stx.raw
    match cs with
    | [c] => return some c
    | _ => return none
  catch _ => return none

/--
The **single** strict elaboration entry point for every term this tactic
elaborates.

Round 6 found a false theorem admitted through the one elaboration site that
lacked a `sorry` guard: Lean's elaborators report many failures as *recoverable*
errors, logging a message and returning a `sorryAx`-typed expression rather than
throwing. A caller that does not check then proceeds on a term that means
nothing, and — because the surrounding `by` block is abandoned without an error —
the theorem is admitted at exit code 0. Fixing that per call site is how the hole
survived two rounds, so every site now goes through here.

The checks, in order: elaborate with error recovery **off**, optionally force
synthetic metavariables without postponing, instantiate, then reject the result
if it contains `sorry` (synthetic or not), any disallowed expression or level
metavariable, or if any error was logged while elaborating. Every rejection is
a step-indexed error.

`allowMVars` is for callers that legitimately need open metavariables. Lemma
and proposition replay close those themselves after matching at the recorded
position (`closeLemmaMVars`, `checkNoLevelMVars`, `synthesizeInstanceMVars`).
-/
def elabStrict (idx? : Option Nat) (what : String) (stx : Term)
    (expectedType? : Option Expr := none) (allowMVars := false)
    (synthesize := true) : TacticM Expr := do
  let errsBefore := (← Core.getMessageLog).hasErrors
  let e ← Term.withoutErrToSorry do
    let e ← match expectedType? with
      | some ty => Term.elabTermEnsuringType stx ty
      | none => Term.elabTerm stx none
    if synthesize then Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let e ← instantiateMVars e
  let fail (why : MessageData) : TacticM Expr :=
    match idx? with
    | some idx => stepError idx m!"{what} {why}"
    | none => throwError "explicit_rw: {what} {why}"
  if e.hasSorry || e.hasSyntheticSorry then
    return ← fail m!"failed to elaborate. (The error above says why.)"
  unless errsBefore do
    if (← Core.getMessageLog).hasErrors then
      return ← fail m!"failed to elaborate. (The error above says why.)"
  unless allowMVars do
    if e.hasExprMVar then
      return ← fail m!"still contains an unassigned metavariable after \
        elaboration:{indentExpr e}"
    if e.hasLevelMVar then
      return ← fail m!"still contains an unassigned universe level after \
        elaboration:{indentExpr e}"
  return e

/--
Elaborate a term to a proof of an equation or iff, returning `lhs`, `rhs` and a
proof of `lhs = rhs`, together with the metavariables introduced for the
lemma's own arguments so the caller can insist they all get assigned.
-/
def elabEquation (idx : Nat) (stx : Term) :
    TacticM (Expr × Expr × Expr × Array Expr) := do
  checkNoTacticBlock s!"the lemma term of this step" (some idx) stx
  let lemmaMsg := m!"`{stx}`"
  let snapshot ← syntheticMVarSnapshot
  -- Elaborate *without* forcing instance synthesis. A class-polymorphic lemma
  -- such as Mathlib's `add_zero` has an instance-implicit argument whose type is
  -- only fixed once the lemma's left side is unified with the subterm at the
  -- recorded position; synthesizing here would fail with "typeclass instance
  -- problem is stuck" on a metavariable, which is what plain `rw` avoids by
  -- postponing. Unification happens in `runRwStep`; `closeLemmaMVars` then
  -- synthesizes whatever remains.
  -- A bare constant is resolved directly rather than elaborated, so its
  -- instance-implicit arguments stay open as metavariables for unification to
  -- fix. Going through `Term.elabTerm` would try to synthesize them immediately
  -- and fail with "typeclass instance problem is stuck" on a metavariable,
  -- because nothing has yet said what type the lemma is being used at.
  let proof ←
    if let some name ← resolveBareConst? stx then
      let info ← getConstInfo name
      let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      pure (mkConst name lvls)
    else
      elabStrict (some idx) s!"the lemma term of this step" stx
        (allowMVars := true) (synthesize := false)
  checkNoPendingTactic s!"the lemma term of this step" (some idx) snapshot
  let proof ← instantiateMVars proof
  -- Elaboration runs under `withoutErrToSorry`, so a term that fails (an unknown
  -- identifier, say, because the lemma's module is not imported) throws Lean's
  -- own message with the step index attached, rather than coming back as
  -- `sorryAx` for a later check to misdiagnose.
  let type ← instantiateMVars (← inferType proof)
  -- Open the lemma's own leading binders as metavariables, so that matching the
  -- position determines them by unification rather than by search.
  let (mvars, _, type') ← forallMetaTelescopeReducing type
  let proof' := mkAppN proof mvars
  let (lhs, rhs, eqProof) ← asEquation idx lemmaMsg proof' type'
  -- Metavariables can also enter through elaboration of the written term itself
  -- (an implicit argument the syntax leaves open), not only through the
  -- telescope above. Collect both so none can escape into the goal.
  let fromTerm := (← instantiateMVars proof).collectMVars {} |>.result
  let fromType := (← instantiateMVars type).collectMVars {} |>.result
  let extra := (fromTerm ++ fromType).map Expr.mvar
  return (lhs, rhs, eqProof, mvars ++ extra)

/--
Elaborate the proof supplied to a `prop_true`/`prop_false` step.  Unlike an
equation lemma, a proposition rule has a proof type rather than an equality
type.  Open every leading binder as an ordinary metavariable, then match the
resulting proposition with the *selected* redex.  This is intentionally called
from inside `rewriteAt`: implicit arguments, explicit binders and instances are
therefore fixed by that redex before any remaining proof hypotheses are closed.
-/
def elabProposition (idx : Nat) (stx : Term) (sub : Expr) (truth : Bool) :
    TacticM (Expr × Array Expr) := do
  checkNoTacticBlock s!"the proposition proof of this step" (some idx) stx
  let snapshot ← syntheticMVarSnapshot
  let proof ←
    if let some name ← resolveBareConst? stx then
      let info ← getConstInfo name
      let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      pure (mkConst name lvls)
    else
      -- Keep placeholders and dependent instances open until the proposition
      -- is matched at `sub`: e.g. `NeZero.ne _` cannot synthesize
      -- `[NeZero ?n]` until that match fixes `?n`. `closeLemmaMVars` below
      -- still rejects anything matching and instance synthesis cannot close.
      elabStrict (some idx) s!"the proposition proof of this step" stx
        (allowMVars := true) (synthesize := false)
  checkNoPendingTactic s!"the proposition proof of this step" (some idx) snapshot
  let proof ← instantiateMVars proof
  let type ← instantiateMVars (← inferType proof)
  let (mvars, _, _) ← forallMetaTelescope type
  let proof' := mkAppN proof mvars
  let proofType ← instantiateMVars (← inferType proof')
  -- A Bool in proposition position is represented by its `= true` coercion.
  -- Keep that coercion explicit for proposition evidence so a recorded local
  -- `h : ¬b` can be replayed as `prop_false h` while the replacement remains
  -- the Bool constructor `false`, rather than changing a Bool into a Prop.
  let subType ← inferType sub
  let subIsBool ← isDefEq subType (mkConst ``Bool)
  let proposition ←
    if subIsBool then mkAppM ``Eq #[sub, mkConst ``true] else pure sub
  let expected :=
    if truth then proposition else mkApp (mkConst ``Not) proposition
  unless ← isDefEq proofType expected do
    let expected ← instantiateMVars expected
    stepError idx m!"proposition proof `{stx}` does not match the selected proposition at \
      position: expected a proof of{indentExpr expected}
      but its type is{indentExpr (← instantiateMVars proofType)}"
  let fromTerm := (← instantiateMVars proof).collectMVars {} |>.result
  let fromType := (← instantiateMVars type).collectMVars {} |>.result
  let extra := (fromTerm ++ fromType).map Expr.mvar
  return (proof', mvars ++ extra)

/--
Fail when any universe level metavariable survives in the given expressions.

Levels are determined by unifying the lemma's side with the subterm at the
recorded position. A leftover level metavariable means the trace did not pin it;
letting Lean default it would make the same trace replay differently depending
on elaboration order and on which modules happen to be imported.
-/
def checkNoLevelMVars (idx : Nat) (lemmaStx : MessageData) (es : Array Expr) :
    TacticM Unit := do
  for e in es do
    let e ← instantiateMVars e
    if e.hasLevelMVar then
      stepError idx m!"lemma {lemmaStx} still has an unassigned universe level \
        after matching at the given position. The position does not determine it, \
        and `explicit_rw` never defaults a level: that would make the replay \
        depend on the import context. Write the universe explicitly on the lemma \
        name, or fix the position."


/-- Run a definitional step at `pos` inside `e`, using `reduce` on the subterm. -/
def runDefeqStep (idx : Nat) (e : Expr) (pos : Pos) (what : MessageData)
    (reduce : Expr → TacticM Expr) : TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let newSub ← reduce sub
      unless ← isDefEq sub newSub do
        stepError idx m!"{what} at position {Pos.render pos} produced a term that is \
          not definitionally equal to the original.\nBefore{indentExpr sub}\n\
          After{indentExpr newSub}"
      return Replacement.defeq newSub)
    (fun pfx child sub => badPosError idx pos pfx child sub)

/-- Delta-unfold exactly the constant `c` at the head of `sub`. -/
def unfoldConst (idx : Nat) (c : Name) (sub : Expr) : TacticM Expr := do
  unless (← getEnv).contains c do
    stepError idx m!"`unfold {c}` names a constant that does not exist."
  -- Check the head before unfolding, so naming the wrong constant is reported as
  -- such rather than as whatever the subterm happened to reduce to.
  unless sub.getAppFn.constName? == some c do
    stepError idx m!"`unfold {c}` was applied where the head constant is \
      `{sub.getAppFn}`."
  -- `unfoldDefinition?` fails for plain definitions under `withReducible`, so
  -- fall back to default transparency. Both are delta steps on `c` alone.
  match ← withReducible (unfoldDefinition? sub) with
  | some e => return e
  | none =>
    match ← unfoldDefinition? sub with
    | some e => return e
    | none =>
      stepError idx m!"`unfold {c}` cannot unfold the subterm at this position; \
        `{c}` has no delta-reduction here."

/-- Eta-reduce `fun x => f x` to `f`, failing when the subterm is not an eta-redex. -/
def etaReduce (idx : Nat) (sub : Expr) : TacticM Expr := do
  let r := sub.eta
  if r == sub then
    stepError idx m!"`eta` at this position: the subterm is not an eta-redex."
  return r

/--
Reduce a structure projection applied to a constructor application, or a
projection-function application. This is projection reduction only: it refuses a
subterm that is not headed by a projection, so a `proj` step can never stand in
for an arbitrary `whnf`.
-/
def projReduce (idx : Nat) (sub : Expr) : TacticM Expr := do
  let isProjLike ←
    match sub with
    | .proj .. => pure true
    | _ =>
      match sub.getAppFn with
      | .const c _ => pure ((← getEnv).getProjectionFnInfo? c).isSome
      | _ => pure false
  unless isProjLike do
    stepError idx m!"`proj` at this position: the subterm is not a projection; \
      its head is `{sub.getAppFn}`."
  -- A raw `Expr.proj` reduces by `whnfCore` alone. A projection *function*
  -- application (what the elaborator produces for `s.field`) needs a delta step
  -- to unfold the function first; `whnfCore` performs no delta, so without this
  -- the step would always report "does not reduce".
  -- Require the projected structure to be a constructor application, so that the
  -- step really is a projection reduction. Without this, a class projection such
  -- as `HAdd.hAdd` (which `getProjectionFnInfo?` also reports) would let `proj`
  -- perform arbitrary unfolding.
  let env ← getEnv
  let structArg? : Option Expr :=
    match sub with
    | .proj _ _ b => some b
    | _ =>
      match sub.getAppFn with
      | .const c _ =>
        match env.getProjectionFnInfo? c with
        | some info => sub.getAppArgs[info.numParams]?
        | none => none
      | _ => none
  let some structArg := structArg?
    | stepError idx m!"`proj` at this position: the projection is not applied to a \
        structure argument."
  -- A projection may be recorded after its major argument has reduced through
  -- a definition to a constructor. `whnfCore` does not delta-reduce constants,
  -- so it rejects those genuine projection redexes even though the projection
  -- reducer below (and the kernel's definitional equality) can expose them.
  -- Use `whnf` here, then check for a complete constructor application before
  -- allowing `proj` to proceed. This remains restricted to projection redexes.
  let structArg ← whnf structArg
  let isCtor ← isConstructorApp structArg
  unless isCtor do
    stepError idx m!"`proj` at this position: the projection's argument is not a \
      constructor application, so there is nothing to reduce."
  let r ← whnfCore sub
  if r != sub then
    return r
  if let some unfolded ← unfoldDefinition? sub then
    let r ← whnfCore unfolded
    if r != sub then
      return r
  stepError idx m!"`proj` at this position: the projection does not reduce."

mutual

/-- Run a rewrite step at `pos` inside `e`, with its `with` clause if any. -/
partial def runRwStep (idx : Nat) (e : Expr) (pos : Pos) (stx : Term) (symm : Bool)
    (sideTacs : Array Syntax) (handles : IntroducedHandles := {}) :
    TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let (lhs, rhs, eqProof, mvars) ← elabEquation idx stx
      let (source, target) := if symm then (rhs, lhs) else (lhs, rhs)
      -- First match the actual lemma side against the recorded redex.  This
      -- also fixes instance-implicit arguments whose concrete instance is
      -- embedded in the redex (notably `dif_pos` after unfolding a
      -- definition opened under `Classical`).  Matching only the types first
      -- leaves such an instance metavariable untouched, and synthesizing it
      -- before the term match then incorrectly reports a missing instance.
      unless ← matchRewriteSource source sub do
        stepError idx m!"lemma `{stx}` does not match the subterm at \
          position {Pos.render pos}.\nExpected{indentExpr (← instantiateMVars source)}\n\
          but the subterm is{indentExpr sub}"
      Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      synthesizeInstanceMVars idx m!"`{stx}`" mvars sub
      -- Discharge the lemma's hypotheses with the `with` clause, in order. A
      -- hypothesis is a Prop-valued argument metavariable the position did not
      -- determine; anything left over is still an error below.
      let propMVars ← unassignedRewritePropMVars mvars
      if sideTacs.size > propMVars.size then
        stepError idx m!"the `with` clause supplies {sideTacs.size} proof(s) but lemma \
          `{stx}` has {propMVars.size} undetermined hypothesis(es) at this position."
      for h : i in [0 : sideTacs.size] do
        let .mvar mid := ← instantiateMVars propMVars[i]! | pure ()
        runSideProofOn idx (some i) sideTacs[i] mid handles
      Term.synthesizeSyntheticMVarsNoPostponing
      closeLemmaMVars idx m!"`{stx}`" mvars
      let eqProof ← instantiateMVars eqProof
      let target ← instantiateMVars target
      -- Universe levels are fixed by unifying the lemma's side with the subterm.
      -- One still unassigned means the position did not determine it; defaulting
      -- it would make the replay depend on elaboration order and on imports, so
      -- this is an error like any other unresolved argument.
      checkNoLevelMVars idx m!"`{stx}`" #[eqProof, target]
      let h ← if symm then mkEqSymm eqProof else pure eqProof
      return Replacement.eq target h)
    (fun pfx child sub => badPosError idx pos pfx child sub)

/-- Apply one parsed step to the current expression. -/
partial def runStep (idx : Nat) (e : Expr) (stx : Syntax)
    (handles : IntroducedHandles := {}) : TacticM Replacement := do
  -- Each alternation wraps its chosen form in a one-field node.
  let stx := stx[0]
  match stx.getKind with
  | ``explicitRwUnfold =>
    let pos := parsePos stx[2]
    let c ← realizeGlobalConstNoOverloadWithInfo stx[1]
    runDefeqStep idx e pos m!"`unfold {c}`" (unfoldConst idx c)
  | ``explicitRwRed =>
    let pos := parsePos stx[1]
    -- The alternation wraps the keyword in a `token.<kw>` node, so the atom
    -- itself is one level down.
    let kind := stx[0][0].getAtomVal
    match kind with
    | "beta" => runDefeqStep idx e pos m!"`beta`" fun sub => do
        let r := sub.headBeta
        if r == sub then
          stepError idx m!"`beta` at this position: the subterm is not a beta-redex."
        return r
    | "eta" => runDefeqStep idx e pos m!"`eta`" (etaReduce idx)
    | "proj" => runDefeqStep idx e pos m!"`proj`" (projReduce idx)
    | "zeta" => runDefeqStep idx e pos m!"`zeta`" fun sub => do
        let .letE _ _ v b _ := sub
          | stepError idx m!"`zeta` at this position: the subterm is not a `let`."
        return b.instantiate1 v
    | "iota" => runDefeqStep idx e pos m!"`iota`" fun sub => do
        -- Exactly ONE contraction, as the spec requires: `reduceRecMatcher?` is
        -- the single-step primitive. `whnfCore` would iterate to weak-head
        -- normal form and swallow the redexes that later recorded `iota` steps
        -- address, so a trace of N steps would fail at step 2.
        let fn := sub.getAppFn
        let isMatcher ← Meta.isMatcherApp sub
        let env ← getEnv
        let isRec :=
          match fn with
          | .const c _ => (env.find? c).any (· matches .recInfo _)
          | _ => false
        unless isMatcher || isRec do
          stepError idx m!"`iota` at this position: the subterm is not a matcher or \
            recursor application; its head is `{fn}`."
        match ← reduceRecMatcher? sub with
        | some r => return r
        | none =>
          stepError idx m!"`iota` at this position: the application does not reduce; \
            its major premise is not a constructor."
    | "" =>
      throwError "explicit_rw: antiquotations are not admitted in a trace step."
    | k => throwError "explicit_rw: internal error: unknown reduction keyword `{k}`"
  | ``explicitRwZetaLocal =>
    let index ← checkedHandle stx[2] "zeta_local local_ref index"
    let pos := parsePos stx[3]
    let decl ← indexedLocalDecl index
    let some value := decl.value?
      | stepError idx m!"`zeta_local local_ref {index}` names a local declaration without a let value."
    let localExpr := mkFVar decl.fvarId
    runDefeqStep idx e pos m!"`zeta_local local_ref {index}`" fun sub => do
      unless sub == localExpr do
        stepError idx m!"`zeta_local local_ref {index}` was applied where the selected subterm is not that exact local declaration."
      return value
  | ``explicitRwCongr | ``explicitRwCongr0 =>
    -- `congr i [steps] at pos`: rebuild the application at `pos` through its
    -- auto-generated congruence theorem, proving argument `i`'s equation from
    -- the nested steps. Unlike `congrArg`, this transports the arguments that
    -- *depend* on `i`, which is what makes a dependent position replayable.
    let argIdx := (stx[1].isNatLit?).getD 0
    let inner := stx[3].getSepArgs
    let pos := parsePos stx[5]
    rewriteAt e pos
      (fun sub => do
        let fn := sub.getAppFn
        let args := sub.getAppArgs
        if h : argIdx < args.size then
          let some congrThm ← mkCongrSimp? fn
            | stepError idx m!"`congr {argIdx}`: no congruence theorem could be \
                generated for the head{indentExpr fn}"
          -- Prove `args[i] = rhs` by replaying the nested steps at that argument.
          let target := args[argIdx]
          let mut cur := target
          let mut proof? : Option Expr := none
          for h2 : j in [0 : inner.size] do
            let r ← runStep idx cur inner[j] handles
            let next ← instantiateMVars r.newExpr
            match proof?, r.proof? with
            | none, p => proof? := p
            | some p, none => proof? := some p
            | some p, some q => proof? := some (← mkEqTrans p q)
            cur := next
          let argEq ← match proof? with
            | some p => instantiateMVars p
            | none => mkEqRefl target
          -- Apply the congruence theorem with the argument equation in place.
          let newArgs := args.set! argIdx cur
          let newSub := mkAppN fn newArgs
          let mut cargs : Array Expr := #[]
          let mut k := 0
          for kind in congrThm.argKinds do
            if k >= args.size then break
            match kind with
            | .fixed => cargs := cargs.push args[k]!
            | .eq =>
              cargs := cargs.push args[k]!
              cargs := cargs.push newArgs[k]!
              let eqPf ← if k == argIdx then pure argEq else mkEqRefl args[k]!
              cargs := cargs.push eqPf
            | .cast => cargs := cargs.push args[k]!
            | _ =>
              stepError idx m!"`congr {argIdx}`: the congruence theorem for this \
                head needs an argument kind `explicit_rw` does not build."
            k := k + 1
          let pf := mkAppN congrThm.proof cargs
          -- Check the built proof really proves what we claim before using it.
          let pfTy ← instantiateMVars (← inferType pf)
          let expected ← mkEq sub newSub
          unless ← isDefEq pfTy expected do
            -- Print with `pp.explicit`: when the step changes an argument the
            -- congruence theorem treats as fixed, the two sides differ *only* in
            -- implicit arguments, so the default rendering shows the same term
            -- twice and the refusal reads as nonsense.
            -- Render the two terms *eagerly* under `pp.explicit`: `MessageData`
            -- resolves its context when the error is finally displayed, so
            -- setting the option around the throw has no effect.
            let opts := (← getOptions).setBool `pp.explicit true
            let pfStr ← withOptions (fun _ => opts) do ppExpr pfTy
            let expStr ← withOptions (fun _ => opts) do ppExpr expected
            stepError idx m!"`congr {argIdx}`: the congruence theorem proves\
              \n  {pfStr}\nbut this step needs\n  {expStr}\n\
              (shown with `pp.explicit`, because the mismatch is in the \
              implicit arguments.)"
          return Replacement.eq newSub pf
        else
          stepError idx m!"`congr {argIdx}`: the application at this position has \
            only {args.size} argument(s).")
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwTransport =>
    -- `transport forall h [domain] body [body] at pos` is intentionally
    -- mechanical: both nested lists are replayed at their exact locations,
    -- and the stable handle is the only way body terms can name the newly
    -- introduced binder.
    let handle ← checkedHandle stx[2] "transport binder handle"
    if handles.contains handle then
      stepError idx m!"`transport forall {handle}` reuses an introduced handle already in scope"
    let domainSteps := stx[4].getSepArgs
    let bodySteps := stx[8].getSepArgs
    let pos := parsePos stx[10]
    rewriteAt e pos
      (fun sub => do
        let .forallE binderName binderType binderBody binderInfo := sub
          | stepError idx m!"`transport forall` at position {Pos.render pos} requires a `∀`"
        let replay (start : Expr) (steps : Array Syntax) (hs := handles) :
            TacticM Replacement := do
          let mut cur := start
          let mut proof? : Option Expr := none
          for h : j in [0 : steps.size] do
            let r ← runStep idx cur steps[j] hs
            let next ← instantiateMVars r.newExpr
            match proof?, r.proof? with
            | none, p => proof? := p
            | some p, none => proof? := some p
            | some p, some q => proof? := some (← mkEqTrans p q)
            cur := next
          return { newExpr := cur, proof? := proof? }
        let domainR ← replay binderType domainSteps
        let some domainEq := domainR.proof?
          | stepError idx m!"`transport forall {handle}` needs a propositional domain equality"
        withLocalDecl binderName binderInfo domainR.newExpr fun q => do
          let hSymm ← mkEqSymm domainEq
          let castArg ← mkAppM ``Eq.mp #[hSymm, q]
          let bodySeed := binderBody.instantiate1 castArg
          let bodyR ← replay bodySeed bodySteps (handles.insert handle q.fvarId!)
          dependentForallTransport binderName binderInfo binderType binderBody domainR
            (some q) (some bodyR))
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwIntroCtx =>
    -- A contextual introduction is a scoped replay, not a name-based `intro`.
    -- The recorder supplies all identity data; nested steps are relative to the
    -- introduced arrow body and may refer to its proof only by handle.
    let handle ← checkedHandle stx[1] "intro_ctx handle"
    if handles.contains handle then
      stepError idx m!"`intro_ctx {handle}` reuses an introduced handle already in scope"
    let domainPos := parsePos stx[3]
    let dependencies := stx[6].getSepArgs.map (·.isNatLit?.getD 0)
    let scopeId ← checkedHandle stx[9] "intro_ctx scope"
    let enterPos := parsePos stx[11]
    let exitPos := parsePos stx[13]
    let nested := stx[16].getSepArgs
    let pos := parsePos stx[18]
    unless domainPos == pos ++ [0] do
      stepError idx m!"`intro_ctx {handle}` domain position {Pos.render domainPos} does not \
        equal the arrow-domain position {Pos.render (pos ++ [0])}"
    unless enterPos == pos do
      stepError idx m!"`intro_ctx {handle}` scope {scopeId} enters at \
        {Pos.render enterPos} but the operation is at {Pos.render pos}"
    unless exitPos == pos do
      stepError idx m!"`intro_ctx {handle}` scope {scopeId} exits at \
        {Pos.render exitPos} but the operation is at {Pos.render pos}"
    rewriteAt e pos
      (fun sub => do
        let .forallE binderName binderType binderBody binderInfo := sub
          | stepError idx m!"`intro_ctx {handle}` at {Pos.render pos} requires an implication"
        unless ← isProp binderType do
          stepError idx m!"`intro_ctx {handle}` requires a proposition-valued domain"
        unless ← isProp binderBody do
          stepError idx m!"`intro_ctx {handle}` requires a proposition-valued body"
        if binderBody.hasLooseBVars then
          stepError idx m!"`intro_ctx {handle}` does not support a dependent arrow body"
        -- Dependencies are direct LocalDecl.index references. They are
        -- validation data, never a context search or a source-level term.
        let lctx ← getLCtx
        let actualDependencies :=
          (collectFVars {} binderType).fvarIds.filterMap fun fvarId =>
            lctx.find? fvarId |>.map (·.index)
        unless actualDependencies == dependencies do
          stepError idx m!"`intro_ctx {handle}` domain dependencies do not match the \
            recorded local indices"
        for dependency in dependencies do
          if dependency >= lctx.decls.size then
            stepError idx m!"`intro_ctx {handle}` dependency local index {dependency} \
              is outside the current local context"
          let some decl := lctx.decls.get! dependency
            | stepError idx m!"`intro_ctx {handle}` dependency local index {dependency} \
                is not a declaration"
          unless decl.index == dependency do
            stepError idx m!"`intro_ctx {handle}` dependency local index {dependency} \
              resolved to declaration index {decl.index}"
          if decl.isAuxDecl then
            stepError idx m!"`intro_ctx {handle}` dependency local index {dependency} \
              names an auxiliary declaration"
        withLocalDeclD binderName binderType fun h => do
          let scopedHandles := handles.insert handle h.fvarId!
          let mut cur := binderBody.instantiate1 h
          let mut proof? : Option Expr := none
          for hNested : j in [0 : nested.size] do
            let r ← runStep idx cur nested[j] scopedHandles
            let next ← instantiateMVars r.newExpr
            match proof?, r.proof? with
            | none, p => proof? := p
            | some p, none => proof? := some p
            | some p, some q => proof? := some (← mkEqTrans p q)
            cur := next
          let newAll ← mkForallFVars #[h] cur
          match proof? with
          | none =>
            unless ← isDefEq sub newAll do
              stepError idx m!"`intro_ctx {handle}` scoped replay changed the arrow \
                without producing a proof"
            return Replacement.defeq newAll
          | some proof =>
            let hAll ← mkLambdaFVars #[h] (← instantiateMVars proof)
            let arrowProof ← mkForallCongr hAll
            return Replacement.eq newAll arrowProof)
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwChange =>
    let pos := parsePos stx[2]
    let target ← toTerm stx[1] handles
    checkNoTacticBlock s!"the `change` term of this step" (some idx) target
    runDefeqStep idx e pos m!"`change {target}`" fun sub => do
      let ty ← inferType sub
      let snapshot ← syntheticMVarSnapshot
      let newSub ← elabStrict (some idx) s!"the `change` term of this step" target
        (expectedType? := some ty)
      checkNoPendingTactic s!"the `change` term of this step" (some idx) snapshot
      -- `elabTermEnsuringType` reports a type mismatch as a *recoverable* error
      -- and hands back `sorryAx`, which would then pass the defeq check against
      -- anything. A `change` whose term does not have the subterm's type must
      -- fail, since pinning that type is the whole point of the step.
      if newSub.hasSorry then
        stepError idx m!"the `change` term of this step does not elaborate at the \
          type of the subterm{indentExpr (← inferType sub)}"
      return newSub
  | ``explicitRwEq =>
    let pos := parsePos stx[4]
    let eqStx ← toTerm stx[1] handles
    checkNoTacticBlock s!"the `eq` equation of this step" (some idx) eqStx
    -- The `by` slot is the closed keyword `rfl` or `decide`, never a tacticSeq.
    let byKind := stx[3][0].getAtomVal
    -- Prove the stated equation with the named ordinary tactic, then rewrite.
    rewriteAt e pos
      (fun sub => do
        let snapshot ← syntheticMVarSnapshot
        let eqType ← elabStrict (some idx) s!"the `eq` equation of this step" eqStx
        checkNoPendingTactic s!"the `eq` equation of this step" (some idx) snapshot
        let some (_, lhs, rhs) := eqType.eq?
          | stepError idx m!"`eq {eqStx}` must state an equation `lhs = rhs`; it states\
              {indentExpr eqType}"
        unless ← isDefEq lhs sub do
          stepError idx m!"`eq {eqStx}`: its left-hand side does not match the subterm \
            at position {Pos.render pos}.\nExpected{indentExpr lhs}\n\
            but the subterm is{indentExpr sub}"
        let goal ← mkFreshExprSyntheticOpaqueMVar eqType
        let remaining ←
          match byKind with
          | "rfl" => Tactic.run goal.mvarId! (evalTactic (← `(tactic| rfl)))
          | "decide" => Tactic.run goal.mvarId! (evalTactic (← `(tactic| decide)))
          | k => stepError idx m!"`eq ... by {k}`: only `rfl` and `decide` are accepted."
        unless remaining.isEmpty do
          stepError idx m!"`eq {eqStx} by {byKind}`: the tactic left \
            {remaining.length} goal(s) open."
        let h ← instantiateMVars goal
        return Replacement.eq (← instantiateMVars rhs) h)
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwProp =>
    let truth := stx[0][0].getAtomVal == "prop_true"
    let term ← toTerm stx[1] handles
    let pos := parsePos stx[2]
    let sideTacs : Array Syntax :=
      if stx[3].isNone then #[] else stx[3][0][2].getSepArgs
    rewriteAt e pos
      (fun sub => do
        let (proof, mvars) ← elabProposition idx term sub truth
        -- Match first, then synthesize class-implicit binders before selecting
        -- proof-valued side evidence.  Otherwise an unresolved instance would
        -- occupy a `with [...]` slot ahead of the recorded proof hypothesis.
        synthesizeInstanceMVars idx m!"`{term}`" mvars sub
        -- A proposition rule can still have proof-valued binders.  They are
        -- discharged by the same closed, ordered side-proof language as an
        -- ordinary rewrite lemma; no hypothesis search is introduced here.
        let propMVars ← unassignedRewritePropMVars mvars
        if sideTacs.size > propMVars.size then
          stepError idx m!"the `with` clause supplies {sideTacs.size} proof(s) but proposition proof \
            `{term}` has {propMVars.size} undetermined hypothesis(es) at this position."
        for h : i in [0 : sideTacs.size] do
          let .mvar mid := ← instantiateMVars propMVars[i]! | pure ()
          runSideProofOn idx (some i) sideTacs[i] mid handles
        closeLemmaMVars idx m!"`{term}`" mvars
        let proof ← instantiateMVars proof
        let subType ← inferType sub
        let subIsBool ← isDefEq subType (mkConst ``Bool)
        let (replacement, eqProof) ←
          if subIsBool then
            if truth then
              pure (mkConst ``true, proof)
            else
              pure (mkConst ``false, ← mkAppM ``Bool.of_not_eq_true #[proof])
          else
            let eqProof ←
              if truth then
                mkAppM ``eq_true #[proof]
              else
                mkAppM ``eq_false #[proof]
            pure (if truth then mkConst ``True else mkConst ``False, eqProof)
        checkNoLevelMVars idx m!"`{term}`" #[eqProof]
        return Replacement.eq replacement eqProof)
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwRw =>
    let symm := !stx[0].isNone
    let term ← toTerm stx[1] handles
    let pos := parsePos stx[2]
    -- The optional `with [...]` clause, if present.
    let sideTacs : Array Syntax :=
      if stx[3].isNone then #[] else stx[3][0][2].getSepArgs
    runRwStep idx e pos term symm sideTacs handles
  | k =>
    if isAntiquot k then
      stepError idx m!"antiquotations are not admitted in a trace step."
    else
      throwError "explicit_rw: internal error: unexpected step kind `{k}`"

/-- Apply every step in order to the expression at `target`, rebuilding the goal. -/
partial def runSteps (steps : Array Syntax) (target : Target)
    (handles : IntroducedHandles := {}) : TacticM Unit := do
  -- Keep a hypothesis target's declaration stable while composing a multi-step
  -- replacement.  `MVarId.replace` necessarily rebinds the declaration after a
  -- propositional type change; continuing to read the original `FVarId` then
  -- feeds a stale free variable into the next step (the exact failure seen when
  -- `unfold Injective` is followed by nested `not_forall` rewrites).  Build the
  -- complete type/equality in the original context and replace the local once.
  -- Goal targets retain the existing per-step replacement semantics because
  -- they do not expose a declaration whose identity can go stale.
  if let some fvarId := target then
    let goal ← getMainGoal
    goal.withContext do
      let mut current ← instantiateMVars (← fvarId.getType)
      let mut proof? : Option Expr := none
      for h : idx in [0 : steps.size] do
        let stx := steps[idx]
        let r ←
          try
            runStep idx current stx handles
          catch ex => do
            let msg ← ex.toMessageData.toString
            if msg.startsWith "explicit_rw:" then
              throw ex
            else
              stepError idx ex.toMessageData
        let next ← instantiateMVars r.newExpr
        match proof?, r.proof? with
        | none, p => proof? := p
        | some p, none => proof? := some p
        | some p, some q => proof? := some (← mkEqTrans p q)
        current := next
      match proof? with
      | none =>
        let res ← goal.replaceLocalDeclDefEq fvarId current
        replaceMainGoal [res]
      | some h =>
        let h ← instantiateMVars h
        let newProof ← mkEqMP h (mkFVar fvarId)
        let res ← goal.replace fvarId newProof current
        replaceMainGoal [res.mvarId]
    return
  for h : idx in [0 : steps.size] do
    let stx := steps[idx]
    let goal ← getMainGoal
    goal.withContext do
      let e ← match target with
        | none => instantiateMVars (← goal.getType)
        | some fvarId => instantiateMVars (← fvarId.getType)
      -- Navigation errors are raised inside `rewriteAt`, which does not know the
      -- step index. Prefix any message that does not already carry it, so every
      -- failure names the step it came from.
      let r ←
        try
          runStep idx e stx handles
        catch ex => do
          let msg ← ex.toMessageData.toString
          if msg.startsWith "explicit_rw:" then
            throw ex
          else
            stepError idx ex.toMessageData
      let newE ← instantiateMVars r.newExpr
      match target with
      | none =>
        match r.proof? with
        | none => replaceMainGoal [← goal.replaceTargetDefEq newE]
        | some h => replaceMainGoal [← goal.replaceTargetEq newE (← instantiateMVars h)]
      | some fvarId =>
        match r.proof? with
        | none =>
          let res ← goal.replaceLocalDeclDefEq fvarId newE
          replaceMainGoal [res]
        | some h =>
          -- `Eq.mp h hyp : newType` transports the hypothesis forwards.
          let h ← instantiateMVars h
          let newProof ← mkEqMP h (mkFVar fvarId)
          let res ← goal.replace fvarId newProof newE
          replaceMainGoal [res.mvarId]

/--
Run the closing tactic of a `then` clause.

The parser already restricts this to the closed enumeration, so this only has to
dispatch. `exact <term>` additionally rejects a term containing a tactic block,
which is the one way a term could reintroduce arbitrary tactics.
-/
partial def runCloser (stx : Syntax) (handles : IntroducedHandles := {}) : TacticM Unit := do
  -- `stx` is the side proof itself; the caller has already unwrapped the
  -- optional `then` clause around it.
  let goal ← getMainGoal
  runSideProofOn 0 none stx goal handles
  replaceMainGoal []

/--
Run one side proof against `goal`, which it must close completely.

`which?` names the `with` entry for error messages; `none` means this is a
closing `then` clause. The `intro` and nested-`explicit_rw` cases are what make
this recursive: an implication-shaped side condition is discharged by
introducing its antecedents and replaying a nested trace under them.
-/
partial def runSideProofOn (idx : Nat) (which? : Option Nat) (stx : Syntax)
    (goal : MVarId) (handles : IntroducedHandles := {}) : TacticM Unit := do
  let where? : MessageData :=
    match which? with
    | some i => m!"the `with` entry {i + 1}"
    | none => m!"the closing `then` proof"
  let run (t : TSyntax `tactic) : TacticM Unit := do
    let remaining ← Tactic.run goal (evalTactic t)
    unless remaining.isEmpty do
      stepError idx m!"{where?} left {remaining.length} goal(s) open on\
        {indentExpr (← instantiateMVars (← goal.getType))}"
  -- `explicitRwSideTac` is a one-field wrapper around the category, and the
  -- nested-trace alternative keeps the `explicit_rw` keyword as its own node.
  let stx := if stx.getKind == ``explicitRwSideTac then stx[0] else stx
  match stx.getKind with
  | ``explicitRwSideRfl => run (← `(tactic| rfl))
  | ``explicitRwOperationalProofAtom =>
    match stx[0].getId.toString with
    | "rfl" => run (← `(tactic| rfl))
    | "true_intro" => run (← `(tactic| exact True.intro))
    | "equation_hypothesis" =>
      goal.withContext do
        let some proof ← Lean.Meta.Simp.dischargeEqnThmHypothesis? (← goal.getType)
          | stepError idx m!"the recorded equation-hypothesis discharge no longer applies in {where?}."
        goal.assign (← instantiateMVars proof)
    | atom => stepError idx m!"unknown closed proof operation `{atom}` in {where?}"
  | ``explicitRwSideDecide => run (← `(tactic| decide))
  | ``explicitRwSideOmega => run (← `(tactic| omega))
  | ``explicitRwSideNofun => run (← `(tactic| exact nofun))
  | ``explicitRwOperationalProofAssumption =>
    goal.withContext do
      let hyp : Ident := ⟨stx[1]⟩
      let fvarId ← getFVarId hyp.raw
      goal.assign (.fvar fvarId)
  | ``explicitRwOperationalProofAssumptionRef =>
    goal.withContext do
      let localIndex : TSyntax `num := ⟨stx[2]⟩
      let t ← `(explicitRwTerm| local_ref $localIndex:num)
      let t ← toTerm t.raw handles
      let val ← elabStrict (some idx) s!"the recorded local assumption" t
        (expectedType? := some (← goal.getType))
      goal.assign val
  | ``explicitRwSideExact =>
    goal.withContext do
      let t ← toTerm stx[1] handles
      checkNoTacticBlock s!"the `exact` term of a side proof" (some idx) t
      let snapshot ← syntheticMVarSnapshot
      let val ← elabStrict (some idx) s!"the `exact` term of a side proof" t
        (expectedType? := some (← goal.getType))
      checkNoPendingTactic s!"the `exact` term of a side proof" (some idx) snapshot
      goal.assign (← instantiateMVars val)
  | ``explicitRwSideClose =>
    goal.withContext do
      let t ← toTerm stx[2] handles
      checkNoTacticBlock s!"the `close` term of a side proof" (some idx) t
      let snapshot ← syntheticMVarSnapshot
      let val ← elabStrict (some idx) s!"the `close` term of a side proof" t
        (expectedType? := some (← goal.getType))
      checkNoPendingTactic s!"the `close` term of a side proof" (some idx) snapshot
      goal.assign (← instantiateMVars val)
  | ``explicitRwSideIntro =>
    let names : Array Name := stx[1].getArgs.map fun a => a.getId
    let (_, goal') ← goal.introN names.size names.toList
    runSideProofOn idx which? stx[3] goal' handles
  | ``explicitRwOperationalProofIntro =>
    let count := stx[1].isNatLit?.getD 0
    let names := (Array.range count).map fun i =>
      Name.mkSimple s!"__explicit_rw_v2_bound_{i}"
    let (_, goal') ← goal.introN names.size names.toList
    runSideProofOn idx which? stx[3] goal' handles
  | ``explicitRwSideIntroRef =>
    let handle ← checkedHandle stx[1] "intro_ref handle"
    if handles.contains handle then
      stepError idx m!"{where?} duplicates introduced handle {handle}."
    let (fvarId, goal') ← goal.intro1P
    runSideProofOn idx which? stx[3] goal' (handles.insert handle fvarId)
  | ``explicitRwOperationalProofNested =>
    -- Reclassify the same closed parser children as the tactic-level v2 node.
    -- The inserted empty optional location keeps the recursive proof scoped to
    -- this exact side goal; the v2 evaluator performs the actual operations.
    let nested : TSyntax `tactic := ⟨mkNode ``explicitRwOperational #[
      stx[0], stx[1], stx[2], stx[3], mkNullNode #[], stx[4]
    ]⟩
    run nested
  | ``explicitRwSideNested =>
    -- Replay a nested trace under the introduced hypotheses.
    let steps := stx[2].getSepArgs
    let remaining ← Tactic.run goal do
      runSteps steps none handles
      unless stx[4].isNone do
        let g ← getMainGoal
        runSideProofOn idx which? stx[4][0][1] g handles
        replaceMainGoal []
    unless remaining.isEmpty do
      stepError idx m!"{where?} left {remaining.length} goal(s) open on\
        {indentExpr (← instantiateMVars (← goal.getType))}"
  | k =>
    if isAntiquot k then
      stepError idx m!"antiquotations are not admitted in a side proof."
    else
      throwError "explicit_rw: internal error: unknown side proof `{k}`"

end

end Impl

open Impl in
@[tactic explicitRw]
def evalExplicitRw : Tactic := fun stx => do
  let steps := stx[2].getSepArgs
  let locStx := stx[4]
  let closeStx := stx[5]
  -- Resolve the location: the goal, or exactly one hypothesis.
  let target ← do
    if locStx.isNone then
      pure (none : Target)
    else
      match expandLocation locStx[0] with
      | .targets hyps goalToo =>
        if goalToo || hyps.size != 1 then
          throwError "explicit_rw: a trace applies to exactly one location: either the \
            goal, or `at h` for a single hypothesis."
        let fvarId ← getFVarId hyps[0]!
        pure (some fvarId : Target)
      | .wildcard =>
        throwError "explicit_rw: `at *` is not supported: positions are relative to one \
          location. Write one `explicit_rw` per location."
  runSteps steps target
  unless closeStx.isNone do
    match target with
    | none => runCloser closeStx[0][1]
    | some _ =>
      throwError "explicit_rw: the `then` closing form applies to the goal, but this \
        trace rewrites a hypothesis. Write the closing tactic on the next line."

end ExplicitLean.ExplicitRw
