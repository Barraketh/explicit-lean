module
prelude

public meta import ExplicitLean.ExplicitRw.Basic
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.Intro
public meta import Lean.Parser.Tactic

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

## Step forms

| Form                              | Meaning                                         |
| --------------------------------- | ----------------------------------------------- |
| `e at [..]`                       | rewrite left-to-right with the equation/iff `e`  |
| `← e at [..]`                     | rewrite right-to-left                            |
| `unfold c at [..]`                | delta-unfold the constant `c` (definitional)     |
| `beta at [..]`                    | beta-reduce the subterm (definitional)           |
| `eta at [..]`                     | eta-reduce the subterm (definitional)            |
| `proj at [..]`                    | reduce a structure projection (definitional)     |
| `zeta at [..]`                    | replace `let x := v; b` by `b[v/x]` (the only    |
|                                   | step that destroys a `let`)                      |
| `change t at [..]`                | replace by the defeq term `t` (definitional)     |
| `eq (lhs = rhs) by rfl at [..]`   | prove the equation with `rfl`/`decide`, rewrite  |
| `intro_ctx h at [..]`             | recognised, **not implemented**; fails by name   |

`e` is an ordinary term, so explicit arguments (`baz a b`), local hypotheses and
side-condition proofs are written as usual and elaborated as usual: implicits,
universes and instances are recovered by elaboration and unification.

Positions are raw child indices, *not* `conv`'s `arg n` numbering: `conv`'s
`arg` counts explicit arguments, while `0`/`1` here are the `fn`/`arg` children
of `Expr.app`, so `f a b` has `b` at `[1]` and `a` at `[0, 1]`.

## Closing form

`explicit_rw [...] then rfl` runs `rfl` on the remaining goal after the last
step. The closer is a **closed enumeration** — `rfl`, `decide`, `exact <term>` —
and `eq ... by` likewise accepts only `rfl` or `decide`. Omit the clause to leave
the goal open. `trivial` and bare `assumption` are excluded because both search
where the spec recorded an exact choice; the spec's `true_intro`,
`assumption:<name>` and `absurd:<hyp>` all render as `exact <term>`. `rfl` is the
ordinary `rfl` tactic (`Eq`/`Iff`/`HEq` reflexivity and `@[refl]` lemmas), not a
simp-backed one.

The `then` clause applies to the goal. A trace that rewrites a hypothesis leaves
the closer to the next line, which is where the spec's `absurd:<hyp>` form lands.

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
enumerations and every term is parsed in the whitelist grammar above, so no
tactic — simp-family or otherwise — can be written into a trace. What the
grammar cannot see is an identifier bound to a custom term elaborator, which is
indistinguishable from an ordinary constant at parse time and can run the
simplifier in `MetaM` without producing any `by` syntax. So:

> No trace written in this syntax can introduce a simp-family tactic, **provided
> the file it lives in declares no term elaborators** (`elab`, `macro`,
> `syntax`, `@[term_elab]`).

That proviso holds for generated Mathlib files by construction — a translated
file has no business declaring elaborators — and is to be enforced generator-side
by a lint (T4), not from inside this tactic. The synthetic-metavariable check in
`checkNoPendingTactic` remains as defence in depth for anything that slips past
the grammar.
-/

namespace ExplicitLean.ExplicitRw

open Lean Elab Tactic Meta

/-!
## The whitelisted term grammar

Every term a trace hands to `explicit_rw` — a rewrite lemma with its explicit
arguments, an `eq` equation, a `change` target, an `exact` closer — is parsed in
the `explicitRwTerm` category below rather than as a general Lean `term`.

This is a **whitelist enforced by the parser**, which is the point. Guarding a
general `term` means enumerating the shapes that can run tactics and hoping the
enumeration is complete; it is not. A `by` block is easy to spot, but a term
elaborator declared with `elab` can build its proof by calling the simplifier in
`MetaM` directly, producing neither `by` syntax nor a synthetic metavariable, so
nothing is left for a syntactic or a metavariable-based guard to see. A grammar
has no such escape: what it does not admit never reaches an elaborator at all.

Admitted: identifiers (dotted, optionally `@`-prefixed, including projection
suffixes such as `h.elim`), application of whitelisted terms, `_`, numeric and
string literals, parentheses, and type ascriptions `(t : T)` whose type is built
from the same grammar plus the binder-free connectives needed to *state* an
equation (`=`, `↔`, `¬`, `∧`, `∨`, `→`) and typed `∀`/`∃`/`fun` binders.

Not admitted, deliberately: `by`, `match`, `let`, `do`, `⟨…⟩` anonymous
constructors, `show … from`, `‹_›`, and `▸`.

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
A whitelisted term. One category covers terms and types alike: in dependent type
theory they are the same syntactic class, and splitting them only duplicated
every production.
-/
declare_syntax_cat explicitRwTerm

/-- Types are whitelisted terms; the alias keeps the step syntax readable. -/
syntax explicitRwType := explicitRwTerm

/-! ### Atoms -/

/-- An identifier, optionally `@`-prefixed; dotted names included. -/
syntax:max (name := explicitRwTermIdent) ("@")? ident : explicitRwTerm
/-- A placeholder for an argument the position determines. -/
syntax:max (name := explicitRwTermHole) "_" : explicitRwTerm
/-- A numeric literal. -/
syntax:max (name := explicitRwTermNum) num : explicitRwTerm
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
/-- Parentheses. -/
syntax:max (name := explicitRwTermParen) "(" explicitRwTerm ")" : explicitRwTerm
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

/--
`with [tac, ...]` — how a conditional lemma's hypotheses are discharged, in
order. Each entry is from a closed set: `rfl`, `decide`, `omega`, or
`exact <whitelisted term>`. `omega` is admitted because it is a decision
procedure for linear arithmetic, not a simp-family tactic; the spec records it
as a side close. Nothing else is accepted, for the same reason the closer set is
closed.
-/
syntax explicitRwSideTac :=
  &"rfl" <|> &"decide" <|> &"omega" <|> &"nofun" <|> (&"exact " explicitRwTerm)

/-- The optional side-condition clause of a rewrite step. -/
syntax explicitRwWith := " with " "[" explicitRwSideTac,* "]"

/-- A lemma rewrite, forwards or backwards: `foo a b at [1]`, `← bar at []`. -/
syntax explicitRwRw := ("← ")? explicitRwTerm explicitRwPos (explicitRwWith)?

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
`intro_ctx <name> at [1]` — the spec's contextual-simp step.

Recognised but **not implemented**: contextual rewriting changes what is in scope
for subsequent positions, which this tactic's single-location model does not
represent. It has syntax so that a trace containing it fails with an honest
"not implemented" error naming the kind, rather than being read as a lemma.
-/
syntax explicitRwIntroCtx := &"intro_ctx " ident explicitRwPos

/-- `change t at [1]` — last-resort definitional replacement, checked by defeq. -/
syntax explicitRwChange := "change " explicitRwTerm explicitRwPos

/--
The closers a trace may use, as a **closed enumeration**. `explicit_rw` is
product code, so it must not embed a free `tacticSeq`. The spec's `close` field
maps onto `rfl` and `decide`, plus `exact <term>` for every form that names
something: `true_intro` is `exact True.intro`, `assumption:<name>` is
`exact <name>`, `absurd:<hyp>` is `exact <hyp>.elim`.

Two tactics are deliberately **not** offered, both because they search where the
spec recorded an exact choice: `trivial` is a macro that tries several tactics in
turn, and bare `assumption` scans the whole local context, so it can succeed by
finding a *different* hypothesis than the one the trace recorded.

`rfl` here is the ordinary `rfl` tactic — `Eq`/`Iff`/`HEq` reflexivity and
`@[refl]` lemmas. It is not `simp`-backed and performs no simplification.
-/
syntax explicitRwCloser :=
  &"rfl" <|> &"decide" <|> &"nofun" <|> (&"exact " explicitRwTerm)

/--
`eq (2 + 3 = 5) by rfl at [1]` — a simproc-computed equation, proved by an
ordinary tactic. The spec's `by` field is exactly `rfl | decide`, so only those
two are accepted; see `explicitRwCloser` for why this is not a `tacticSeq`.
-/
syntax explicitRwEq := &"eq " explicitRwType " by " (&"rfl" <|> &"decide") explicitRwPos

/-- One step of an `explicit_rw` trace. -/
syntax explicitRwStep :=
  explicitRwUnfold <|> explicitRwRed <|> explicitRwIntroCtx <|> explicitRwChange <|>
  explicitRwEq <|> explicitRwRw

/-- Optional closing tactic: `explicit_rw [...] then rfl`. -/
syntax explicitRwClose := " then " explicitRwCloser

/--
Replay a recorded simp trace positionally, with no search.

Each step names a `SubExpr.Pos` child-index path and the rewrite to perform
there. See the module documentation for the step forms.
-/
syntax (name := explicitRw) "explicit_rw " "[" explicitRwStep,* "]"
  (Lean.Parser.Tactic.location)? (explicitRwClose)? : tactic

namespace Impl

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
Translate a whitelisted term or type into ordinary Lean syntax.

The whitelist is a syntactic restriction only: once a term has been shown to be
inside the grammar, it is elaborated exactly as the corresponding ordinary term
would be, so implicits, universes, instances and coercions behave as in any
Lean proof. This function is total on the grammar; an unrecognised node is an
internal error, never a silent pass-through to a general `term`.
-/
partial def toTermCore (stx : Syntax) : TermElabM Term := do
  match stx.getKind with
  -- Atoms
  | ``explicitRwTermIdent =>
    let id : Term := ⟨stx[1]⟩
    if stx[0].isNone then return id else `(@$id)
  | ``explicitRwTermHole => `(_)
  | ``explicitRwTermNum => return ⟨stx[0]⟩
  | ``explicitRwTermStr => return ⟨stx[0]⟩
  | ``explicitRwTermProp => `(Prop)
  | ``explicitRwTermNumType =>
    match stx[0][0].getAtomVal with
    | "ℕ" => `(Nat)
    | "ℤ" => `(Int)
    | "ℚ" => `(Rat)
    | "ℝ" => `(Real)
    | "ℂ" => `(Complex)
    | k => throwError "explicit_rw: internal error: unknown numeric type `{k}`"
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
    let f ← toTermCore stx[0]; let a ← toTermCore stx[1]; `($f $a)
  | ``explicitRwTermParen => do let t ← toTermCore stx[1]; `(($t))
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
    throwError "explicit_rw: internal error: unhandled whitelisted node `{k}`"

/-- `toTermCore` in `TacticM`, which is where the step elaborators run. -/
def toTerm (stx : Syntax) : TacticM Term := toTermCore stx



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
    for arg in s.getArgs do
      if let some r := find? arg then
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
Elaborate a term to a proof of an equation or iff, returning `lhs`, `rhs` and a
proof of `lhs = rhs`, together with the metavariables introduced for the
lemma's own arguments so the caller can insist they all get assigned.
-/
def elabEquation (idx : Nat) (stx : Term) : TacticM (Expr × Expr × Expr × Array Expr) := do
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
  let proof ← Term.withoutErrToSorry do
    if let some name ← resolveBareConst? stx then
      let info ← getConstInfo name
      let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      pure (mkConst name lvls)
    else
      instantiateMVars (← Term.elabTerm stx none)
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

/--
Discharge one hypothesis of a conditional lemma with one entry of a `with`
clause. The entry comes from a closed set (`rfl`, `decide`, `omega`,
`exact <whitelisted term>`), so a side condition cannot smuggle in a tactic any
more than a closer can. `omega` is admitted because it is a decision procedure
for linear arithmetic, not a member of the simp family.
-/
def runSideTac (idx : Nat) (which : Nat) (tacStx : Syntax) (goal : MVarId) :
    TacticM Unit := do
  let kind := tacStx[0][0].getAtomVal
  let run (t : TSyntax `tactic) : TacticM Unit := do
    let remaining ← Tactic.run goal (evalTactic t)
    unless remaining.isEmpty do
      stepError idx m!"the `with` entry {which + 1} left {remaining.length} goal(s) \
        open on the side condition{indentExpr (← goal.getType)}"
  match kind with
  | "rfl" => run (← `(tactic| rfl))
  | "decide" => run (← `(tactic| decide))
  | "omega" => run (← `(tactic| omega))
  | "nofun" => run (← `(tactic| exact nofun))
  | "exact" =>
    let t ← toTerm tacStx[0][1]
    run (← `(tactic| exact $t))
  | k => throwError "explicit_rw: internal error: unknown `with` entry `{k}`"

/--
Synthesize the instance-implicit arguments of a lemma once the position has
fixed their types, and check the result against the subterm.

Instance arguments are left open by `elabEquation` so that unification with the
subterm can determine them; this is where they are closed. A synthesized
instance that is not defeq to the one the subterm actually uses would silently
rewrite along a different algebraic structure, so that is a step-indexed error
rather than something to paper over.
-/
def synthesizeInstanceMVars (idx : Nat) (lemmaStx : MessageData)
    (mvars : Array Expr) (sub : Expr) : TacticM Unit := do
  for m in mvars do
    let m ← instantiateMVars m
    let .mvar mid := m | continue
    if ← mid.isAssigned then continue
    let ty ← instantiateMVars (← mid.getType)
    if ty.hasExprMVar then continue
    let some _ ← isClass? ty | continue
    match ← trySynthInstance ty with
    | .some val =>
      -- If the position already determined an instance, the synthesized one
      -- must agree with it; otherwise the replay would rewrite along a
      -- different structure than the recorder did.
      unless ← isDefEq m val do
        stepError idx m!"lemma {lemmaStx} needs an instance of{indentExpr ty}\n\
          but the instance synthesized here is not the one the subterm uses:\
          {indentExpr sub}"
      pure ()
    | .undef => pure ()
    | .none =>
      stepError idx m!"lemma {lemmaStx} needs an instance of{indentExpr ty}\n\
        which cannot be synthesized at this position."

/-- Run a rewrite step at `pos` inside `e`, with its `with` clause if any. -/
def runRwStep (idx : Nat) (e : Expr) (pos : Pos) (stx : Term) (symm : Bool)
    (sideTacs : Array Syntax) :
    TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let (lhs, rhs, eqProof, mvars) ← elabEquation idx stx
      let (source, target) := if symm then (rhs, lhs) else (lhs, rhs)
      -- Unify the *type* of the lemma's side with the subterm's type first. That
      -- is what fixes a class-polymorphic lemma's instance argument: once the
      -- carrier is known, synthesis has something to work with. Without this the
      -- instance metavariable blocks the defeq below and the step reports a
      -- spurious mismatch (`?a + 0` against `7 + 0`).
      let srcTy ← inferType source
      let subTy ← inferType sub
      discard <| isDefEq srcTy subTy
      synthesizeInstanceMVars idx m!"`{stx}`" mvars sub
      unless ← isDefEq source sub do
        stepError idx m!"lemma `{stx}` does not match the subterm at \
          position {Pos.render pos}.\nExpected{indentExpr (← instantiateMVars source)}\n\
          but the subterm is{indentExpr sub}"
      -- Discharge the lemma's hypotheses with the `with` clause, in order. A
      -- hypothesis is a Prop-valued argument metavariable the position did not
      -- determine; anything left over is still an error below.
      let propMVars ← mvars.filterM fun m => do
        match ← instantiateMVars m with
        | .mvar mid => do
          if ← mid.isAssigned then pure false else isProp (← instantiateMVars (← mid.getType))
        | _ => pure false
      if sideTacs.size > propMVars.size then
        stepError idx m!"the `with` clause supplies {sideTacs.size} proof(s) but lemma \
          `{stx}` has {propMVars.size} undetermined hypothesis(es) at this position."
      for h : i in [0 : sideTacs.size] do
        let .mvar mid := ← instantiateMVars propMVars[i]! | pure ()
        runSideTac idx i sideTacs[i] mid
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
  let isCtor ←
    match (← whnfCore structArg).getAppFn with
    | .const c _ => pure ((env.find? c).any (· matches .ctorInfo _))
    | _ => pure false
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

/-- Apply one parsed step to the current expression. -/
def runStep (idx : Nat) (e : Expr) (stx : TSyntax ``explicitRwStep) : TacticM Replacement := do
  let stx := stx.raw[0]
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
    | k => throwError "explicit_rw: internal error: unknown reduction keyword `{k}`"
  | ``explicitRwIntroCtx =>
    stepError idx m!"`intro_ctx` is a recorded step kind that `explicit_rw` does not \
      implement: contextual rewriting changes what is in scope for later positions, \
      which this tactic's single-location model does not represent. This trace \
      cannot be replayed; hand-write the proof instead."
  | ``explicitRwChange =>
    let pos := parsePos stx[2]
    let target ← toTerm stx[1]
    checkNoTacticBlock s!"the `change` term of this step" (some idx) target
    runDefeqStep idx e pos m!"`change {target}`" fun sub => do
      let ty ← inferType sub
      let snapshot ← syntheticMVarSnapshot
      let newSub ← Term.withSynthesize (postpone := .no) do
        let e ← Term.elabTermEnsuringType target ty
        checkNoPendingTactic s!"the `change` term of this step" (some idx) snapshot
        pure e
      let newSub ← instantiateMVars newSub
      -- `elabTermEnsuringType` reports a type mismatch as a *recoverable* error
      -- and hands back `sorryAx`, which would then pass the defeq check against
      -- anything. A `change` whose term does not have the subterm's type must
      -- fail, since pinning that type is the whole point of the step.
      if newSub.hasSorry then
        stepError idx m!"the `change` term of this step does not elaborate at the \
          type of the subterm{indentExpr (← inferType sub)}\n(Lean reports the \
          underlying error separately.)"
      return newSub
  | ``explicitRwEq =>
    let pos := parsePos stx[4]
    let eqStx ← toTerm stx[1]
    checkNoTacticBlock s!"the `eq` equation of this step" (some idx) eqStx
    -- The `by` slot is the closed keyword `rfl` or `decide`, never a tacticSeq.
    let byKind := stx[3][0].getAtomVal
    -- Prove the stated equation with the named ordinary tactic, then rewrite.
    rewriteAt e pos
      (fun sub => do
        let snapshot ← syntheticMVarSnapshot
        let eqType ← Term.withSynthesize (postpone := .no) do
          let e ← Term.elabType eqStx
          checkNoPendingTactic s!"the `eq` equation of this step" (some idx) snapshot
          pure e
        let eqType ← instantiateMVars eqType
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
  | ``explicitRwRw =>
    let symm := !stx[0].isNone
    let term ← toTerm stx[1]
    let pos := parsePos stx[2]
    -- The optional `with [...]` clause, if present.
    let sideTacs : Array Syntax :=
      if stx[3].isNone then #[] else stx[3][0][2].getSepArgs
    runRwStep idx e pos term symm sideTacs
  | k => throwError "explicit_rw: internal error: unexpected step kind `{k}`"

/-- Apply every step in order to the expression at `target`, rebuilding the goal. -/
def runSteps (steps : Array (TSyntax ``explicitRwStep)) (target : Target) : TacticM Unit := do
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
          runStep idx e stx
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
def runCloser (stx : Syntax) : TacticM Unit := do
  -- Each alternative wraps its keyword one level down: a bare keyword as
  -- `token.<kw>`, and `exact <term>` as a `group` whose child 0 is the atom.
  match stx[0][0].getAtomVal with
  | "rfl" => evalTactic (← `(tactic| rfl))
  | "decide" => evalTactic (← `(tactic| decide))
  | "nofun" => evalTactic (← `(tactic| exact nofun))
  | "exact" =>
    let t ← toTerm stx[0][1]
    checkNoTacticBlock "the closing `exact` term" none t
    let goal ← getMainGoal
    goal.withContext do
      let snapshot ← syntheticMVarSnapshot
      let val ← Term.withSynthesize (postpone := .no) do
        let e ← Term.elabTermEnsuringType t (← goal.getType)
        checkNoPendingTactic "the closing `exact` term" none snapshot
        pure e
      goal.assign (← instantiateMVars val)
      replaceMainGoal []
  | k =>
    throwError "explicit_rw: internal error: unknown closer `{k}`"

end Impl

open Impl in
@[tactic explicitRw]
def evalExplicitRw : Tactic := fun stx => do
  let steps := stx[2].getSepArgs.map fun s => (⟨s⟩ : TSyntax ``explicitRwStep)
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
