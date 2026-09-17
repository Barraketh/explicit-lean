# T2-explicit-rw result

Status: **complete**, all checks pass. Rounds 1-3: 7/7, 7/7, 3/3.
`explicit_rw` replays a simp trace positionally with no search (design and
syntax: `ExplicitLean/ExplicitRw/Tactic.lean`). Nothing in it reaches
`Lean.Meta.Simp`. For what a *trace* can introduce the guarantee is a
**conditional**, which is what is actually true: no trace written in this syntax
can introduce a simp-family tactic, *provided its file declares no term
elaborators* (see Round 3 item 1).

## Round 3 fixes
1. *(major)* Both previous guard layers keyed on **syntax**, so a term elaborator
   building its proof by calling the simplifier in `MetaM` produced neither a `by`
   node nor a synthetic metavariable, and passed — my round-2 claim that the guard
   caught a block "however it got there" was false. Terms are now parsed in a
   **whitelist grammar** (`explicitRwTerm`/`explicitRwType`): identifiers (dotted,
   optional `@`, `.field`), application, `_`, literals, parentheses, ascriptions,
   arithmetic and comparison operators, and the binder-free connectives
   (`= ↔ ¬ ∧ ∨ →`) plus typed `∀`/`∃`/`fun` binders needed to state an equation.
   No `by`, `match`, `let`, `do`, `⟨…⟩`, `show … from`, `‹_›`. Both `MetaM`
   attacks are now rejected **at parse time** — a whitelist has no
   elaboration-time escape. The metavariable check stays as defence in depth.
   **Residual hole, stated not papered over:** an identifier bound to a
   `@[term_elab]` elaborator is indistinguishable from a constant at parse time.
   Closed generator-side by the simp lint plus a ban on `elab`/`macro`/`syntax`
   in generated regions — **noted for T4, not implemented here**.
2. *(minor)* `mkLetFVars (usedLetOnly := false)`: a `let` whose body stops
   mentioning the bound variable is no longer elided, so the round-2 invariant
   ("only an explicit `zeta` destroys a `let`") now actually holds. Fixture with
   an unused binder added.
3. *(minor)* Counts corrected (65 fixture theorems, not 58). Six parser-rejected
   cases added, including both `MetaM` attacks; the `Negative.lean` section that
   promised a term-elaborator case now points at them. Positive `then exact`
   fixtures for **every** spec close form: `rfl`, `decide`, `exact True.intro`,
   `exact hb` (`assumption:<name>`), `exact hp.elim` (`absurd:<hyp>`, next line
   since `then` targets the goal). `decide` inherits Lean's closed-goal
   restriction, so emit it only for goals with no free variables.

## Rounds 1-2 fixes (all re-verified by the round-3 reviewer)
Round 2: the `let`-body branch abstracted by **value**, destroying the `let` when
the value was closed and capturing unrelated occurrences when it was a free
variable — now `withLetDecl` + `mkLetFVars`, abstracting by identity, and the new
fixtures were verified to **fail** against the old code; the tactic-block guard
was made semantic (superseded by the Round 3 grammar); `zeta` became a real step
kind; `intro_ctx` fails by name; bare `assumption` dropped (it searches).
Round 1: the `tacticSeq` hole, `proj` delta, `change` messages, the dependent
message, `import` linting, coverage claims. Details in git.

**Addendum (T1 cross-check).** The reported `IsEmpty` failure was **not** a
universe defect: `not_nonempty_iff` lives in `Mathlib.Logic.IsEmpty.Basic`, which
the failing file did not import, and `?m.2` was the `sorryAx`'s type. Level
handling was implemented as directed anyway (forced synthesis, step-indexed
error, never defaulted), plus `Sort*` fixtures at `Sort 0` and `Type`.

## Files (only owned; `ExplicitLean.lean`, `lakefile.toml` untouched)
`ExplicitLean/ExplicitRw{.lean,/Basic,/Tactic}.lean`; `test/ExplicitRw/` (5
fixtures + `RejectedSyntax/`: 12 cases, `expected.json`, README);
`Experiment/{check_explicit_rw,check_no_simp_family}.py`.

## Checks (re-run from scratch; Lean 4.32.2, pinned Mathlib)
- `lake build ExplicitLean.ExplicitRw` (clean): PASS, no warnings, 3.7 s
- `lake env lean test/ExplicitRw/<each>.lean` (5): PASS, no output, 1.8–2.3 s ea
- `python3 -B Experiment/check_explicit_rw.py`: PASS (5 + 12 cases), 35.7 s
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), 0.04 s

`#print axioms` on the 64 theorems of the four positive fixtures: **no
`sorryAx`** — 44 axiom-free, 8 `Quot.sound`, 11 `propext`, 1 both. (The 65th, in
`Negative.lean`, is a helper proved by `rw` whose leftover metavariable the
negative tests pin.) Each check was verified to *fail* when it should, including
the `let` fixtures against the pre-fix code.

## Limitations and open questions
- **Dependent positions are refused, not guessed**, each with a step-indexed
  message: dependent function argument and `∀` domain, binder types, `let`
  type/value, projection argument.
- `intro_ctx` recognised but unimplemented (T1 does not emit it); `at *` refused.
  Ordinary goals carry no `mdata`, so that fixture wraps the target.
- Generator must emit raw child indices, **not** `conv`'s `arg n` numbering.
  `explicit_rw` also matches up to reducible defeq, succeeding where plain `rw`
  fails (`conditional_conv`); confirm before the post-pass collapses such steps.
- `ExplicitLean.lean` needs `ExplicitLean.ExplicitRw` wired in at merge.
