# T2-explicit-rw result

Status: **complete**, all checks pass. Rounds 1-5: 7/7, 7/7, 3/3, 4/4, 5/5.
`explicit_rw` replays a simp trace positionally with no search (design and
syntax: `ExplicitLean/ExplicitRw/Tactic.lean`). Nothing in it reaches
`Lean.Meta.Simp`. What a *trace* can introduce is a **conditional** guarantee,
which is what is actually true: no trace in this syntax can introduce a
simp-family tactic, *provided its file declares no term elaborators* (Round 3.1).

## Round 5 fixes
No safety defect: 385 escape probes across 77 constructs and five slots were all
rejected, and `then`/`with`/`eq … by` were shown closed by *hijacking*
`omega`/`rfl`/`decide` rather than by inspection.
1+2. *(major, one root)* The sort productions read their keyword at `stx[0]`
   instead of `stx[0][0]`, so `Type`, `Type*` and `Sort*` all collapsed to
   `Sort _` — an unconstrained universe metavariable that unifies with anything,
   `Prop` included. **The fixtures that claimed to cover sorts contained no sort
   spelling**, which is why nothing caught it. Fixing the index alone was not
   enough: `elabTermEnsuringType` reports a sort mismatch as *recoverable* and
   hands back `sorryAx`, which then passed the defeq check, so `change` now
   rejects a term that failed to elaborate. The new fixtures include the
   **discriminating** case — `change Type` at a `Prop` position must be *refused*
   — because with `Sort _` every accepting case passes either way.
3. *(major)* `iota` used `whnfCore`, which iterates to weak-head normal form and
   swallows the redexes later recorded `iota` steps address, so a trace of N
   steps would fail at step 2. It now uses `reduceRecMatcher?`, the single-step
   primitive; a nested-matcher fixture needs two distinct `iota` steps, and the
   recursor fixture a following `beta` that would be a no-op if `iota` had
   normalised.
4. *(major)* `ℕ ℤ ℚ ℝ ℂ` are lexer *tokens*, not identifiers, so they never
   reached the category. Added as atoms, verified in all five slots.
5. *(minor, spec)* The `nofun` close form, in both the `then` and `with [...]`
   sets, with a fixture closing an impossible constructor equation.

**Addendum (T1 round-4 cross-check).** A class-polymorphic lemma was elaborated
*before* unification with the subterm, so nothing fixed its instance argument and
`add_zero` failed with "typeclass instance problem is stuck" — blocking many
traces, since it opens several T1 fixtures. A bare constant is now resolved
directly, leaving instance arguments open; the lemma's type is unified with the
subterm's first, fixing the carrier and hence the instance path, and synthesis
runs only then, erroring if the result is not the instance the subterm uses.
Fixtures: `add_zero` at `ℕ` and under a binder, `mul_one` on a `Monoid` variable,
`mul_comm` at `ℝ`.
## Rounds 1-4 fixes (each re-verified by the following reviewer)
**Round 4** *(4 major, sufficiency)*: the grammar admitted far less than Lean
prints. It now covers `if _ then _ else _`, projection on any parenthesised term
(needed by `absurd:<hyp>`), untyped binders, prefix/postfix/binary operators,
set-builder, pairs and sorts; terms and types became one category. Safety was
re-verified, not assumed: 216 probes re-run, all 140 escapes still rejected; two
earlier sweep runs were discarded rather than reported (one against a mid-edit
build, one grading *any* error as rejection). Also added `iota`, the `with [...]`
clause, and `eq_true`/`eq_false` fixtures.
**Round 3** *(major)*: both guard layers keyed on syntax, so a term elaborator
calling the simplifier in `MetaM` produced neither a `by` node nor a synthetic
metavariable and passed — my claim that the guard caught a block "however it got
there" was false. Terms are now parsed in a whitelist grammar; the metavariable
check remains as defence in depth. **Residual hole, stated not papered over:** an
identifier bound to a `@[term_elab]` elaborator is indistinguishable from a
constant at parse time — closed generator-side by the simp lint plus a ban on
`elab`/`macro`/`syntax` in generated regions, **noted for T4, not here**.
**Round 2**: the `let`-body branch abstracted by *value*, destroying the `let`
when the value was closed and capturing unrelated occurrences when it was free —
now `withLetDecl` + `mkLetFVars` by identity, with fixtures verified to **fail**
against the old code. `zeta` became a real kind; `intro_ctx` fails by name; bare
`assumption` dropped (it searches). **Round 1**: the `tacticSeq` hole in
`then`/`eq … by` (now closed enumerations), `proj` delta, `change` messages, the
dependent-function message, `import` linting, coverage claims. **Addendum (T1
round-2)**: the `IsEmpty` failure was **not** a universe defect —
`not_nonempty_iff` was simply not imported. Details in git.

## Files (only owned; `ExplicitLean.lean`, `lakefile.toml` untouched)
`ExplicitLean/ExplicitRw{.lean,/Basic,/Tactic}.lean`; `test/ExplicitRw/` (6
fixtures + `RejectedSyntax/`: 13 cases, `expected.json`, README);
`Experiment/{check_explicit_rw,check_no_simp_family}.py`.
## Checks (re-run from scratch; Lean 4.32.2, pinned Mathlib)
- `lake build ExplicitLean.ExplicitRw` (clean): PASS, no warnings, 5.4 s
- `lake env lean test/ExplicitRw/<each>.lean` (6): PASS, no output, 1.8–2.6 s ea
- `python3 -B Experiment/check_explicit_rw.py`: PASS (6 + 13 cases), 41.9 s
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), 0.04 s

`#print axioms` on the 100 theorems of the five positive fixtures: **no
`sorryAx`** — 68 axiom-free, the rest `propext`/`Quot.sound`/`Classical.choice`
(the last only in the `ℝ` fixtures, which any `Real` proof needs). Each check was
verified to *fail* when it should, including the sort and `let` fixtures against
the pre-fix code.

## Limitations and open questions
- **Dependent positions are refused, not guessed**, each with a step-indexed
  message: dependent function argument and `∀` domain, binder types, `let`
  type/value, projection argument.
- `intro_ctx` recognised but unimplemented (T1 does not emit it); `at *` refused.
  Ordinary goals carry no `mdata`, so that fixture wraps the target.
- Recorded `lhs`/`rhs`/`to` must be **whitelist-dialect** terms. Rounds 4-5
  widened the grammar to what the pretty printer emits (`ℕ ℤ ℚ ℝ ℂ` included), but
  the dialect excludes `⟨…⟩`, `match`, `let`, `show … from` and big operators
  (`∑`), which a generator must re-render.
- Generator must emit raw child indices, **not** `conv`'s `arg n` numbering.
  `explicit_rw` also matches up to reducible defeq, succeeding where plain `rw`
  fails (`conditional_conv`); confirm before the post-pass collapses such steps.
- `ExplicitLean.lean` needs `ExplicitLean.ExplicitRw` wired in at merge.
