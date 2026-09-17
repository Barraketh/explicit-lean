# T2-explicit-rw result

Status: **complete**, all checks pass. Rounds 1-6: 7/7, 7/7, 3/3, 4/4, 5/5, 6/6.
`explicit_rw` replays a simp trace positionally with no search (design and
syntax: `ExplicitLean/ExplicitRw/Tactic.lean`). Nothing in it reaches
`Lean.Meta.Simp`. What a *trace* can introduce is a **conditional** guarantee,
which is what is actually true: no trace in this syntax can introduce a
simp-family tactic, *provided its file declares no term elaborators* (Round 3.1).

## Round 6 fixes
1. *(CRITICAL — merge blocker)* The `eq` slot called `Term.elabType` with no
   guard, so an unresolvable equation logged a *recoverable* error, returned
   `sorryAx`, and the surrounding `by` block was abandoned **with no
   diagnostic**: `theorem false_thm : (1 : Nat) = 2` was admitted at exit 0. This
   is the hole round 5 fixed at the `change` site — and wrote the mechanism down
   — then did not apply twelve lines below; guarding sites one at a time is why
   it survived. All four sites now go through one **`elabStrict`**: error
   recovery off, synthesize without postponing, instantiate, then reject on
   `sorry`, synthetic sorry, leftover expression or universe metavariables, or
   any error logged while elaborating, each step-indexed.
   `test/ExplicitRw/Strict.lean` pins one rejected fixture per site, and
   **`check_explicit_rw.py` now computes the axiom audit itself** — any `sorryAx`
   in a fixture fails the run. That gate would have caught this while the suite
   was green.
2+4. *(major)* The discriminating sort fixture RESULT.md claimed did not exist,
   and the `ℝ`/`ℂ` fixtures put those tokens only in theorem *statements*, never
   inside a step — which is why defect 3 passed the suite. Both are now real:
   `change Type` at a `Prop` position must be **refused** (verified by reverting
   the fix and watching `Strict.lean` fail), and `ℝ`/`ℂ` appear inside steps.
3. *(major)* The numeric atoms mapped tokens to `Real`/`Complex` — hygienic
   names resolving in this `prelude` module's scope, where they do not exist
   (`ℕ ℤ ℚ` only worked because `Nat`/`Int`/`Rat` are core). The notation node is
   now rebuilt so Mathlib's elaborator resolves it at the call site.
5+6. *(minor)* An antiquotation is named rather than reported as an "internal
   error", and no longer produces a reduction-keyword message in the lemma slot,
   which pointed at the wrong step kind. The `change` error no longer promises an
   underlying diagnostic that was never printed.

**Recursive side proofs** (item 4). `with [...]` and `then` take a closed
*recursive* grammar: `rfl | decide | omega | nofun | exact <term> |
intro <ids> ; <proof> |` a nested `explicit_rw` with its own closer. A
conditional lemma's hypothesis is often implication-shaped — `ite_congr` and
`dite_congr` give `c → x = u` — which no flat enumeration can discharge.
Fixtures replay both. The sweep was re-run serially over 324 probes including
the two new slots: **zero escapes, 210/210 parse-rejected**; three the classifier
flagged were hand-checked and are parse errors too.
**The `congr` step** (T1 round-5 cross-check). The spec's `congr` kind had no T2
form, so cast-transport traces could not replay at all. `congr <i> [steps] at
[pos]` rebuilds the application through `Lean.Meta.mkCongrSimp?`'s theorem,
proving argument `i`'s equation from the nested steps; unlike `congrArg` it
transports the arguments that *depend* on `i`, so the type-equality proof rides
along. The built proof's type is checked against the claimed equation before
use. `Lean.Meta.CongrTheorems` sits outside `Lean.Meta.Tactic.Simp` and the lint
accepts it. Fixtures replay T1's `congr_cast` and `congr_nested_cast` verbatim
plus the `Function/Basic:390` shape.
## Rounds 1-5 fixes (each re-verified by the following reviewer)
**Round 5** *(4 major, 1 minor)*: the sort productions read their keyword one node
too shallow, so `Type`/`Type*`/`Sort*` collapsed to `Sort _`, which unifies with
anything including `Prop`. `iota` reduced many steps where the spec says one —
now `reduceRecMatcher?`. `ℕ ℤ ℚ ℝ ℂ` added as atoms; `nofun` added. **Addendum**:
a class-polymorphic lemma was elaborated before unification, so nothing fixed its
instance argument and `add_zero` was stuck; a bare constant is now resolved
directly and instances synthesized after the position fixes the carrier.
**Round 4** *(4 major, sufficiency)*: the grammar admitted far less than Lean
prints; it now covers conditionals, projection on parenthesised terms, untyped
binders, the operators Mathlib pp emits, set-builder, pairs and sorts. Two sweep
runs were discarded rather than reported (one against a mid-edit build, one
grading *any* error as rejection).
**Round 3** *(major)*: both guard layers keyed on syntax, so a term elaborator
calling the simplifier in `MetaM` produced neither a `by` node nor a synthetic
metavariable and passed — my claim that the guard caught a block "however it got
there" was false. Terms are now parsed in a whitelist grammar. **Residual hole,
stated not papered over:** an identifier bound to a `@[term_elab]` elaborator is
indistinguishable from a constant at parse time — closed generator-side, **T4**.
**Round 2**: the `let`-body branch abstracted by *value*, destroying the `let`
when the value was closed and capturing unrelated occurrences when it was free —
now `withLetDecl` + `mkLetFVars` by identity. `zeta` became a real kind; bare
`assumption` dropped (it searches).
**Round 1**: the `tacticSeq` hole in `then`/`eq … by` (now closed enumerations),
`proj` delta, `change` messages, `import` linting, coverage claims. See git.

## Files (only owned; `ExplicitLean.lean`, `lakefile.toml` untouched)
`ExplicitLean/ExplicitRw{.lean,/Basic,/Tactic}.lean`; `test/ExplicitRw/` (6
fixtures + `RejectedSyntax/`: 13 cases, `expected.json`, README);
`Experiment/{check_explicit_rw,check_no_simp_family}.py`.
## Checks (re-run from scratch; Lean 4.32.2, pinned Mathlib)
- `lake build ExplicitLean.ExplicitRw` (clean): PASS, no warnings, ~5 s
- `lake env lean test/ExplicitRw/<each>.lean` (7): PASS, no output, 1.6–2.5 s ea
- `python3 -B Experiment/check_explicit_rw.py`: PASS (7 + 13 cases), ~42 s,
  including the axiom audit it now computes: **111 theorems, no `sorryAx`**
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), 0.04 s

The axiom audit is no longer a claim in this file but a step in the runner, so
it is re-checked on every invocation rather than by the next reviewer. Each check
was verified to *fail* when it should, including the sort fixtures against the
pre-fix code and the escape sweep after each widening.
## Limitations and open questions
- **Dependent positions are refused, not guessed**, each step-indexed: dependent
  function argument and `∀` domain, binder types, `let` type/value, projection
  argument. A `congr` step is the way to replay one.
- `intro_ctx` recognised but unimplemented (T1 does not emit it); `at *` refused;
  `congr` nesting is two levels deep, which is what T1 emits.
- Recorded `lhs`/`rhs`/`to` must be **whitelist-dialect** terms. Rounds 4-5
  widened the grammar to what the pretty printer emits (`ℕ ℤ ℚ ℝ ℂ` included), but
  the dialect excludes `⟨…⟩`, `match`, `let`, `show … from` and big operators
  (`∑`), which a generator must re-render.
- Generator must emit raw child indices, **not** `conv`'s `arg n` numbering.
  `explicit_rw` also matches up to reducible defeq, succeeding where plain `rw`
  fails; confirm before the post-pass collapses such steps.
- `ExplicitLean.lean` needs `ExplicitLean.ExplicitRw` wired in at merge.
