# T2-explicit-rw result

Status: **complete**, all checks pass. Rounds 1-7: 7/7, 7/7, 3/3, 4/4, 5/5, 6/6,
4/4. Round 7 found no critical or major defect and the integration merge gate
passed on this side (5/5 T1 traces replay, 0 T2 mismatches).
`explicit_rw` replays a simp trace positionally with no search (design and syntax
in `ExplicitLean/ExplicitRw/Tactic.lean`). Nothing in it reaches
`Lean.Meta.Simp`. What a *trace* can introduce is a **conditional** guarantee,
which is what is actually true: no trace in this syntax can introduce a
simp-family tactic, *provided its file declares no term elaborators* (Round 3.1).

## Round 7 fixes (all diagnostics or bookkeeping)
1+2. *(minor)* Round 6 fixed the antiquotation wording in the term and step
   slots, but the recursive side-proof grammar added in that same round
   re-introduced "internal error" in four of six slots. One `isAntiquot`
   predicate now serves every fallthrough, pinned by three fixtures. The `congr`
   refusal compared terms differing only in *implicit* arguments, printing the
   same term twice; both are now rendered **eagerly** under `pp.explicit` —
   eagerly because `MessageData` resolves its context where the error is
   displayed, not where it is thrown.
3. *(minor, honesty)* The escape-sweep figures had **no committed artefact**:
   they came from scratch runs, two of which proved to be classifier errors
   rather than grammar defects — exactly the case where an artefact matters. The
   probe list now lives in `test/ExplicitRw/sweep/probes.json` and
   `check_explicit_rw.py` runs it, so the count is produced by the check, not
   asserted here. An escape must be stopped by the **parser**; the only two that
   cannot be (`admit`, `$x`) are listed explicitly, so anything else surviving
   the parser fails the run.
4. *(trivial)* The fixture count said 6; there are 7.

## Round 6 fixes
1. *(CRITICAL — merge blocker)* The `eq` slot elaborated with no guard, so an
   unresolvable equation logged a *recoverable* error, returned `sorryAx`, and
   the `by` block was abandoned **with no diagnostic**:
   `theorem false_thm : (1 : Nat) = 2` was admitted at exit 0. This is the hole
   round 5 fixed at the `change` site — and wrote the mechanism down — then did
   not apply twelve lines below; guarding sites one at a time is why it survived.
   All four sites now go through one **`elabStrict`**: error recovery off,
   synthesize without postponing, instantiate, then reject on `sorry`, synthetic
   sorry, leftover expression or universe metavariables, or any error logged
   while elaborating, each step-indexed. `Strict.lean` pins one rejected fixture
   per site, and **`check_explicit_rw.py` computes the axiom audit itself** — any
   `sorryAx` fails the run, the gate that would have caught this.
2-4. *(major)* The discriminating sort fixture this file claimed did not exist,
   and the `ℝ`/`ℂ` fixtures put those tokens only in theorem *statements*, never
   inside a step — which is why the atom bug passed the suite. Both are now real
   (`change Type` at a `Prop` position must be **refused**, verified by reverting
   the fix). The atoms had mapped to `Real`/`Complex`, hygienic names resolving
   in this `prelude` module's scope where they do not exist; the notation node is
   now rebuilt so Mathlib's elaborator resolves it at the call site.
5+6. *(minor)* Antiquotations named rather than "internal error"; the `change`
   error no longer promises a diagnostic that was never printed.
**Recursive side proofs** (item 4). `with [...]` and `then` take a closed
*recursive* grammar: `rfl | decide | omega | nofun | exact <term> |
intro <ids> ; <proof> |` a nested `explicit_rw`. An implication-shaped hypothesis
— `ite_congr`/`dite_congr` give `c → x = u` — needs the `intro` form.
**The `congr` step** (T1 round-5 cross-check). The spec's `congr` kind had no T2
form, so cast-transport traces could not replay. `congr <i> [steps] at [pos]`
rebuilds the application through `Lean.Meta.mkCongrSimp?`'s theorem; unlike
`congrArg` it transports the arguments that *depend* on `i`. The built proof's
type is checked against the claimed equation before use — what refuses every
unsound rebuild the round-7 reviewer constructed. Fixtures replay T1's
`congr_cast`, `congr_nested_cast` and the `Function/Basic:390` shape.

## Rounds 1-5 fixes (each re-verified by the following reviewer)
**Round 5**: sort productions read their keyword one node too shallow, so
`Type`/`Type*`/`Sort*` collapsed to `Sort _`, which unifies with anything
including `Prop`; `iota` reduced many steps where the spec says one; `ℕ ℤ ℚ ℝ ℂ`
and `nofun` added. **Addendum**: a class-polymorphic lemma was elaborated before
unification, so `add_zero` was stuck — instances are now synthesized only after
the position fixes the carrier.
**Round 4**: the grammar admitted far less than Lean prints; it now covers
conditionals, projection on parenthesised terms, untyped binders, the operators
Mathlib pp emits, set-builder, pairs and sorts.
**Round 3** *(major)*: both guard layers keyed on syntax, so a term elaborator
calling the simplifier in `MetaM` produced neither a `by` node nor a synthetic
metavariable and passed — my claim that the guard caught a block "however it got
there" was false. Terms are now parsed in a whitelist grammar. **Residual hole,
stated not papered over:** an identifier bound to a `@[term_elab]` elaborator is
indistinguishable from a constant at parse time — closed generator-side (**T4**).
**Round 2**: the `let`-body branch abstracted by *value*. **Round 1**: the
`tacticSeq` hole in `then`/`eq … by`, now closed enumerations. Details in git.

## Files (only owned; `ExplicitLean.lean`, `lakefile.toml` untouched)
`ExplicitLean/ExplicitRw{.lean,/Basic,/Tactic}.lean`; `test/ExplicitRw/` (7
fixtures + `RejectedSyntax/`: 13 cases; `sweep/`: probe list + README);
`Experiment/{check_explicit_rw,check_no_simp_family}.py`.
## Checks (re-run from scratch; Lean 4.32.2, pinned Mathlib)
- `lake build ExplicitLean.ExplicitRw` (clean): PASS, no warnings, ~5 s
- `lake env lean test/ExplicitRw/<each>.lean` (7): PASS, no output, 1.6–2.5 s ea
- `python3 -B Experiment/check_explicit_rw.py`: PASS (7 + 13 cases), ~6 min,
  including two gates it now computes rather than this file asserting them —
  the **axiom audit** (111 theorems, no `sorryAx`) and the **escape sweep**
  (2 of 6 slots by default). `T2_FULL_SWEEP=1` sweeps all six: **330 escape
  probes all rejected, 318 by the parser and 12 at elaboration (only `admit` and
  `$x`, which no parser can stop); 120 benign all parse**
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), 0.04 s

Both gates were verified to *fail* when they should: the axiom audit on an
injected `sorry` and on a new axiom, the sweep on a planted escape (the first
version of that check counted any error as a rejection and let the plant pass).
## Limitations and open questions
- **Dependent positions are refused, not guessed**, each step-indexed: dependent
  function argument and `∀` domain, binder types, `let` type/value, projection
  argument. A `congr` step is the way to replay one. `intro_ctx` is recognised
  but unimplemented (T1 does not emit it); `at *` is refused; `congr` nesting is
  two levels deep, which is what T1 emits.
- Recorded `lhs`/`rhs`/`to` must be **whitelist-dialect** terms. Rounds 4-5
  widened the grammar to what the pretty printer emits (`ℕ ℤ ℚ ℝ ℂ` included), but
  the dialect excludes `⟨…⟩`, `match`, `let`, `show … from` and big operators
  (`∑`), which a generator must re-render.
- Generator must emit raw child indices, **not** `conv`'s `arg n` numbering.
  `explicit_rw` also matches up to reducible defeq, succeeding where plain `rw`
  fails; confirm before the post-pass collapses such steps.
- `ExplicitLean.lean` needs `ExplicitLean.ExplicitRw` wired in at merge.
