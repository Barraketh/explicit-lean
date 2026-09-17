# T2-explicit-rw result

Status: **complete**, all checks pass. Rounds 1-8: 7/7, 7/7, 3/3, 4/4, 5/5, 6/6,
4/4, 9/9. Rounds 7-8 found **no soundness defect in the tactic**; round 8's were
in the checks and documentation. Round 8 also retracted round 7's two
"T1-side" merge findings as reviewer errors, so the merge questions were all
T2's own and are now closed.
`explicit_rw` replays a simp trace positionally with no search (design and syntax
in `ExplicitLean/ExplicitRw/Tactic.lean`). Nothing in it reaches
`Lean.Meta.Simp`. What a *trace* can introduce is a **conditional** guarantee,
which is what is actually true: no trace in this syntax can introduce a
simp-family tactic, *provided its file declares no term elaborators* (Round 3.1).

## Round 8 fixes
1. *(major)* The axiom audit grepped for `sorryAx`, enforcing only half the
   governing rule: a theorem depending on a freshly declared `axiom` prints that
   axiom's name and **no** `sorryAx`, so it passed. The audit now parses every
   report and fails unless the axiom set is within
   `{propext, Quot.sound, Classical.choice}`, and fails if the report count does
   not match the theorem count. Verified with the injection **inside** the
   fixture namespace, where a real regression would sit: previously exit 0, now a
   named failure. Round 7's verification had appended after the `end`, so the
   file failed to compile for an unrelated reason and the gate was never
   exercised — this file's claim that it had been verified was wrong.
2. *(major)* Two of the six sweep slots rewrote at `[0,1]` against the goal
   `True`, which has no children, so every probe died on the *position* before
   its term was elaborated — four rejections credited on unrelated evidence. Each
   slot now carries a goal with the structure its position needs, and both reject
   `admit` **by name**. The post-parse branch now requires a non-zero exit and an
   attributable message, and the template's trailing `trivial` — absorbed as an
   *argument*, since application spans lines — is gone.
3. *(major)* Inaccessible hypotheses need no new syntax: `rename_i` is ordinary
   Lean and already worked. The convention is now documented precisely (it names
   the last *n* inaccessibles in context order, so a generator names all of them
   up to the one it needs) with a fixture using the **earlier** of two.
4. *(major)* The step-forms table listed about half the forms. It now covers
   every spec kind — `congr`, `iota`, `with [...]` and its recursive side-proof
   grammar, the `prop` convention (`eq_true`/`eq_false`) which lived only in a
   *test comment*, `rename_i`, and what has no form (`intro_ctx`, `at *`) with
   the reason. A generator author should not need to read the parser.
5. *(minor)* `zeta` with a `name`: T1 emits the field, the spec does not define
   it, and T2 cannot consume it. **Coordinator decision** — one of the two must
   move; no T2 change is possible without a spec amendment.

## Rounds 1-7 fixes (each re-verified by the following reviewer)
**Round 7** *(4 minor)*: round 6's antiquotation fix had not reached the
recursive side-proof slots added in the same round — one `isAntiquot` predicate
now serves every fallthrough. The `congr` refusal compared terms differing only
in *implicit* arguments, printing the same term twice; both are now rendered
eagerly under `pp.explicit`. The escape-sweep figures had no committed artefact,
so the probe list moved into `test/ExplicitRw/sweep/probes.json` and the runner
drives it.
**Round 6** *(1 critical, 3 major)*: the `eq` slot elaborated with no guard, so
an unresolvable equation logged a *recoverable* error, returned `sorryAx`, and
the `by` block was abandoned **with no diagnostic** — `theorem false_thm :
(1 : Nat) = 2` admitted at exit 0. That was the hole round 5 fixed at the
`change` site and wrote the mechanism down for, then did not apply twelve lines
below. All four sites now go through one **`elabStrict`**, pinned by one fixture
per site. The sort fixtures were accepting-only and the `ℝ`/`ℂ` ones never put
the token inside a step, which is why the atom bug passed; both fixed. The
**recursive side-proof grammar** and the **`congr` step** via `mkCongrSimp?` were
added here — the latter's `isDefEq` guard refuses every unsound rebuild since.
**Round 5**: sort productions read their keyword one node too shallow, so
`Type`/`Type*`/`Sort*` collapsed to `Sort _`, which unifies with anything
including `Prop`; `iota` reduced many steps where the spec says one; `ℕ ℤ ℚ ℝ ℂ`
and `nofun` added; instances are now synthesized only after the position fixes
the carrier, which unblocked `add_zero`.
**Round 4**: the grammar admitted far less than Lean prints; it now covers
conditionals, projection on parenthesised terms, untyped binders, the operators
Mathlib pp emits, set-builder, pairs and sorts.
**Round 3** *(major)*: both guard layers keyed on syntax, so a term elaborator
calling the simplifier in `MetaM` produced neither a `by` node nor a synthetic
metavariable and passed — my claim that the guard caught a block "however it got
there" was false. Terms are now parsed in a whitelist grammar. **Residual hole,
stated not papered over:** an identifier bound to a `@[term_elab]` elaborator is
indistinguishable from a constant at parse time — closed generator-side (**T4**).
**Rounds 1-2**: the `tacticSeq` hole in `then`/`eq … by`, now closed
enumerations; the `let`-body branch abstracted by *value*. Details in git.

## Files (only owned; `ExplicitLean.lean`, `lakefile.toml` untouched)
`ExplicitLean/ExplicitRw{.lean,/Basic,/Tactic}.lean`; `test/ExplicitRw/` (7
fixtures + `RejectedSyntax/`: 13 cases; `sweep/`: probe list + README);
`Experiment/{check_explicit_rw,check_no_simp_family}.py`.
## Checks (re-run from scratch; Lean 4.32.2, pinned Mathlib)
- `lake build ExplicitLean.ExplicitRw` (clean): PASS, no warnings, ~5 s
- `lake env lean test/ExplicitRw/<each>.lean` (7): PASS, no output, 1.6–2.5 s ea
- `python3 -B Experiment/check_explicit_rw.py`: PASS (7 + 13 cases), **~5 min**,
  including two gates it computes rather than this file asserting them — the
  **axiom audit** (112 theorems, all within the allowlist) and the **escape
  sweep** (2 of 6 slots by default, ~285 s of that runtime)
- `T2_FULL_SWEEP=1` sweeps all six slots: **330 escape probes all rejected, 318
  by the parser and 12 at elaboration**, 120 benign all parse. That run takes
  **~20 min**, almost all of it the sweep. The 12 are `admit` and `$x` in all six
  slots: `admit` is a tactic with no term-level constant, so it can only arrive
  as a bare identifier and die in `elabStrict`; `$x` cannot be excluded at parse
  time because Lean gives every `declare_syntax_cat` an antiquotation
  alternative. Since round 8 each is rejected **attributably** — non-zero exit
  and a message naming this tactic or the identifier
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), 0.04 s

Both gates were verified to *fail* when they should: the axiom audit on an
injected `sorry` **and** on an `axiom` declared inside the fixture namespace
(the placement a real regression would have — round 7's injection went after the
`end` and failed to compile, so the gate was never exercised); the sweep on a
planted escape.
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
