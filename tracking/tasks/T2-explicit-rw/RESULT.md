# T2-explicit-rw result

Status: **complete**, all required checks pass. Round 1: 7/7. Round 2: 7/7.
`explicit_rw` replays a simp trace positionally with no search (design and
syntax: `ExplicitLean/ExplicitRw/Tactic.lean`). Nothing reaches `Lean.Meta.Simp`,
and no trace in this syntax can introduce it: the two tactic slots are closed
enumerations, and every term it elaborates is refused if it elaborates a tactic
block, however that block got there.

## Round 2 fixes
1+2. *(major)* The `let`-body branch abstracted by **value**, destroying the `let`
   when the value was closed (so later positions went stale) and capturing
   unrelated occurrences when it was a free variable. It now opens the `let` with
   `withLetDecl` and rebuilds with `mkLetFVars`, abstracting by identity. The old
   `let_body` fixture had no `guard_target` and pinned nothing; the three new ones
   were verified to **fail** against the old implementation.
3. *(major)* The tactic-block guard is now semantic. Matching the synthetic
   metavariable's recorded *syntax* rather than its kind is what makes it robust:
   a term elaborator calling `elabTerm` on a `by` block registers it `.postponed`,
   not `.tactic`. Found while testing: an `elab`-based smuggler defeated both the
   kind check and macro expansion, and is now refused. The syntax walk stays as a
   second layer, run on macro-expanded syntax.
4. *(major)* `zeta` is a real step kind — the only step that destroys a `let`;
   an unrecognised keyword no longer falls through to the lemma branch.
5. *(minor)* `intro_ctx` has syntax and fails **by name** as unimplemented,
   rather than being parsed as a lemma called `intro_ctx`.
6. *(minor)* Bare `assumption` dropped from the closer set: it scans the whole
   context, so it can close with a different hypothesis than the trace recorded.
   The spec's `assumption:<name>`, `true_intro` and `absurd:<hyp>` render as
   `exact <term>`. 7 *(info)*: no change needed.

**Addendum (T1 cross-check).** The reported `IsEmpty` failure is **not** a
universe-level defect: `not_nonempty_iff` lives in `Mathlib.Logic.IsEmpty.Basic`,
which the failing file did not import; the `?m.2` was the type of the `sorryAx`
elaboration produces for an unknown identifier, and the passing file's extra
import pulled the lemma in transitively. Fixed as directed anyway:
`elabEquation` forces synthetic metavariables, rejects a surviving universe level
with a step-indexed error rather than defaulting it, and names a failed
elaboration as such. Fixtures replay `call01` of the captured traces and use the
same `Sort*`-polymorphic lemma at `Sort 0` and at `Type` in one file.

**Round 1 fixes** (the `tacticSeq` hole, `proj` delta, `let` bodies, `change`
messages, the dependent-function message, `import` linting, coverage claims) were
all re-verified fixed by the round-2 reviewer; details in git history.

## Files (only owned; `ExplicitLean.lean`, `lakefile.toml` untouched)
`ExplicitLean/ExplicitRw{.lean,/Basic,/Tactic}.lean`; `test/ExplicitRw/` (5
fixtures + `RejectedSyntax/`: 6 cases, `expected.json`, README);
`Experiment/{check_explicit_rw,check_no_simp_family}.py`.

## Checks (re-run from scratch; Lean 4.32.2, pinned Mathlib)
- `lake build ExplicitLean.ExplicitRw` (clean): PASS, no warnings, 3.4 s
- `lake env lean test/ExplicitRw/<each>.lean` (5): PASS, no output, 1.9–2.5 s ea
- `python3 -B Experiment/check_explicit_rw.py`: PASS (5 + 6 cases), 23.0 s
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), 0.05 s

`#print axioms` on all 58 fixture theorems: **no `sorryAx`** — 38 axiom-free, 8
`Quot.sound`, 11 `propext`, 1 both. Each check was verified to *fail* when it
should, including the new `let` fixtures against the pre-fix code.

## Limitations and open questions
- **Dependent positions are refused, not guessed**, each with a step-indexed
  message: dependent function argument and `∀` domain, binder types, `let`
  type/value, projection argument.
- `intro_ctx` is recognised but unimplemented (T1 does not emit it); `at *` is
  refused. Ordinary goals carry no `mdata`, so that fixture wraps the target.
- Generator must emit raw child indices, **not** `conv`'s `arg n` numbering.
  `explicit_rw` also matches up to reducible defeq, succeeding where plain `rw`
  fails (`conditional_conv`); confirm before the post-pass collapses such steps.
- `ExplicitLean.lean` needs `ExplicitLean.ExplicitRw` wired in at merge.
