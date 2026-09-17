# T2-explicit-rw result

Status: **complete**, all required checks pass. Review round 1: 7/7 fixed.

`explicit_rw` replays a simp trace positionally with no search (design and
syntax: `ExplicitLean/ExplicitRw/Tactic.lean`). Nothing reaches
`Lean.Meta.Simp`, **and no trace in this syntax can introduce it**.

## Round 1 fixes
1. *(critical)* `then` / `eq ... by` took a free `tacticSeq`, so a trace could
   run `simp` inside the product tactic where the lint could never see it. Both
   are now closed enumerations: `then simp`, `then (dsimp; simp)` and
   `eq ... by simp` fail in the **parser**; `then exact (by simp)` and a `by`
   block in any elaborated term fail at elaboration. Per addendum `trivial` is
   excluded (search macro; use `exact True.intro`); keywords are non-reserved,
   so those words stay usable as ordinary terms elsewhere.
2. *(major)* `proj` never reduced a projection-*function* application
   (`whnfCore` does no delta). It now delta-unfolds first, and requires a
   constructor argument so a class projection cannot make `proj` unfold freely.
3. *(major)* `let`-body positions (child 2) need no cast; supported by
   zeta-substituting the bound value. `let` type/value stay refused.
4-5. *(minor)* `change` errors pretty-print the term; a dependent function
   argument is caught before `mkCongrArg`, giving the tactic's own message.
6. *(minor)* The lint scans `import` lines; it immediately caught this tactic's
   own error message, which named the tactics — reworded.
7. *(minor)* Added the missing fixtures (`proj` both shapes, `mdata`, `letE`
   body, universe-polymorphic lemma, stale position, `change` message,
   dependent app, refused `let` value) and corrected the coverage claims.

## Files (only owned; `ExplicitLean.lean`, `lakefile.toml` untouched)
`ExplicitLean/ExplicitRw{.lean,/Basic,/Tactic}.lean`; `test/ExplicitRw/` (5
fixtures + `RejectedSyntax/`: 5 cases, `expected.json`, README);
`Experiment/{check_explicit_rw,check_no_simp_family}.py`.

## Checks (all re-run from scratch; Lean 4.32.2, pinned Mathlib)
- `lake build ExplicitLean.ExplicitRw` (clean): PASS, no warnings, 3.1 s
- `lake env lean test/ExplicitRw/<each>.lean` (5): PASS, no output, 1.8–2.4 s ea
- `python3 -B Experiment/check_explicit_rw.py`: PASS (5 + 5 cases), 21.0 s
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), 0.04 s

`#print axioms` on all 50 fixture theorems: **no `sorryAx`** — 33 axiom-free, 8
`Quot.sound` (funext), 9 `propext` (iff), each matching its `conv` cross-check.
Every check was verified to *fail* when it should: the lint fed a bare `simp`,
an `open Lean.Meta.Simp`, `mkSimpContext` and a simp import; the runner fed a
wrong `guard_target`, a rejected-syntax file made to compile, and one rejected
for the wrong reason.

## Limitations and open questions
- **Dependent positions are refused, not guessed**, each with a step-indexed
  message: dependent function argument and `∀` domain, binder types, `let`
  type/value, projection structure argument. Definitional steps work there;
  non-dependent arrow domains and `let` bodies work fully.
- `at *` refused (per-location); `at h` takes one hypothesis. `intro_ctx`
  unimplemented. Ordinary goals carry no `mdata`; that fixture wraps the target.
- Generator must emit raw child indices, **not** `conv`'s `arg n` numbering;
  paths are long through instance-laden arithmetic, so the readability
  post-pass matters. `explicit_rw` also matches up to reducible defeq, so it
  succeeds where plain `rw` fails (`conditional_conv` in `Lemmas.lean`);
  confirm before the post-pass collapses such steps into `rw [...]`.
- `ExplicitLean.lean` needs `ExplicitLean.ExplicitRw` wired in at merge.
