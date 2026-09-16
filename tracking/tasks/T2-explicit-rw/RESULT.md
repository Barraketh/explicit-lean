# T2-explicit-rw result

Status: **complete**, all required checks pass. No escalation.

## What was built

`explicit_rw`: a product tactic replaying a simp trace positionally with no
search. Positions are the `SubExpr.Pos` child-index lists of
`tracking/SIMP-TRACE-SPEC.md`; steps apply in order, each relative to the
previous result; every failure names the step index and reason, with no
fallback, search or retry. Syntax and step kinds (lemma rewrite forward/`←`,
`unfold`, `beta`, `eta`, `proj`, `change`, `eq <eqn> by <tac>`, optional `at h`,
closing `then tac`) are documented in `ExplicitLean/ExplicitRw/Tactic.lean`.

Implementation: direct `Expr` navigation, rebuilding congruence bottom-up with
`congrArg`/`congrFun`/`congr`, `funext` under a lambda, `forall_congr` under a
`∀` body, `implies_congr_left` for a non-dependent arrow domain, `propext` for
iff, and `Eq.mpr`/`Eq.mp` at the root; definitional steps carry no proof. Lemma
arguments are opened as metavariables and fixed by unifying with the subterm,
instances are synthesized, and any metavariable still unassigned after matching
is a hard error, so none escapes into the goal. Nothing calls, imports for use
or expands to `Lean.Meta.Simp` or the simp family.

## Files added (only owned; `ExplicitLean.lean`, `lakefile.toml` untouched)
`ExplicitLean/ExplicitRw.lean`; `ExplicitLean/ExplicitRw/{Basic,Tactic}.lean`;
`test/ExplicitRw/{Basic,Binders,Definitional,Lemmas,Negative}.lean`;
`Experiment/{check_explicit_rw,check_no_simp_family}.py`.

## Checks (this worktree, Lean 4.32.2, pinned Mathlib)
| Command | Result | Runtime |
| --- | --- | --- |
| `lake build ExplicitLean.ExplicitRw` (clean) | PASS, no warnings | 3.1 s |
| `lake env lean test/ExplicitRw/<each>.lean` (5) | PASS, no output | 1.9–2.6 s ea |
| `python3 -B Experiment/check_explicit_rw.py` | PASS (5 fixtures) | 12.2 s |
| `python3 -B Experiment/check_no_simp_family.py` | PASS (3 files) | 0.04 s |

Both scripts were verified to *fail* when they should (the lint fed a bare
`simp`, an `open Lean.Meta.Simp` and `mkSimpContext`; the runner fed a wrong
`guard_target`). Fixtures cover every case the task listed. Positives assert
their goal with `guard_target`/`guard_hyp` before closing and carry the `conv`
equivalent as a cross-check; negatives pin ten messages with `#guard_msgs`.

## Known limitations
- **Dependent positions are refused, not guessed**: dependent `∀` domain, binder
  types, `let` parts, projection structure argument (definitional steps still
  work there; non-dependent arrow domains work fully). This is the spec's
  "dependent positions needing casts stay unresolved" — no spec change needed.
- `at *` refused (positions are per-location); `at h` takes one hypothesis. Spec
  kind `intro_ctx` unimplemented; no fixture needs it. `proj` is
  projection-only; `change` is the general escape hatch. Binder-crossing proofs
  use `Quot.sound` via `funext`, as `conv`/`ext` do; others are axiom-free.

## Open questions
- Generator must emit raw child indices, **not** `conv`'s `arg n` numbering;
  paths are long through instance-laden arithmetic (`a` in `a + c` is
  `[0, 1, 0, 1]`), so the planned readability post-pass matters.
- `explicit_rw` matches up to reducible defeq, so it succeeds where plain `rw`
  fails (`conditional_conv` in `test/ExplicitRw/Lemmas.lean`); confirm before the
  post-pass collapses such steps into `rw [...]`, which would not re-elaborate.
- `ExplicitLean.lean` needs `ExplicitLean.ExplicitRw` wired in at merge.
