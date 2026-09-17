# T17 explicit proposition provenance: review 1

Reviewed commit `4e102123bf1b399d2d81f8f203f9e490992d7054` in its isolated
worktree. Verdict: **PASS; no defects observed.** The diff is scoped to the
new proposition-rule implementation, its consumer/negative fixtures, and
`RESULT.md`.

## Exact-navigation and trust review

The `explicitRwProp` branch calls `rewriteAt e pos`; only inside that callback
does `elabProposition` resolve/elaborate the source declaration/whitelisted
term. It opens the proof type's leading binders, unifies the resulting proof
type with exactly the selected redex (or `Not` of it for `prop_false`), then
synthesizes class instances and consumes ordered `with [...]` proof evidence.
Thus the proposition is fixed by the recorded position before proof elaboration
can close remaining binders. `closeLemmaMVars` and the existing level-mvar
checks remain in the path, so unassigned arguments are still fail-closed.

The implementation has no `Lean.Meta.Simp` import/call, term serialization or
general proof DSL, hypothesis search, goal fingerprint, unsafe fallback,
`sorry`/`admit`, or weakened guard. The source-term parser remains the existing
whitelist, and side proofs remain the closed recursive enumeration.

The 11 requested site-shaped fixtures are all nontrivial, source-faithful
consumers:

| site-shaped rule | fixture |
| --- | --- |
| `leftTotal_empty` | quantified proposition, class argument |
| `rightTotal_empty` | quantified proposition, class argument |
| `exists_apply_eq_apply` | quantified existential proposition |
| `cast_heq` | dependent cast proposition |
| `Decidable.em` | proposition with inferred decidability |
| `if_neg` | fixed conditional redex |
| `dif_pos` | fixed dependent conditional redex |
| `IsPartialInv.eq` | theorem application at a fixed result |
| `Function.FactorsThrough.extend_apply` | fixed `Function.extend` redex |
| `Function.Injective.extend_apply` | fixed `Function.extend` redex |
| `Subsingleton.elim` | fixed tuple component redex |

The other three of the 14 fixtures provide `prop_false`, recursive nested
side evidence, and an inferred-instance proposition. The existing
`with`/nested-side machinery is exercised by `proposition_with_side` and the
full pre-existing ExplicitRw suite. `Negative.lean` rejects missing evidence;
an independent wrong-evidence probe also exited nonzero with the expected
`hq` type mismatch (`q` versus `p`, and `¬q` versus `¬p`).

The dedicated fixture count is therefore exactly **0 → 14**: no T17
provenance fixtures before this commit, 14 after (11 site-shaped + 3 support).

## Checks

- `lake build ExplicitLean.ExplicitRw`: passed.
- All eight `test/ExplicitRw/*.lean` files: passed individually, including
  `Provenance.lean` and `Negative.lean`.
- `python3 -B Experiment/check_explicit_rw.py`: passed (8 fixtures, 13
  rejected-syntax cases; escape sweep passed).
- `python3 -B Experiment/check_no_simp_family.py`: passed (3 files scanned).
- `python3 -m py_compile Experiment/check_explicit_rw.py`: passed.
- `git diff --check`: passed.

No implementation fix is required; this review adds only this file.
