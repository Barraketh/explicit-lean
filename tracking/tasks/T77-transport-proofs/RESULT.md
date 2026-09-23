# T77 transported proof terms

## Result

No validation change was integrated. The unresolved classification is not
ordinary proof irrelevance: the representative trace changes a dependent
argument's type and transports a proof with `Eq.ndrec`. Treating the two proof
terms as interchangeable would validate propositions that are not known to be
equal. The saved `simp-trace-v1` event contains pretty-printed before/after
terms, which elide the cast proof and do not carry enough typed evidence to
validate this transport after the recorder has exited.

A future general fix can still be pursued from a fresh recording, while the
typed `Expr` values are available. It would need to authenticate the dependent
congruence/cast from the changed argument through the enclosing expression and
then validate the ordinary Lean replay. Simply adding `Eq.ndrec`-shaped proof
acceptance or relying on `eqIgnoringProofs` is not sufficient: it does not
establish equality of the enclosing propositions.

## Reproduction and evidence

- Worktree: `/Users/ptsier/.codex/worktrees/t77-transport-proof/explicit-lean`
- Base HEAD: `c6c5bd256f7ff059d4d76f63b7d3951ffcc7652e`
- Reproduced the worker failure from `Mathlib.Order.Copy`, ordinal 11, in a
  private copy of its staged module at
  `.lake/private/OrderCopyTransportProbe.lean`. A fresh
  `lake env lean .lake/private/OrderCopyTransportProbe.lean` reaches the
  `simp_trace +instances [eq_le, eq_sdiff, eq_sup]` call and reports the same
  `transported proof term at a rewritten proposition` failure.
- A temporary diagnostic in the isolated worktree (removed afterward) showed
  the mismatch at relative position `[1, 1, 1, 0, 1]`. Both terms pretty-print
  as `a \\ b ≤ c`, but the proof arguments include `eq_le : le = LE.le` on one
  side and the dependent cast `eq_le ▸ eq_le : LE.le = LE.le` on the other.
  The next proposition, `a ≤ b ⊔ c ↔ a ≤ b ⊔ c`, has the same mismatch. The
  temporary diagnostics did not change the comparison or accept the event.
- The persisted raw trace shows the structural `congr` and rewrite sequence,
  but its pretty-printer elides the cast. Therefore it is not a typed
  certificate for this transport once the recording process has ended.
- Existing review records for `by_cases`/`rw` transported propositions
  independently found ordinary `rw` insufficient for those dependent
  contexts. This reproduction is a separate dependent-structure-field case.

## Checks and changes

- `lake build ExplicitLean.SimpTrace` passed in the isolated worktree while
  compiling temporary diagnostic instrumentation; that instrumentation was
  removed and no product Lean source changed.
- The fresh staged-module reproduction failed with the expected unresolved
  classification.
- `git diff --check` passed after cleanup of the temporary source edits.
- No worker roots, databases, source modules, or frozen evidence were changed.

## Limitation

This documents a blocker for the persisted trace shape, not a claim that a
typed dependent-congruence validator is impossible. Such a validator would be
a recorder trust-boundary change and needs a separately specified structural
certificate plus negative controls before the classification can be removed.
