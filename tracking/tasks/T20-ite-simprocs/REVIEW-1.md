# T20 review 1 — NO-GO

## Verdict

**NO-GO / merge-ineligible.** The bounded records are sound on the simple
value-valued `ite`/`dite` fixture, but the implementation regresses existing
dependent conditional applications. This is a validation failure, not merely
an unobserved-coverage count.

## Evidence

- `lake build ExplicitLean.SimpTrace`: **PASS**.
- `lake env lean test/SimpTrace/T20IteSimproc.lean`: **PASS**. The five
  `reduceIte` records and two `reduceDIte` records have exact fixed positions,
  true/false branch labels, matching `ite_cond_eq_*`/`dite_cond_eq_*`
  constructors, and condition-side evidence. Dependent records correctly have
  no branch proof in `args`.
- The complete existing `Fixtures.lean` compiled successfully after using the
  already-built pinned Mathlib/package artifacts from the base checkout. The
  trace checker accepted all 74 pre-existing traces; its only remaining
  failures were the seven T20 fixture outputs (no expected skeletons) and four
  generated `.1` duplicates.
- `check_simp_engine_ite.py`, `check_simp_engine_dite.py`,
  `check_simp_engine_simproc.py`, and `check_simp_engine_replay.py`: **PASS**.
  The existing generic simproc/arithmetic/replay probes remain unchanged.
- T18 remains the inventory baseline: 15 `reduceIte` steps at 6 sites and 15
  `reduceDIte` steps at 8 sites. No fresh 91-site inventory was run. Focused
  observed records are therefore 5/15 `reduceIte` and 2/15 `reduceDIte`, not
  campaign coverage credit.

## Blocking defect: applied conditional redex

The T20 emitter writes the semantic rewrite using the untrimmed `e`/`r.expr`
pair at `emitBoundedIteStep` (Recorder lines 747–795). When the conditional is
a function applied to an argument, stock `reduceIte`/`reduceDIte` rewrites the
function prefix and reapplies the trailing argument. The recorded step is then
checked at the application root with `before` equal to the already-applied
branch, while the actual redex is the conditional function application.

Minimal reproductions (temporary, not committed) both fail visibly:

```text
example [Decidable P] (f g : Nat → Nat) (a : Nat) (h : P) :
  (if P then f else g) a = f a := by simp_trace [h]
error: simp_trace: validation failed: subterm at [] is
(if P then f else g) a = f a
but the recorded step's before is f a = f a

example [Decidable P] (f : P → ∀ a, σ a) (g : ¬P → ∀ a, σ a) (a : α) :
  (dite P f g) a = dite P (fun h ↦ f h a) (fun h ↦ g h a) := by ...
error: simp_trace: validation failed (both true and false branches)
```

The same regression appears in the existing corpus fixtures at
`LogicBasicTraced.lean:974` (and the corresponding `FunctionBasicTraced`
conditional site): the parent emits the prior classified unresolved result,
whereas T20 emits a validation failure. This violates stock-result/validation
parity and blocks merge.

## Cached-origin assessment

The nested T20 occurrence demonstrates the known `usedTheorems` cache-origin
gap: the second occurrence has no diverted nested condition events. In this
case the recorder still recovers `reduceIte` from the visible redex/result and
gets a replayable `assumption:eq_true h` side close, so the gap alone is a
coverage limitation and fails visibly when side evidence cannot be completed
(`markUnresolved` is used on all missing/malformed evidence branches). It does
not cure the applied-redex validation defect above. The fallback is also a
bounded shape heuristic, so it must not be treated as generic attribution for
future/custom simprocs.

`git diff --check`: **PASS**. No implementation fix is included in this review.
