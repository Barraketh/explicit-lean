# T1-trace-capture: RESULT (T1b — forked traversal)

`simp_trace` now runs a **fork of simp's own traversal** that records positions directly. Frontend unchanged and still
substitutable (every `simp` argument form plus a trailing `=>trace "<path>"`; without it the JSON is logged as
`simp-trace-json:{...}`); goal-state replication still mirrors `Meta.simpGoal`.

## The fork — `ExplicitLean/SimpTrace/Traversal.lean` (1180 lines, 41 `SOURCE:` annotations)

Copied from Lean 4.32.2 `src/lean/Lean/Meta/Tactic/Simp/`: 31 functions from **Main.lean** (`reduceStep`, `reduce`, `unfold?`,
`reduceProjFn?`, `reduceFVar`, `dsimpImpl`, `simpProj`/`Const`/`Lambda`/`Arrow`/`Forall`/`Let`/`App`/`Step`, `visitFn`,
`congr`/`congrDefault`, `processCongrHypothesis`, `trySimpCongrTheorem?`, `simpLoop`, `simpImpl`, `withNewLemmas`,
`lambdaTelescopeDSimp` and their helpers) and 6 from **Types.lean** (`congrArgs`, `simpAppUsingCongr`, `tryAutoCongrTheorem?`,
`mkCongrFun'`/`mkCongrPrefix`/`mkCongr'`). Each carries a `SOURCE:` comment with its upstream file and line range, so a Lean bump
re-syncs by diffing. Nine are `private` upstream; every symbol their bodies reference is public, so no `private`/`unsafe`/
`@[implemented_by]` boundary had to be reproduced — no escalation.

**Stock and untouched:** everything deciding *what* simp does — `Simp.Methods` (`pre`/`post`/`dpre`/`dpost`/`discharge?`) from
the context, `Simp.rewrite?`, `Simp.Result`, simproc tables, congruence lookup, `synthesizeArgs`, `mkCongrSimp?`. Two edits
applied uniformly: every recursive `Simp.simp`/`Simp.dsimp` (an `@[extern "lean_simp"]` opaque that would dispatch to *stock*
`simpImpl` and lose positions) becomes `simpT`/`dsimpT` with the child's position; and stock `Methods` run under `withPos`, so the
recorder reads the position of the subterm they fire on.

**Threading.** `pos : Pos` is an explicit parameter on every copied function, extended per the spec (`app` 0/1, binder 0/1, `letE`
0/1/2, `mdata`/`proj` 0). For an `n`-ary application argument `i` is at `0^(n-1-i) ++ [1]` (`argPos`/`fnPos`) — exactly the order
`simpAppUsingCongr`'s `visit` walks, as REVIEW-3's fork note predicted. `processCongrHypothesisT` locates the argument a
congruence *hypothesis* simplifies and hands `simpT` its position, so `ite_congr` traces at the condition. A **binder stack**
(`EvCtx.binders`) records the fvars the traversal substituted for term binders, so the validator never infers them.

**Two deliberate departures.** (1) The result **cache is disabled**: keyed on the expression alone, reuse at a second position
would log events nowhere or at the first — a position-exact trace and an expression-keyed cache are incompatible. (2) A simproc
may call the opaque `Simp.simp` on a subterm of its choosing (`reduceIte` on an `ite`'s condition); that enters stock `simpImpl`
and its firings carry no position, so they are **diverted** into a frame and attached to the simproc's `eq` step as `side`
evidence.

**Deleted.** `Position.lean` lost 327 of 404 lines: `findBridge?`, `findBridgeChain?`, `reducibleSites`, `reduceHere?`,
`substAll`, `refresh`, `findOccurrences`, `Occurrence`, `Bridge`, `collectBridges`, `solvePositions`, the no-op-match rule. What
remains is navigation plus the **validator**, run after every location: navigate `pos`, check the subterm equals `before`,
substitute `after`, require the final term to equal simp's result; mismatch is a hard failure. **No search anywhere in the
recorder.**

## Measurements (macOS, Lean 4.32.2; outputs gitignored; wall/RSS are cold-cache upper bounds — a warm re-run is ~2.9 s)

| file | calls | traced | steps | kinds | bytes | wall | peak RSS | unres. |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `IsEmptyBasicTraced.lean` | 17 | 17 | 76 | `rw` 70, `unfold` 6 | 15 045 | 4.71 s | 677 MB | 0 |
| `NontrivialDefsTraced.lean` | 1 | 1 | 6 | `rw` 6 | 1 109 | 5.20 s | 638 MB | 0 |
| `FunctionDefsTraced.lean` | 1 | 1 | 12 | `rw` 8, `proj` 4 | 1 878 | 5.09 s | 645 MB | 0 |
| `ExistsUniqueTraced.lean` | 8 | 8 | 29 | `rw` 23, `beta` 4, `unfold` 2 | 5 601 | 5.33 s | 649 MB | 1 |
| **Mathlib total** | **10** | **10** | **47** | `rw` 37, `beta` 4, `proj` 4, `unfold` 2 | **8 588** | — | — | **1** |

Every call stock simp proves traces (10/10, against REVIEW-3's 8/11); no goal stock simp closes is left open. The one unresolved
is `ExistsUnique.lean:121` — *`exists_prop_congr` simplifies a subterm that is not a child of the application*; its trace is
emitted and passes validation, the flag being conservative about a firing it cannot place. IsEmpty reproduces the previous kind
tally exactly — the fork does not diverge from stock.

## REVIEW-3 items (each reproduced before, re-run after)

- **C1** fixed: an unattributable firing is an `eq` step whose `by` a scratch check decides, never an abort. `FINAL.lean` closes
  (`Nat.reduceAdd`, `by:"rfl"`); `IOTA5.lean`'s `Option.getD` traces as `unfold` + **`iota`** — the kind that previously had no
  emitter. (`IOTA2.lean:19`'s error is stock simp's own unsolved goal, verified against stock.)
- **C2** fixed by deletion. Chain depths 4/6/8/12: **2.71/2.70/2.70/3.26 s** (was 6.8/219.4/timeout/timeout), flat against stock's
  2.7 s. `PROJ3.lean`: **3.98 s** vs stock 4.04 s (was a 101.6 s timeout).
- **M3** fixed: `UNK2.lean` records `close:{"by":"omega"}`. Discharger text is read by pretty-printing the node and stripping
  delimiters, stable across its `atomic`/`patternIgnore` wrappers.
- **M4** both fixed. (a) `Function/Defs.lean` emits the four `proj` reductions at four distinct positions in simp's order — the
  composition the chain search exhausted its bound on. (b) `ExistsUnique.lean:115` traces; the `_fvar` leak is structurally
  impossible now. Fixing (b) exposed a real validator bug: **a non-dependent arrow is a binder node that binds no term variable**,
  so `Expr.abstract`'s indices need padding for it.
- **M5** fixed: a Prop-valued lemma carries `"prop":"true"`/`"false"`, from the origin's declared type. Both lemmas REVIEW-3 named
  carry it — `leftTotal_empty`/`rightTotal_empty` (`true`), `List.not_mem_nil` (`false`). Acting on the flag is T2's side. **M6**
  fixed: no `#N` in any of the 57 traces — subterms come from the live traversal with binders in scope. **M7**: this file replaces
  the overstated one.

## Lemma-headed simproc proofs (spec amendment 408a39b)

A simproc whose proof is one lemma applied is now an ordinary `rw` naming that lemma, with the discharged condition as a `side`
sub-trace and `"source"` naming the simproc. `classifyProof` is **generic, never a table of simproc names**: it takes the proof's
head constant and walks its arguments against the lemma's own binder telescope, requiring every *explicit* argument to be a
subterm of the position, an instance, or a proof (which becomes the side entry). Plumbing heads (`Eq.trans`/`Eq.mpr`/`Eq.symm`/
`of_eq_true`) are excluded, so those stay `eq`.

| simproc | proof head | recorded | replay shape, verified well-typed |
| --- | --- | --- | --- |
| `reduceIte` | `ite_cond_eq_true`/`_false` | `rw` + side | `rw [ite_cond_eq_true 1 2 (eq_true h)]` |
| `reduceDIte` | `dite_cond_eq_true`/`_false` | `rw` + side | `rw [dite_cond_eq_true (eq_true h)]` |
| `simpUsingDecide` (`+decide`) | `eq_true_of_decide` | `rw` + side | `rw [eq_true_of_decide (rfl : decide _ = true)]` |
| `Nat.reduceEqDiff` | `eq_false_of_decide` | `rw` + side | `rw [eq_false_of_decide (rfl : decide _ = false)]` |
| `reduceCtorEq` | `eq_false'` | `rw` + **unresolved** side | — (see below) |

Each row was checked by running the replay in ordinary Lean; the `Decidable` instance being an argument of `ite` rather than part
of the motive is what makes the shape work, as the coordinator noted. The actual head constants are
`ite_cond_eq_true`/`dite_cond_eq_true`, not `if_pos`/`dif_pos` — Lean 4.32.2's `reduceIte` builds the former.

**`reduceCtorEq` is the honest limit.** Its head *is* one lemma, but `eq_false'`'s explicit argument is a `noConfusion`
elimination under a local binder — a term no close form in the spec describes. Claiming `true_intro` would tell a replayer to
close `FixtureColor.red = FixtureColor.green → False`, which is not `True`; the side entry carries a classified `unresolved:`
close instead and the call is reported unresolved. On `Nat` literals `Nat.reduceEqDiff` fires first and maps cleanly (the
`ctor_eq` fixture); `ctor_eq_inductive` reaches the real one.

**Fixture changes** (four skeletons; each is the fork being more faithful). `contextual` now emits two **`intro_ctx`** steps
(never emitted before); `zeta` puts `zeta` first — verified against `trace.Debug.Meta.Tactic.simp` that `reduceStep (pre)` fires
on the `let` before any `add_zero`, so the old order was a reconstruction artifact; `shadowed` emits `beta` then three separate
`add_zero` rewrites at exact positions where the old trace merged two occurrences; `ite` carries the simproc's nested condition
rewrites as `side` evidence (side goal `n = 3`). The checker gained the amended spec's forms (`omega`, `unresolved:` closes,
`prop`, `intro_ctx` naming) and was re-verified to catch a perturbed `pos`.

**Checks, all re-run from scratch after the amendment.** `lake build ExplicitLean.SimpTrace` with oleans deleted: clean, no
warnings, 14.63 s, 737 MB. `Fixtures.lean` (33): pass, 4.93 s, 1 511 MB — the one remaining unresolved is the deliberate
`ctor_eq_inductive` fixture. `python3 -B Experiment/check_simp_trace.py`: `OK: 33 ...`, 9.23 s, and its new assertion (a `rw`
carrying a `source` must carry a `side`) was verified to fire on a regression. `IsEmptyBasicTraced.lean`: pass 17/17, 4.06 s,
676 MB. The three measurement modules re-run unchanged — those corpora contain no lemma-headed simproc firings. Nothing came near
30 minutes or 40 GB.

**Known limitations.**

- **`reduceCtorEq` on a user inductive is the one remaining unresolved fixture** — its condition proof is a `noConfusion` term no
  close form describes (above). Resolving it needs a close form for "eliminated by `noConfusion`", which is a further spec
  question, not a coding one.
- `eta` is in the spec but **never emitted**: stock `reduceStep` does not perform eta reduction (its `-- TODO: eta reduction` is
  still there in 4.32.2), so emitting it would diverge from stock simp.
- `simpHaveTelescope` simplifies a `have` telescope as a unit through `MonadSimp SimpM`, which dispatches to stock `simp`; a
  change there marks the call unresolved. Unexercised by this corpus.
- Disabling the cache costs time on heavily shared terms — not visible at this size (IsEmpty 4.71 s against the reconstruction's
  2.4 s) but worth watching on a large module. A Lean bump needs a re-sync.

**Open questions.** 1. Should the spec gain a close form for a condition discharged by constructor `noConfusion`? That is the
only thing keeping `reduceCtorEq` unresolved. 2. `exists_prop_congr`-style congruence theorems simplify
under their own binders: give the spec a position form, or is the classified unresolved the intended end state? 3. `ctxIndex` is
`LocalDecl.index` and (per REVIEW-3) is not a `rename_i` argument; worth saying so in the spec.
