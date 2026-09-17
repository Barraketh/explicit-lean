# T1-trace-capture: RESULT (T1b — forked traversal)

`simp_trace` runs a **fork of simp's own traversal** that records positions directly. Frontend unchanged and still substitutable
(every `simp` argument form plus a trailing `=>trace "<path>"`, else the JSON is logged); goal state mirrors `Meta.simpGoal`.

## The fork — `ExplicitLean/SimpTrace/Traversal.lean` (~1200 lines, 43 `SOURCE:` annotations)

Copied from Lean 4.32.2 `src/lean/Lean/Meta/Tactic/Simp/`: the traversal of **Main.lean** (`reduceStep`, `reduce`, `unfold?`,
`reduceProjFn?`, `reduceFVar`, `dsimpImpl`, `simpProj`/`Const`/`Lambda`/`Arrow`/`Forall`/`Let`/`App`/`Step`, `visitFn`,
`congr`/`congrDefault`, `processCongrHypothesis`, `trySimpCongrTheorem?`, `simpLoop`, `simpImpl`, `withNewLemmas`,
`lambdaTelescopeDSimp` and helpers), the congruence machinery of **Types.lean** (`congrArgs`, `simpAppUsingCongr`,
`tryAutoCongrTheorem?`, `mkCongr*`), and **Transform.lean**'s `transformWithCache` (as `dsimpT`, round 4). Each carries a `SOURCE:`
comment with its upstream file and line range. Nine are `private` upstream; every symbol their bodies reference is public, so no
`private`/`unsafe`/`@[implemented_by]` boundary had to be reproduced.

**Stock and untouched:** everything deciding *what* simp does — `Simp.Methods` from the context, `Simp.rewrite?`, `Simp.Result`,
simproc tables, congruence lookup, `synthesizeArgs`, `mkCongrSimp?`. Two edits applied uniformly: every recursive
`Simp.simp`/`Simp.dsimp` (an `@[extern]` opaque that would dispatch to *stock* `simpImpl` and lose positions) becomes
`simpT`/`dsimpT` with the child's position; and stock `Methods` run under `withPos`.

**Threading.** `pos : Pos` is an explicit parameter on every copied function, extended per the spec (`app` 0/1, binder 0/1, `letE`
0/1/2, `mdata`/`proj` 0). For an `n`-ary application argument `i` is at `0^(n-1-i) ++ [1]` (`argPos`/`fnPos`) — exactly the order
`simpAppUsingCongr`'s `visit` walks. A **binder stack** (`EvCtx.binders`) records the fvars the traversal substituted for term
binders, so the validator never infers them.

**Deliberate departures.** (1) The result **cache is disabled**: keyed on the expression alone, reuse at a second position would log
events nowhere or at the first. (2) Where stock simp is re-entered on a subterm the fork did not descend into — a simproc's own
`simp c`, `simpHaveTelescope`, a congruence hypothesis — those firings have no position, so they are **diverted** and the net change
recorded instead.

**Deleted.** `Position.lean` lost 327 of 404 lines (`findBridgeChain?`, `reducibleSites`, `refresh`, `findOccurrences`,
`collectBridges`, `solvePositions`, the no-op-match rule). What remains is navigation plus the **validator**: navigate `pos`, check
the subterm equals `before` (modulo proof irrelevance), substitute `after`, require the final term to equal simp's result. **No
search anywhere in the recorder.**

## Measurements (macOS, Lean 4.32.2; outputs gitignored; cold-cache figures)

| file | calls | traced | steps | kinds | bytes | wall | stock | peak RSS | unres. |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `IsEmptyBasicTraced.lean` | 17 | 17 | 76 | `rw` 70, `unfold` 6 | 15 045 | 2.42 s | — | 645 MB | 0 |
| `NontrivialDefsTraced.lean` | 1 | 1 | 6 | `rw` 6 | 1 109 | 2.39 s | — | 638 MB | 0 |
| `FunctionDefsTraced.lean` | 1 | 1 | 12 | `rw` 8, `proj` 4 | 1 878 | 2.56 s | — | 645 MB | 0 |
| `ExistsUniqueTraced.lean` | 8 | 8 | 29 | `rw` 23, `beta` 4, `unfold` 2 | 5 601 | 2.54 s | — | 651 MB | 1 |
| `FunctionBasicTraced.lean` | 19 | 19 | 102 | `rw` 76, `beta` 7, `intro_ctx` 8, `proj` 3, `unfold` 4, `congr` 2, `change` 2 | 20 274 | 3.05 s | 2.62 s | 709 MB | 5 |

**Every call stock simp proves traces: 46 of 46**, none leaves a goal stock closes, no panics, no validation failures. The 6
unresolved are user `@[congr]` transports (see Round 5). The four earlier corpora reproduce their tallies exactly.

**REVIEW-3 items, all confirmed fixed by the round-4 reviewer.** C1 an unattributable firing is an `eq` step whose `by` a scratch
check decides, never an abort; `iota` gained an emitter. C2 fixed by deleting the search: chain depths 4–30 flat, matching stock. M3
`(disch := omega)` records `close:{"by":"omega"}`. M4 both Mathlib calls trace; fixing (b) exposed that a non-dependent arrow is a
binder node binding no term variable, so `Expr.abstract`'s indices need padding. M5 Prop-valued lemmas carry `"prop"`. M6 no `#N` in
any trace.

**Lemma-headed simproc proofs (spec 408a39b).** A simproc whose proof is one lemma applied is an ordinary `rw` naming that lemma,
with the discharged condition as a `side` sub-trace and `"source"` naming the simproc. `classifyProof` is **generic, never a table
of simproc names**: it walks the proof head's arguments against the lemma's own binder telescope, requiring every *explicit*
argument to be a subterm of the position, an instance, or a proof. Plumbing heads (`Eq.trans`/`Eq.mpr`/`Eq.symm`/ `of_eq_true`) are
excluded, so those stay `eq`.

| simproc | proof head | verified replay shape |
| --- | --- | --- |
| `reduceIte` / `reduceDIte` | `ite_cond_eq_true`/`_false`, `dite_…` | `rw [ite_cond_eq_true 1 2 (eq_true h)]` |
| `+decide` / `Nat.reduceEqDiff` | `eq_true_of_decide` / `eq_false_of_decide` | `rw [eq_true_of_decide (rfl : decide _ = true)]` |
| `reduceCtorEq` | `eq_false'` | `exact eq_false' nofun` (round 4) |

Each replay shape was run in ordinary Lean; the heads are `ite_cond_eq_true`/`dite_cond_eq_true`, not `if_pos`/`dif_pos`. The
round-4 reviewer confirmed `classifyProof` resisted all three fooling attempts.

**Earlier fixture-skeleton changes,** each the fork being more faithful: `contextual` emits `intro_ctx` (never emitted before);
`zeta` puts `zeta` first (verified against `trace.Debug.Meta.Tactic.simp`); `shadowed` emits three separate rewrites where the old
trace merged two occurrences; `ite` carries the simproc's nested rewrites as `side`.

## Round 4 fixes

**1 (critical) — `let` under every config.** `dsimpT` was a hand-written traversal, not a port of `transformWithCache`; it is now
the latter verbatim, so the telescope is collected, each body instantiated with `instantiateRev fvars`, and the post step run on the
term rebuilt by `mkLambdaFVars` **at the telescope root**. `simpLetT` no longer desyncs the validator: a `letToHave` conversion is
recorded as a `change`, and `simpHaveTelescope` (which runs *stock* simp on the telescope bodies) has its events diverted and the
net rewrite recorded as one `change`, with the call classified. Fixtures: both reviewer shapes under `zeta := true` and `zeta :=
false`, plus the `zetaDelta` shape; all verified against stock's goal state.

**2 (critical) — the PANIC.** Root cause was **not** the binder path but `tryAutoCongrTheoremT?`: its `eq` arm pushed two `subst`
entries where upstream pushes three (`arg`, `argResult.expr`, `argProof`), and the tail read `type.appArg!.instantiateRev subst`
instead of destructuring `type.instantiateRev subst |>.eq?`. The misaligned `subst` left loose bvars in the rhs, which reached stock
`rewritePost`. Loop and tail are now upstream's. Found by asserting closedness at every stock-method entry.

**3 (major) — `dsimp` fidelity and the validator.** Restored verbatim: `skipInstances := !cfg.instances`, `usedLetOnly := cfg.zeta
|| cfg.zetaUnused`, per-node `Core.checkSystem "transform"`. The five validation failures are gone, fixed at the source rather than
by loosening the check: (a) `trySimpCongrTheoremT?` diverts its hypothesis rewrites and records the node's whole change as one
`change`, which also fixed `:976`, whose recorded `before` was a strictly wrong position; (b) `validate` compares with
`eqUpToProofs`, structural equality with proof subterms compared by type, because upstream's own `isDefEq` runs with
`proofIrrelevance := true`. Instance arguments and binder types are deliberately **not** weakened. `validate` also instantiates
metavariables on both sides.

**4 (major) — the fixture gate.** `Fixtures.lean` exits 0 once defect 5 lands, and `check_simp_trace.py` now compiles the positive
fixtures itself and fails on any nonzero exit. Calls unresolved *by design* moved to `UnresolvedFixtures.lean`, whose traces are
still compared and which must report at least one classified line.

**5 (major) — `nofun`.** `assumptionName?` recognises a condition proof refutable by empty pattern matching from its **type** (one
hypothesis, an equation between distinct constructors) rather than the `noConfusion` term's shape. `reduceCtorEq` records
`close:{"by":"nofun"}`; replay is `exact eq_false' nofun`.

**6 (minor)** an `eq` step whose firing registered no origin no longer carries the placeholder `"source":"simproc"`. **7 (minor)**
`simpLoopT` takes one `reduceStep` as upstream, not a fixpoint.

## Round 5: the `congr` step kind (spec 3b17247)

`tryAutoCongrTheoremT?` captures each `CongrArgKind.eq` argument's events into a frame, then decides once every argument has been
visited. With a `CongrArgKind.cast` dependent, each rewritten argument becomes one `congr` step at the application's position
carrying the argument index and its own steps at relative positions (several such steps compose in array order); otherwise the
events are re-rooted to absolute positions and stay plain `rw` steps, per the spec. The validator checks **both** halves: the node's
whole before/after at `pos`, and `validateNested` independently replays the argument at relative positions, recursing through nested
`congr`. The checker requires an integer `arg` and non-empty `steps`, rejects `steps` on any other kind, and compares nested steps
recursively — verified to fire on a perturbed nested position.

**The 6 previously unresolved calls did not become `congr`, and should not have.** They fire *user* `@[congr]` theorems through
`trySimpCongrTheorem?` — `ite_congr` (head `ite`), `dite_congr` (head `dite`), `exists_prop_congr` (head `Exists`) — which is a
different mechanism from the auto-generated `mkCongrSimp?` path the spec's `congr` kind names. I checked what `mkCongrSimp?`
produces for those three heads: `ite ↦ [fixed, eq, subsingletonInst, eq, eq]`, `dite ↦ [fixed, fixed, subsingletonInst, eq, eq]`,
`Exists ↦ [fixed, eq]` — **no `CongrArgKind.cast` in any of them**, and the spec says to use `congr` "only when plain positional
rewriting would need casts (a `CongrArgKind.cast` dependent)". Emitting `congr` there would have claimed a cast transport that does
not exist. Those 6 stay classified `change` + unresolved; the user-`@[congr]` case is a separate spec question (open question 1
below).

Where the kind *does* apply, it fires on real code: **2 `congr` steps in `Function/Basic`**, both in `FunctionBasicTraced_02`
(`:390`, the call that used to PANIC) — `cast hU (g s).snd ↦ cast hU (cast ⋯ s)`, argument 3, nested `proj` at relative `[]`, and
the same for `t`.

**Fixed while adding this:** every trace-frame access indexed with `[depth-1]!` under a `>= depth` guard, which panics with "index
out of bounds" when `depth` is 0 or a nested frame popped early — 10 panics once `captureEvents` added a second frame kind. All are
now total, and `rootOf` clamps its drop for a subtree simplified from a fresh root. **`ctxIndex`** is documented per the spec as
`LocalDecl.index`, identifying the declaration and explicitly not a `rename_i` argument.

**Checks, all re-run from scratch.** `lake build ExplicitLean.SimpTrace` with oleans deleted: clean, no warnings, 10.08 s, 743 MB.
`Fixtures.lean` (40 traces): **exit 0**. `UnresolvedFixtures.lean`: exits 1 by design, 1 classified line. `python3 -B
Experiment/check_simp_trace.py`: `OK: 40 ...`; it compiles the fixtures itself, and its three assertions (a `rw` with a `source`
must carry a `side`; a positive fixture must exit 0; a `congr` step's nested positions) were each verified to fire on a regression.
The five measurement modules: see the table. Nothing came near 30 minutes or 40 GB.

**Known limitations.**

- **User `@[congr]` transports are recorded as one `change`** (6 of 46 calls): `ite_congr`, `dite_congr`, `exists_prop_congr`. The
  trace is sound and validates, but a replayer gets a defeq assertion where simp made a rewrite. The spec's `congr` kind does not
  cover these (Round 5); this is the largest remaining gap.
- **`simpHaveTelescope`** simplifies a `have` telescope through `MonadSimp SimpM`, which dispatches to *stock* `simp`; its inner
  rewrites carry no position, so the telescope rewrite is one `change` and the call is classified. Redirecting it would need a
  change to that instance, outside this task's ownership.
- `eta` is in the spec but **never emitted**: stock `reduceStep` does not perform eta reduction (its `-- TODO: eta reduction` is
  still there in 4.32.2), so emitting it would diverge from stock simp.
- The disabled result cache costs 1.99x on the reviewer's 200-identical-subterm pathology and **nothing measurable on real
  modules**. On that pathology it also exhausts the default `maxSteps` where stock succeeds; raising `maxSteps` makes both succeed.
- A Lean bump needs a re-sync; the `SOURCE:` annotations give file and line range for every copied function.

**Open questions.** 1. Should the spec's `congr` kind (or a sibling) cover *user* `@[congr]` theorems? They have no
`CongrArgKind.cast`, so the current wording excludes them, yet they are the only remaining unresolved shape and `ite`/`dite` are
common. A replay would obtain the named theorem rather than `mkCongrSimp?`'s.
2. REVIEW-4 found a **T2-side** blocker: T2 elaborates a lemma before unifying it with the subterm, so
class-polymorphic lemmas like `add_zero` fail with a stuck instance problem where plain `rw` succeeds. `add_zero` is the first step
of four T1 fixtures, so T1 traces of ordinary Mathlib cannot replay until T2 resolves instances against the position.
