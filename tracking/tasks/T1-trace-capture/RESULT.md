# T1-trace-capture: RESULT (T1b — forked traversal)

`simp_trace` runs a **fork of simp's own traversal** that records positions directly. Frontend unchanged and still substitutable
(every `simp` argument form plus a trailing `=>trace "<path>"`, else the JSON is logged); goal state mirrors `Meta.simpGoal`.

## The fork — `ExplicitLean/SimpTrace/Traversal.lean` (~1200 lines, 43 `SOURCE:` annotations)

Copied from Lean 4.32.2 `src/lean/Lean/Meta/Tactic/Simp/`: the traversal of **Main.lean** (`reduceStep`, `reduce`, `unfold?`,
`reduceProjFn?`, `reduceFVar`, `dsimpImpl`, `simpProj`/`Const`/`Lambda`/`Arrow`/`Forall`/`Let`/`App`/`Step`, `visitFn`,
`congr`/`congrDefault`, `processCongrHypothesis`, `trySimpCongrTheorem?`, `simpLoop`, `simpImpl`, `withNewLemmas`,
`lambdaTelescopeDSimp` and helpers), the congruence machinery of **Types.lean** (`congrArgs`, `simpAppUsingCongr`,
`tryAutoCongrTheorem?`, `mkCongr*`), and **Transform.lean**'s `transformWithCache` (as `dsimpT`, round 4). Each carries a
`SOURCE:` comment with its upstream file and line range. Nine are `private` upstream; every symbol their bodies reference is
public, so no `private`/`unsafe`/`@[implemented_by]` boundary had to be reproduced.

**Stock and untouched:** everything deciding *what* simp does — `Simp.Methods` from the context, `Simp.rewrite?`, `Simp.Result`,
simproc tables, congruence lookup, `synthesizeArgs`, `mkCongrSimp?`. Two edits applied uniformly: every recursive
`Simp.simp`/`Simp.dsimp` (an `@[extern "lean_simp"]` opaque that would dispatch to *stock* `simpImpl` and lose positions) becomes
`simpT`/`dsimpT` with the child's position; and stock `Methods` run under `withPos`.

**Threading.** `pos : Pos` is an explicit parameter on every copied function, extended per the spec (`app` 0/1, binder 0/1, `letE`
0/1/2, `mdata`/`proj` 0). For an `n`-ary application argument `i` is at `0^(n-1-i) ++ [1]` (`argPos`/`fnPos`) — exactly the order
`simpAppUsingCongr`'s `visit` walks. A **binder stack** (`EvCtx.binders`) records the fvars the traversal substituted for term
binders, so the validator never infers them.

**Deliberate departures.** (1) The result **cache is disabled**: keyed on the expression alone, reuse at a second position would
log events nowhere or at the first. (2) Where stock simp is re-entered on a subterm the fork did not descend into — a simproc's
own `simp c`, `simpHaveTelescope`, a congruence hypothesis — those firings have no position, so they are **diverted** and the net
change recorded instead.

**Deleted.** `Position.lean` lost 327 of 404 lines (`findBridgeChain?`, `reducibleSites`, `refresh`, `findOccurrences`,
`collectBridges`, `solvePositions`, the no-op-match rule). What remains is navigation plus the **validator**: navigate `pos`,
check the subterm equals `before` (modulo proof irrelevance), substitute `after`, require the final term to equal simp's result.
**No search anywhere in the recorder.**

## Measurements (macOS, Lean 4.32.2; outputs gitignored; cold-cache figures)

| file | calls | traced | steps | kinds | bytes | wall | stock | peak RSS | unres. |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `IsEmptyBasicTraced.lean` | 17 | 17 | 76 | `rw` 70, `unfold` 6 | 15 045 | 2.58 s | — | 677 MB | 0 |
| `NontrivialDefsTraced.lean` | 1 | 1 | 6 | `rw` 6 | 1 109 | 2.52 s | — | 638 MB | 0 |
| `FunctionDefsTraced.lean` | 1 | 1 | 12 | `rw` 8, `proj` 4 | 1 878 | 2.68 s | — | 646 MB | 0 |
| `ExistsUniqueTraced.lean` | 8 | 8 | 29 | `rw` 23, `beta` 4, `unfold` 2 | 5 601 | 2.70 s | — | 651 MB | 1 |
| `FunctionBasicTraced.lean` | 19 | 19 | 102 | `rw` 76, `beta` 7, `proj` 5, `intro_ctx` 8, `unfold` 4, `change` 2 | 20 070 | 3.84 s | 2.62 s | 743 MB | 5 |

**Every call stock simp proves traces: 46 of 46**, none leaves a goal stock closes, no panics, no validation failures. The 6
unresolved are all congruence transports. The four committed corpora reproduce their earlier tallies exactly.

**REVIEW-3 items, all confirmed fixed by the round-4 reviewer.** C1 an unattributable firing is an `eq` step whose `by` a scratch
check decides, never an abort; `iota` gained an emitter. C2 fixed by deleting the search: chain depths 4–30 flat, matching stock.
M3 `(disch := omega)` records `close:{"by":"omega"}`. M4 both Mathlib calls trace; fixing (b) exposed that a non-dependent arrow
is a binder node binding no term variable, so `Expr.abstract`'s indices need padding. M5 Prop-valued lemmas carry `"prop"`.
M6 no `#N` in any trace.

**Lemma-headed simproc proofs (spec 408a39b).** A simproc whose proof is one lemma applied is an ordinary `rw` naming that
lemma, with the discharged condition as a `side` sub-trace and `"source"` naming the simproc. `classifyProof` is **generic, never
a table of simproc names**: it walks the proof head's arguments against the lemma's own binder telescope, requiring every
*explicit* argument to be a subterm of the position, an instance, or a proof. Plumbing heads (`Eq.trans`/`Eq.mpr`/`Eq.symm`/
`of_eq_true`) are excluded, so those stay `eq`.

| simproc | proof head | verified replay shape |
| --- | --- | --- |
| `reduceIte` / `reduceDIte` | `ite_cond_eq_true`/`_false`, `dite_…` | `rw [ite_cond_eq_true 1 2 (eq_true h)]` |
| `+decide` / `Nat.reduceEqDiff` | `eq_true_of_decide` / `eq_false_of_decide` | `rw [eq_true_of_decide (rfl : decide _ = true)]` |
| `reduceCtorEq` | `eq_false'` | `exact eq_false' nofun` (round 4) |

Each replay shape was run in ordinary Lean; the heads are `ite_cond_eq_true`/`dite_cond_eq_true`, not `if_pos`/`dif_pos`. The
round-4 reviewer confirmed `classifyProof` resisted all three fooling attempts.

**Earlier fixture-skeleton changes,** each the fork being more faithful: `contextual` emits `intro_ctx` (never emitted before);
`zeta` puts `zeta` first (verified against `trace.Debug.Meta.Tactic.simp`); `shadowed` emits three separate rewrites where the
old trace merged two occurrences; `ite` carries the simproc's nested rewrites as `side`.

## Round 4 fixes

**1 (critical) — `let` under every config.** `dsimpT` was a hand-written traversal, not a port of `transformWithCache`. It is now
the latter verbatim: `visitLambda`/`visitForall`/`visitLet` collect the whole telescope, instantiate each body with
`instantiateRev fvars`, and run the post step on the term rebuilt by `mkLambdaFVars` **at the telescope root**. That fixes the
wrong post position under a binder. `simpLetT` no longer desyncs the validator: a `letToHave` conversion is recorded as a `change`
at the position, and `simpHaveTelescope` — which runs *stock* simp on the telescope bodies through the `MonadSimp SimpM` instance,
so its firings have no position — has its events diverted and the net rewrite recorded as one `change`, with the call classified
unresolved. Fixtures: both reviewer shapes under `zeta := true` and `zeta := false`, plus the `zetaDelta` shape; all five verified
to be proved by stock with the same goal state.

**2 (critical) — the PANIC.** Root cause was **not** the binder path but `tryAutoCongrTheoremT?`: its `eq` arm pushed two `subst`
entries where upstream pushes three (`arg`, `argResult.expr`, `argProof`), and the tail read `type.appArg!.instantiateRev subst`
instead of destructuring `type.instantiateRev subst |>.eq?`. The misaligned `subst` left loose bvars in the rhs, which reached
stock `rewritePost`. Loop and tail are now upstream's, including `getProof'`, `removeUnnecessaryCasts` and the `hasProof` branch.
Found by asserting closedness at every stock-method entry; those assertions now pass and **no corpus produces a panic**.

**3 (major) — `dsimp` fidelity and the validator.** Restored verbatim: `skipInstances := !cfg.instances` via `getFunInfoNArgs`,
`usedLetOnly := cfg.zeta || cfg.zetaUnused` on every rebuild, per-node `Core.checkSystem "transform"`. The five validation
failures are gone. Two causes, both fixed at the source rather than by loosening the check: (a) a congruence theorem rewrites its
hypotheses' subterms *and* transports everything depending on them (`ite_congr` carries the `Decidable` instance and the branch
binder types), so `trySimpCongrTheoremT?` now diverts the hypothesis rewrites and records the node's whole change as one `change`
— this also fixed `:976`, whose recorded `before` was a strictly wrong position; (b) `validate` compares with `eqUpToProofs`,
structural equality with proof subterms compared by type, because upstream's own `isDefEq` runs with `proofIrrelevance := true`
and rejecting `Classical.choose h` against `Classical.choose ⋯` made the validator stricter than the engine it checks. Instance
arguments and binder types are deliberately **not** weakened. `validate` also instantiates metavariables on both sides: an
instance argument can still be an unassigned `?m` when a step is recorded and be assigned later.

**4 (major) — the fixture gate.** `Fixtures.lean` exits 0 once defect 5 lands. To stop a nonzero exit being reported as a pass
again, `check_simp_trace.py` compiles the positive fixtures itself and fails on any nonzero exit — verified to fire. Calls
unresolved *by design* moved to `test/SimpTrace/UnresolvedFixtures.lean`, whose traces are still compared and which must report at
least one classified line, so a fixture that silently stopped being unresolved is caught too.

**5 (major) — `nofun`.** `assumptionName?` recognises a condition proof refutable by empty pattern matching from its **type**
(one hypothesis, an equation between distinct constructors) rather than from the `noConfusion` term's shape, an implementation
detail. `reduceCtorEq` records `close:{"by":"nofun"}`; replay is `exact eq_false' nofun`.

**6 (minor)** an `eq` step whose firing registered no origin no longer carries the placeholder `"source":"simproc"`; the field is
omitted and the call classified. **7 (minor)** `simpLoopT` takes one `reduceStep` (`reduceOnce`) as upstream, not a fixpoint, so
`maxSteps` is charged per reduction.

**Checks, all re-run from scratch.** `lake build ExplicitLean.SimpTrace` with oleans deleted: clean, no warnings, 10.17 s, 737 MB.
`Fixtures.lean` (38 traces): **exit 0**, 3.22 s, 1 512 MB. `UnresolvedFixtures.lean`: exits 1 by design, 1 classified line.
`python3 -B Experiment/check_simp_trace.py`: `OK: 38 ...`, 14.76 s; it now compiles the fixtures itself, and both its newer
assertions (a `rw` with a `source` must carry a `side`; a positive fixture must exit 0) were verified to fire on a regression.
`IsEmptyBasicTraced.lean`: pass 17/17, 2.58 s, 677 MB. The five measurement modules: see the table. Nothing came near 30 minutes
or 40 GB.

**Known limitations.**

- **Congruence transports are recorded as one `change`, not as the individual rewrites** (6 of 46 calls).
  `ite_congr`/`dite_congr`/`exists_prop_congr` rewrite a subterm *and* transport the arguments depending on it; the transport has
  no position in the spec's convention. The trace is sound and validates, but a replayer gets a defeq assertion where simp made a
  rewrite. This is the largest remaining gap.
- **`simpHaveTelescope`** simplifies a `have` telescope through `MonadSimp SimpM`, which dispatches to *stock* `simp`; its inner
  rewrites carry no position, so the telescope rewrite is one `change` and the call is classified. Redirecting it would need a
  change to that instance, outside this task's ownership.
- `eta` is in the spec but **never emitted**: stock `reduceStep` does not perform eta reduction (its `-- TODO: eta reduction` is
  still there in 4.32.2), so emitting it would diverge from stock simp.
- The disabled result cache costs 1.99x on the reviewer's 200-identical-subterm pathology and **nothing measurable on real
  modules** (0.82x–1.47x). On that pathology it also exhausts the default `maxSteps` where stock succeeds, because each identical
  subterm is re-simplified; raising `maxSteps` makes both succeed.
- A Lean bump needs a re-sync; the `SOURCE:` annotations give file and line range for every copied function.

**Open questions.** 1. Should the spec gain a position form, or a dedicated kind, for a congruence theorem's transported
arguments? That is the only thing keeping the 6 unresolved calls unresolved, and the shape is common. 2. `ctxIndex` is
`LocalDecl.index` and (per REVIEW-3) is not a `rename_i` argument; worth saying so in the spec. 3. REVIEW-4 found a **T2-side**
blocker worth flagging: T2 elaborates a lemma before unifying it with the subterm, so class-polymorphic lemmas like `add_zero`
fail with a stuck instance problem where plain `rw` succeeds. `add_zero` is the first step of four T1 fixtures, so T1 traces of
ordinary Mathlib cannot replay until T2 resolves instances against the position.
