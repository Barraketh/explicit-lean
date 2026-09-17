# T1-trace-capture: RESULT (T1b — forked traversal)

`simp_trace` runs a **fork of simp's own traversal** that records positions directly. Frontend unchanged and still substitutable
for every `simp` *simplification* form, plus a trailing `=>trace "<path>"` (else the JSON is logged); goal state mirrors
`Meta.simpGoal`. `simp?` is deliberately **not** covered: it is a suggestion tactic, not a simplification form.

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
`Simp.simp`/`Simp.dsimp` (an `@[extern]` opaque that would dispatch to *stock* `simpImpl` and lose positions) becomes `simpT`/`dsimpT`
with the child's position; and stock `Methods` run under `withPos`.

**Threading.** `pos : Pos` is an explicit parameter on every copied function, extended per the spec (`app` 0/1, binder 0/1, `letE`
0/1/2, `mdata`/`proj` 0). For an `n`-ary application argument `i` is at `0^(n-1-i) ++ [1]` (`argPos`/`fnPos`) — exactly the order
`simpAppUsingCongr`'s `visit` walks. A **binder stack** (`EvCtx.binders`) records the fvars the traversal substituted for term
binders, so the validator never infers them.

**Deliberate departures.** (1) The result **cache is disabled**: keyed on the expression alone, reuse at a second position would log
events nowhere or at the first. (2) Where stock simp is re-entered on a subterm the fork did not descend into — a simproc's own `simp
c`, `simpHaveTelescope`, a congruence hypothesis — those firings have no position, so they are **diverted** and the net change
recorded instead.

**Deleted.** `Position.lean` lost 327 of 404 lines (`findBridgeChain?`, `reducibleSites`, `refresh`, `findOccurrences`,
`collectBridges`, `solvePositions`, the no-op-match rule). What remains is navigation plus the **validator**: navigate `pos`, check
the subterm equals `before` (modulo proof irrelevance), substitute `after`, require the final term to equal simp's result. **No search
anywhere in the recorder.**

## Measurements (macOS, Lean 4.32.2; outputs gitignored; cold-cache figures)

Counts, kinds and bytes below are **generated** by `python3 -B Experiment/check_simp_trace.py --report` from
the traces the five modules write, so they cannot drift from the tree again (REVIEW-5 5). Nested `congr` and
`side` steps are counted, since a replayer must perform them. Wall and RSS are from `/usr/bin/time -l`.

| file | calls | steps | kinds | bytes | wall | peak RSS | unres. |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `IsEmptyBasicTraced.lean` | 17 | 76 | `rw` 70, `unfold` 6 | 15045 | 2.23 s | 646 MB | 0 |
| `NontrivialDefsTraced.lean` | 1 | 6 | `rw` 6 | 1109 | 2.19 s | 637 MB | 0 |
| `FunctionDefsTraced.lean` | 1 | 12 | `rw` 8, `proj` 4 | 1878 | 2.35 s | 646 MB | 0 |
| `ExistsUniqueTraced.lean` | 8 | 29 | `rw` 23, `beta` 4, `unfold` 2 | 5601 | 2.38 s | 650 MB | 0 |
| `FunctionBasicTraced.lean` | 19 | 106 | `rw` 80, `intro_ctx` 8, `beta` 7, `proj` 5, `unfold` 4, `congr` 2 | 20688 | 2.78 s | 710 MB | 0 |
| **total** | **46** | **229** | `rw` 187, `unfold` 12, `beta` 11, `proj` 9, `intro_ctx` 8, `congr` 2 | **44321** | — | — | **0** |

**Every call stock simp proves traces: 46 of 46**, with zero unresolved, zero validation failures, zero
panics and zero other errors across the five modules; every goal state matches stock. Two fixtures are
unresolved *by design* and live in `UnresolvedFixtures.lean`, which exits 1 on purpose.

**REVIEW-3 items, all confirmed fixed by the round-4 reviewer.** C1 an unattributable firing is an `eq` step whose `by` a scratch
check decides, never an abort; `iota` gained an emitter. C2 fixed by deleting the search: chain depths 4–30 flat, matching stock. M3
`(disch := omega)` records `close:{"by":"omega"}`. M4 both Mathlib calls trace; fixing (b) exposed that a non-dependent arrow is a
binder node binding no term variable, so `Expr.abstract`'s indices need padding. M5 Prop-valued lemmas carry `"prop"`. M6 no `#N` in
any trace.

**Lemma-headed simproc proofs (spec 408a39b).** A simproc whose proof is one lemma applied is an ordinary `rw` naming that lemma, with
the discharged condition as a `side` sub-trace and `"source"` naming the simproc. `classifyProof` is **generic, never a table of
simproc names**: it walks the proof head's arguments against the lemma's own binder telescope, requiring every *explicit* argument to
be a subterm of the position, an instance, or a proof. Plumbing heads (`Eq.trans`/`Eq.mpr`/`Eq.symm`/ `of_eq_true`) are excluded, so
those stay `eq`.

| simproc | proof head | verified replay shape |
| --- | --- | --- |
| `reduceIte` / `reduceDIte` | `ite_cond_eq_true`/`_false`, `dite_…` | `rw [ite_cond_eq_true 1 2 (eq_true h)]` |
| `+decide` / `Nat.reduceEqDiff` | `eq_true_of_decide` / `eq_false_of_decide` | `rw [eq_true_of_decide (rfl : decide _ = true)]` |
| `reduceCtorEq` | `eq_false'` | `exact eq_false' nofun` (round 4) |

Each replay shape was run in ordinary Lean; the heads are `ite_cond_eq_true`/`dite_cond_eq_true`, not `if_pos`/`dif_pos`. The round-4
reviewer confirmed `classifyProof` resisted all three fooling attempts.

**Earlier fixture-skeleton changes,** each the fork being more faithful: `contextual` emits `intro_ctx` (never emitted before); `zeta`
puts `zeta` first (verified against `trace.Debug.Meta.Tactic.simp`); `shadowed` emits three separate rewrites where the old trace
merged two occurrences; `ite` carries the simproc's nested rewrites as `side`.

## Rounds 4–6 (all verified fixed by the round-5 reviewer)

**Round 4.** `dsimpT` became a verbatim port of `transformWithCache` (telescope collected, bodies
instantiated with `instantiateRev fvars`, post step at the telescope root, `skipInstances`, `usedLetOnly`,
per-node `Core.checkSystem`), which fixed the wrong post position under a `let`. The `Function/Basic:390`
PANIC's root cause was `tryAutoCongrTheoremT?`: its `eq` arm pushed two `subst` entries where upstream pushes
three, leaving loose bvars that reached stock `rewritePost`; loop and tail are now upstream's. `validate`
compares with `eqUpToProofs` (proof irrelevance, as upstream's `isDefEq` does) and instantiates mvars on both
sides; instance arguments and binder types are deliberately **not** weakened. `nofun` implemented from the
condition's *type*. `Fixtures.lean` made a green gate, with unresolved-by-design cases split into
`UnresolvedFixtures.lean` and the checker compiling both itself.

**Round 5 (`congr` kind, spec 3b17247).** `tryAutoCongrTheoremT?` captures each `CongrArgKind.eq` argument's
events and, when the theorem transports a `CongrArgKind.cast` dependent, emits one `congr` step at the
application's position carrying the argument index and its steps at relative positions; otherwise the events
are re-rooted and stay plain `rw`. `validateNested` independently replays the argument, recursing through
nested `congr`. Fixing this exposed that every trace-frame access indexed `[depth-1]!` under a `>= depth`
guard, which panics when `depth` is 0 — all are now total.

**Round 6 (user `@[congr]`, spec 2e73661).** `trySimpCongrTheoremT?` emits one `rw` naming the theorem with
`"source": "congr"` and one `side` per hypothesis in order; an implication-shaped hypothesis carries its
antecedents in `intros`, as **display** names (`a✝`), never `eraseMacroScopes`'d.

## Round 5 fixes

**1 (critical) — `simp [h]` carried neither `local` nor `prop`.** simp records a hypothesis named in the
argument list as `Origin.stx`, the syntax the user wrote, where `simp [*]` produces `Origin.fvar`; both
`originName` and `originIsEquational` fell through their `.stx` arms. `resolveStxOrigin` resolves the written
identifier in the local context live at the firing — a lookup, not a search: scanning the theorem trees is a
20 000-entry walk per step, and `Origin`'s structural `==` compares the stored `Syntax`, which differs from
the trace's copy. The resolved origin supplies `local` and `prop` **only**; `name` and `dir` stay with the
written syntax, because only the syntax carries a leading `←`. Resolving it wholesale silently turned
`simp [← h]` into a forward rewrite — caught by diffing against the pre-change behaviour, not by a test.

**2 (critical) — `classifyProof` accepted `propext` as the rewriting lemma.** `propext` has one explicit
argument and it is a proof, so the generic walk emitted `rw [propext]`, which no replayer can execute. It is
plumbing exactly as `Eq.mpr`/`of_eq_true` are and now heads `isPlumbingHead` together with `Eq.mp`,
`eq_true`, `eq_false`, `eq_self`, `Iff.intro`/`mp`/`mpr`, `iff_of_eq`, `Eq.subst`, `Eq.ndrec`. For an `Iff`
simproc the rewriting lemma is the proof *inside* `propext`, so one level is unwrapped and classified; a
non-lemma inner proof — Mathlib's `existsAndEq` builds `Iff.intro` — stays `eq`, and the call is the spec's
classified `unresolved:simproc:<name>`. Fixtures: a `propext`-wrapped lemma simproc (positive) and a
`Iff.intro`-proof simproc (negative control, in `UnresolvedFixtures.lean`).

**3 (major) — a complete `eq` trace exited 1.** Round 4's `markUnresolved` beside the omitted `source`
placeholder marked a replayable `eq`/`by:"rfl"` step unresolved, reintroducing REVIEW-3 C1 through the back
door. `source` is optional provenance; the mark is dropped and the omission kept.

**4 (major) — `dsimpT` never entered `withInDSimp`.** Upstream's `dsimpImpl` ends in
`withInDSimpWithCache`, which sets `Context.inDSimp` as well as swapping the cache; stock `dreduceIte`/
`dreduceDIte` read that flag and return `.continue` unless it is set. Now wrapped verbatim. **Contrary to the
review's expectation this is observable**: stock reduces `Fin (if True then 3 else 4)` to `Fin 3` and the
fork did not, which is the new `dreduce_ite` fixture. Entering `withInDSimp` then exposed a latent
double-log — `instrumentD` and `logDStep` both recorded an attributable dsimproc firing — which desynced the
validator; `logDStep` now defers when the stock call already logged.

**5 (major) — RESULT.md's numbers had drifted.** `check_simp_trace.py --report` generates the measurement
table from the committed traces, counting nested `congr` and `side` steps, and the table above is its output.
The reviewer's independent tally (ExistsUnique 29 / 5 601, FunctionBasic 20 553) matches it exactly. Stale
claims removed: the "user `@[congr]` transports as `change`" limitation was superseded in round 6 and no
`change` step appears in any measurement trace; the "none is unresolved" headline now says plainly that two
fixtures are unresolved by design.

**6 (minor)** a side trace with no close is under-determined. Left as is: adding `post` to `SideTrace` is a
spec bump, and T2 supplies the terminal tactic from its own `with [...]` entry. Raised as open question 1.
**7 (minor)** `procDepth` was maintained in four places and read nowhere — deleted; the diversion decision
keys on `procEvents.size`, which `captureEvents` and `withDivertedEvents` both maintain. **8 (minor)**
`simp_trace?` does not exist and is not planned: `simp?` is a suggestion tactic, not a simplification form.
Stated as an exclusion below.

**Checks, all re-run from scratch.** `lake build ExplicitLean.SimpTrace` with oleans deleted: clean, no warnings, 10.08 s, 743 MB.
`Fixtures.lean` (40 traces): **exit 0**. `UnresolvedFixtures.lean`: exits 1 by design, 1 classified line. `python3 -B
Experiment/check_simp_trace.py`: `OK: 40 ...`; it compiles the fixtures itself, and its three assertions (a `rw` with a `source` must
carry a `side`; a positive fixture must exit 0; a `congr` step's nested positions) were each verified to fire on a regression. The
five measurement modules: see the table. Nothing came near 30 minutes or 40 GB.

**Known limitations.**

- **User `@[congr]` transports are recorded as one `change`** (6 of 46 calls): `ite_congr`, `dite_congr`, `exists_prop_congr`. The
  trace is sound and validates, but a replayer gets a defeq assertion where simp made a rewrite. The spec's `congr` kind does not
  cover these (Round 5); this is the largest remaining gap.
- **`simpHaveTelescope`** simplifies a `have` telescope through `MonadSimp SimpM`, which dispatches to *stock* `simp`; its inner
  rewrites carry no position, so the telescope rewrite is one `change` and the call is classified. Redirecting it would need a change
  to that instance, outside this task's ownership.
- `eta` is in the spec but **never emitted**: stock `reduceStep` does not perform eta reduction (its `-- TODO: eta reduction` is still
  there in 4.32.2), so emitting it would diverge from stock simp.
- The disabled result cache costs 1.99x on the reviewer's 200-identical-subterm pathology and **nothing measurable on real modules**.
  On that pathology it also exhausts the default `maxSteps` where stock succeeds; raising `maxSteps` makes both succeed.
- A Lean bump needs a re-sync; the `SOURCE:` annotations give file and line range for every copied function.

**Open questions.** 1. Should the spec's `congr` kind (or a sibling) cover *user* `@[congr]` theorems? They have no
`CongrArgKind.cast`, so the current wording excludes them, yet they are the only remaining unresolved shape and `ite`/`dite` are
common. A replay would obtain the named theorem rather than `mkCongrSimp?`'s.
2. REVIEW-4 found a **T2-side** blocker: T2 elaborates a lemma before unifying it with the subterm, so
class-polymorphic lemmas like `add_zero` fail with a stuck instance problem where plain `rw` succeeds. `add_zero` is the first step of
four T1 fixtures, so T1 traces of ordinary Mathlib cannot replay until T2 resolves instances against the position.
