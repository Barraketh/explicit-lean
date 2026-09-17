# T1-trace-capture: RESULT (T1b — forked traversal)

`simp_trace` runs a **fork of simp's own traversal** that records positions directly. Frontend unchanged and still substitutable for every
`simp` *simplification* form, plus a trailing `=>trace "<path>"` (else the JSON is logged); goal state mirrors `Meta.simpGoal`. `simp?` is
deliberately **not** covered: it is a suggestion tactic, not a simplification form.

## The fork — `ExplicitLean/SimpTrace/Traversal.lean` (~1200 lines, 43 `SOURCE:` annotations)

Copied from Lean 4.32.2 `src/lean/Lean/Meta/Tactic/Simp/`: the traversal of **Main.lean** (`reduceStep`, `reduce`, `unfold?`,
`reduceProjFn?`, `reduceFVar`, `dsimpImpl`, `simpProj`/`Const`/`Lambda`/`Arrow`/`Forall`/`Let`/`App`/`Step`, `visitFn`,
`congr`/`congrDefault`, `processCongrHypothesis`, `trySimpCongrTheorem?`, `simpLoop`, `simpImpl`, `withNewLemmas`, `lambdaTelescopeDSimp`
and helpers), the congruence machinery of **Types.lean** (`congrArgs`, `simpAppUsingCongr`, `tryAutoCongrTheorem?`, `mkCongr*`), and
**Transform.lean**'s `transformWithCache` (as `dsimpT`, round 4). Each carries a `SOURCE:` comment with its upstream file and line range.
Nine are `private` upstream; every symbol their bodies reference is public, so no `private`/`unsafe`/`@[implemented_by]` boundary had to
be reproduced.

**Stock and untouched:** everything deciding *what* simp does — `Simp.Methods` from the context, `Simp.rewrite?`, `Simp.Result`, simproc
tables, congruence lookup, `synthesizeArgs`, `mkCongrSimp?`. Two edits applied uniformly: every recursive `Simp.simp`/`Simp.dsimp` (an
`@[extern]` opaque that would dispatch to *stock* `simpImpl` and lose positions) becomes `simpT`/`dsimpT` with the child's position; and
stock `Methods` run under `withPos`.

**Threading.** `pos : Pos` is an explicit parameter on every copied function, extended per the spec (`app` 0/1, binder 0/1, `letE` 0/1/2,
`mdata`/`proj` 0). For an `n`-ary application argument `i` is at `0^(n-1-i) ++ [1]` (`argPos`/`fnPos`) — exactly the order
`simpAppUsingCongr`'s `visit` walks. A **binder stack** (`EvCtx.binders`) records the fvars the traversal substituted for term binders, so
the validator never infers them.

**Deliberate departures.** (1) The result **cache is disabled**: keyed on the expression alone, reuse at a second position would log
events nowhere or at the first. (2) Where stock simp is re-entered on a subterm the fork did not descend into — a simproc's own `simp c`,
`simpHaveTelescope`, a congruence hypothesis — those firings have no position, so they are **diverted** and the net change recorded
instead.

**Deleted.** `Position.lean` lost 327 of 404 lines (`findBridgeChain?`, `reducibleSites`, `refresh`, `findOccurrences`, `collectBridges`,
`solvePositions`, the no-op-match rule). What remains is navigation plus the **validator**: navigate `pos`, check the subterm equals
`before` (modulo proof irrelevance), substitute `after`, require the final term to equal simp's result. **No search anywhere in the
recorder.**

## Measurements

Pasted verbatim from `python3 -B Experiment/check_simp_trace.py --report`, run after the six modules. Nothing in this section is
transcribed by hand — the count sentences were wrong in three consecutive rounds, so the numbers are now the tool's output and nothing
else.

```
$ python3 -B Experiment/check_simp_trace.py --report
| file | calls | steps | kinds | bytes |
| --- | --- | --- | --- | --- |
| `IsEmptyBasicTraced.lean` | 17 | 76 | `rw` 70, `unfold` 6 | 15250 |
| `NontrivialDefsTraced.lean` | 1 | 6 | `rw` 6 | 1109 |
| `FunctionDefsTraced.lean` | 2 | 15 | `rw` 11, `proj` 4 | 2479 |
| `ExistsUniqueTraced.lean` | 8 | 29 | `rw` 23, `beta` 4, `unfold` 2 | 5601 |
| `FunctionBasicTraced.lean` | 23 | 135 | `rw` 104, `beta` 9, `intro_ctx` 8, `proj` 8, `unfold` 4, `congr` 2 | 27305 |
| `LogicBasicTraced.lean` | 31 | 163 | `rw` 160, `unfold` 3 | 33750 |
| **total** | **82** | **424** | `rw` 374, `unfold` 15, `beta` 13, `proj` 12, `intro_ctx` 8, `congr` 2 | **85494** |
```

Wall and RSS, `/usr/bin/time -l`, cold cache: IsEmpty 3.03 s / 647 MB, Nontrivial 2.82 s / 637 MB, FunctionDefs 3.02 s / 648 MB,
ExistsUnique 2.89 s / 652 MB, FunctionBasic 3.70 s / 713 MB, LogicBasic
4.32 s / 722 MB. `Logic/Basic` against its stock original: 4.32 s vs 2.64 s, 722 MB vs 669 MB.

**All 84 converted sites compile with zero crashes, zero validation failures and no error other than the classified lines** (82 traces;
two sites run under `by_cases <;>` and share a file); every goal state matches stock. 16 classified lines (6 in `FunctionBasic`, 10 in
`LogicBasic`) are all one shape: a proof term simp *transported* along a rewrite of that proof's own proposition, where the positions are
checked but the proof identity is not. `test/SimpTrace/make_traced.py` generates the traced copies and `check_transcription.py` verifies
every source site was converted — 84 of 84, enforced, after an earlier generator silently dropped 9.

**REVIEW-3 items, all confirmed fixed by the round-4 reviewer.** C1 an unattributable firing is an `eq` step whose `by` a scratch check
decides, never an abort; `iota` gained an emitter. C2 fixed by deleting the search: chain depths 4–30 flat, matching stock. M3 `(disch :=
omega)` records `close:{"by":"omega"}`. M4 both Mathlib calls trace; fixing (b) exposed that a non-dependent arrow is a binder node
binding no term variable, so `Expr.abstract`'s indices need padding. M5 Prop-valued lemmas carry `"prop"`. M6 no `#N` in any trace.

**Lemma-headed simproc proofs (spec 408a39b).** A simproc whose proof is one lemma applied is an ordinary `rw` naming that lemma, with the
discharged condition as a `side` sub-trace and `"source"` naming the simproc. `classifyProof` is **generic, never a table of simproc
names**: it walks the proof head's arguments against the lemma's own binder telescope, requiring every *explicit* argument to be a subterm
of the position, an instance, or a proof. Plumbing heads (`Eq.trans`/`Eq.mpr`/`Eq.symm`/ `of_eq_true`) are excluded, so those stay `eq`.

| simproc | proof head | verified replay shape |
| --- | --- | --- |
| `reduceIte` / `reduceDIte` | `ite_cond_eq_true`/`_false`, `dite_…` | `rw [ite_cond_eq_true 1 2 (eq_true h)]` |
| `+decide` / `Nat.reduceEqDiff` | `eq_true_of_decide` / `eq_false_of_decide` | `rw [eq_true_of_decide (rfl : decide _ = true)]` |
| `reduceCtorEq` | `eq_false'` | `exact eq_false' nofun` (round 4) |

Each replay shape was run in ordinary Lean; the heads are `ite_cond_eq_true`/`dite_cond_eq_true`, not `if_pos`/`dif_pos`. The round-4
reviewer confirmed `classifyProof` resisted all three fooling attempts.

**Earlier fixture-skeleton changes,** each the fork being more faithful: `contextual` emits `intro_ctx` (never emitted before); `zeta`
puts `zeta` first (verified against `trace.Debug.Meta.Tactic.simp`); `shadowed` emits three separate rewrites where the old trace merged
two occurrences; `ite` carries the simproc's nested rewrites as `side`.

## Earlier rounds (all verified fixed by later reviewers)

**Round 4.** `dsimpT` became a verbatim port of `transformWithCache` (telescope collected, bodies instantiated with `instantiateRev
fvars`, post step at the telescope root, `skipInstances`, `usedLetOnly`, per-node `Core.checkSystem`), which fixed the wrong post position
under a `let`. The `Function/Basic:390` PANIC's root cause was `tryAutoCongrTheoremT?`: its `eq` arm pushed two `subst` entries where
upstream pushes three, leaving loose bvars that reached stock `rewritePost`; loop and tail are now upstream's. `validate` compares with
`eqUpToProofs` (proof irrelevance, as upstream's `isDefEq` does) and instantiates mvars on both sides; instance arguments and binder types
are deliberately **not** weakened. `nofun` implemented from the condition's *type*. `Fixtures.lean` made a green gate, with
unresolved-by-design cases split into `UnresolvedFixtures.lean` and the checker compiling both itself.

**Round 5 (`congr` kind, spec 3b17247).** `tryAutoCongrTheoremT?` captures each `CongrArgKind.eq` argument's events and, when the theorem
transports a `CongrArgKind.cast` dependent, emits one `congr` step at the application's position carrying the argument index and its steps
at relative positions; otherwise the events are re-rooted and stay plain `rw`. `validateNested` independently replays the argument,
recursing through nested `congr`. Fixing this exposed that every trace-frame access indexed `[depth-1]!` under a `>= depth` guard, which
panics when `depth` is 0 — all are now total.

**Round 6 (user `@[congr]`, spec 2e73661).** `trySimpCongrTheoremT?` emits one `rw` naming the theorem with `"source": "congr"` and one
`side` per hypothesis in order; an implication-shaped hypothesis carries its antecedents in `intros`, as **display** names (`a✝`), never
`eraseMacroScopes`'d.

## Rounds 5 and 6 (verified fixed by later reviewers)

**Round 5.** `simp [h]` carried neither `local` nor `prop`; `resolveStxOrigin` supplies both while `name`/`dir` stay with the written
syntax. `propext` was called the rewriting lemma and emitted `rw [propext]`; it is plumbing, and for an `Iff` simproc the lemma is the
proof *inside* it. A `markUnresolved` beside an omitted `source` made a complete `eq` trace exit 1. `dsimpT` never entered `withInDSimp`,
so `dreduceIte` could not fire — observable: stock reduces `Fin (if True then 3 else 4)` to `Fin 3`. `--report` generates the counts.

**Round 6.** Names were classified by *characters*, so every non-ASCII name lost `local`/`prop`; the fvar is now read off the stored proof
term. An explicit class-typed argument was accepted but dropped, so replay synthesised a different instance; every explicit value argument
is recorded in `args`. The plumbing list was completed and `Iff.symm`/`Eq.symm` unwrapped with a direction flip. A dsimproc firing became
a `change` with `source`. `close.by` took the erased name where `intros` took the display form. Side traces gained `pre`/`post`.

## Structural check on every emitted `rw`

`isPlumbingHead` is an allowlist, and an allowlist has to be *complete* to be correct. It stays a fast path, but correctness rests on a
check that needs no completeness: for every emitted `rw` the validator re-elaborates `name` applied to `args` in the local context at that
position, opens the lemma's telescope so implicits, instances and conditional hypotheses become metavariables, unifies the rewritten side
with the recorded `before` (direction-aware, `prop`-flag-aware) and requires the other side to equal `after`. A failure is classified
`unresolved:unreplayable_rw:<name>`. A misclassified plumbing head therefore cannot ship as a `rw`, whether or not the allowlist names it
— `UnresolvedFixtures.lean` pins this with a *user-defined* plumbing head no allowlist could know about.

Subtleties the corpus forced, each surfaced by a step that demonstrably *does* replay failing the check: `args` excludes proof arguments
(they are `side` entries, not terms a replayer writes); recorded `args` go to the lemma's **explicit** binder positions, not to `mkAppN`;
`forallMetaTelescope` without reducing, and the conclusion read as written before any `whnfR` (reducing turns `LeftTotal R` into `∃ b, R a
b`); the extra-argument peel applies only to a rigid LHS; and both sides are unified **together**, since a higher-order metavariable in
one is determined by the other (round 7's C2).

## Round 7 fixes

**C4** four stock-provable `Logic/Basic` calls crashed with `unexpected bound variable`: `eqUpToProofs` called `isProof` on a subterm with
loose bvars under a dependent `dite`. It now descends with a real local, and a difference confined to a proof *transported* along a
rewrite of its own proposition is classified, not fatal. **C1** every quantified or conditional local lost `local`/`prop`, because simp
stores such a proof under a `.lam` and already applied; `proofLocal?` walks binders, applications and beta-redexes. An origin resolving to
neither a global nor a local is classified `unresolved:origin`. **C2** `unreplayable_rw:exists_prop_congr` was my false positive: the
check unified the sides left-to-right, stranding a higher-order `?q'` that the step's `side` traces determine. **C3** `describeProof`
mapped any `of_eq_true` proof to `close: "rfl"`, which cannot prove an opaque goal. **M5** `Iff.mp`/`Iff.mpr` are not walked (their last
argument proves the iff's left side); `Eq.symm`/`Iff.symm` flip `dir`. Plus T2's two: every `change` carries `to`, every location carries
`pre`/`post`, both pinned by the checker.

## Round 8 fixes

**C1 (critical) — 7 of 8 classified side conditions had a spec close form.** Round 7's fix asked what the side *proof* looked like and
never what the goal **was**, so a goal that is literally `True` or `¬False` was classified although the spec closes both. `goalCloseForm?`
inspects the goal: `True` → `true_intro`, `¬False`/`False → _` → `nofun`, `a = a` → `rfl`, otherwise classified. The six `Logic/Basic`
lines the reviewer showed replaying in plain Lean are gone.

**C2 (critical) — every `Ne`-stated lemma was rejected.** `Ne` is a *definition*, so `concl.not?` returned `none` on `0 ≠ 1` and the
statement became `(0 ≠ 1) = False`, which cannot unify with the recorded `before: "0 = 1"`. The `prop: false` arm now unfolds with
`whnfR`, as the arm below it already did. `Ne` is one of Mathlib's commonest simp shapes, so this was a systematic false-positive source.

**C3 (critical) — side-trace positions were the outer traversal's.** A side goal is its own root, and 11 side steps carried a position
that cannot exist in their goal — T2 rejects such a step by name. The events diverted into a side frame are rebased onto the side goal's
root, and the checker gained `check_side_positions`, which rejects a non-empty position in a side trace whose goal is atomic. I also tried
an in-tactic replay of side steps against `pre` and **removed it after three attempts**: it produced false positives the positional check
does not, and shipping a check that misclassifies is worse than not having it.

**M4 (major) — `args` were unparenthesised and could contain `⋯`.** They are terms a replayer writes, so they are now printed with
`pp.proofs` (the default elides a proof as `⋯`, which cannot be elaborated at all) and parenthesised unless atomic. The checker rejects
any entry containing `⋯` or unbalanced delimiters.

**M5 (major) — the traced copies silently dropped sites.** Two in `Logic/Basic`, as the review found — and the same generator bug hid 7
more in two other modules. `test/SimpTrace/make_traced.py` now generates the copies and `test/SimpTrace/check_transcription.py` counts
source sites against converted ones and fails on mismatch; both are committed, and all **84 of 84** sites convert. No traced copy contains
a live `simp`.

**m6–m8.** The measurement section is now the literal output of `--report` with its command line, because the count sentences were wrong
three rounds running. Expected skeletons carry `pre`/`post`, so that claim is true of them and not only of the emitted traces. A
resolvable origin whose *statement* cannot be read is classified `unreadable_rw_statement:<name>` rather than passing — round 7's "none is
never a pass" held for origins only.

**Proposed spec addition.** `goalCloseForm?` covers every close the corpus needs today. If a side goal appears that is `¬p` for a
non-`False` `p`, the spec has no form for it; `exact not_false` would be the provisional rendering, but no such goal occurs in the six
modules, so nothing is emitted for it yet.

**Checks, all re-run from scratch.** `lake build ExplicitLean.SimpTrace` with oleans deleted: clean, no warnings, 10.66 s, 752 MB.
`Fixtures.lean`: **exit 0**. `UnresolvedFixtures.lean`: exits 1 by design, 4 classified lines. `python3 -B
Experiment/check_simp_trace.py`: `OK: 65 ...`; it compiles the fixtures itself, and its assertions (a positive fixture must exit 0; a
`congr` step's nested positions; a side trace's `intros`, `pre` and `post`; `local`/`args` where expected) were each verified to fire on a
regression. The five measurement modules: see the table. Nothing came near 30 minutes or 40 GB.

**Known limitations.** The 14 classified unresolved across 75 calls are three shapes, all gaps in what the validator can *confirm* rather
than wrong traces:

- **A transported proof term** (8): simp rewrites a proposition and carries a proof of it along; the recorded proof still has the old
  type. Positions are checked, proof identity is not.
- **A side condition rewritten to `True`** (6): simp's default discharger proves it with other lemmas, whose steps are diverted and carry
  no position, so no close form can be named honestly.
- **`simpHaveTelescope`** dispatches to *stock* `simp` through `MonadSimp SimpM`, so its inner rewrites carry no position; the telescope
  rewrite is one `change`. Redirecting it needs a change to that instance, outside this task's ownership.
- `eta` is in the spec but **never emitted**: stock `reduceStep` does not perform eta reduction (its `-- TODO: eta reduction` is still
  there in 4.32.2), so emitting it would diverge from stock simp.
- The disabled result cache costs 1.99x on the reviewer's 200-identical-subterm pathology and **nothing measurable on real modules**. On
  that pathology it also exhausts the default `maxSteps` where stock succeeds; raising `maxSteps` makes both succeed.
- A Lean bump needs a re-sync; the `SOURCE:` annotations give file and line range for every copied function.

**Open questions.** 1. REVIEW-4 found a **T2-side** blocker: T2 elaborates a lemma before unifying it with the subterm, so
class-polymorphic lemmas like `add_zero` fail with a stuck instance problem where plain `rw` succeeds. `add_zero` is the first step of
four T1 fixtures, so T1 traces of ordinary Mathlib cannot replay until T2 resolves instances against the position.
