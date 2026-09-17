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
Nine are `private` upstream; every symbol their bodies reference is public, so nothing was blocked.

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

Pasted verbatim from the tool, run after the six modules. Nothing here is transcribed by hand: the count sentences were wrong
in three consecutive rounds.

```
$ python3 -B Experiment/check_simp_trace.py --report
| file | sites | traces | steps | kinds | bytes |
| --- | --- | --- | --- | --- | --- |
| `IsEmptyBasicTraced.lean` | 17 | 17 | 76 | `rw` 70, `unfold` 6 | 15250 |
| `NontrivialDefsTraced.lean` | 1 | 1 | 6 | `rw` 6 | 1109 |
| `FunctionDefsTraced.lean` | 2 | 3 | 17 | `rw` 13, `proj` 4 | 3013 |
| `ExistsUniqueTraced.lean` | 8 | 8 | 29 | `rw` 23, `beta` 4, `unfold` 2 | 5601 |
| `FunctionBasicTraced.lean` | 23 | 28 | 174 | `rw` 134, `proj` 17, `beta` 9, `intro_ctx` 8, `unfold` 4, `congr` 2 | 35049 |
| `LogicBasicTraced.lean` | 31 | 47 | 281 | `rw` 278, `unfold` 3 | 59118 |
| **total** | **82** | **104** | **583** | `rw` 524, `proj` 21, `unfold` 15, `beta` 13, `intro_ctx` 8, `congr` 2 | **119140** |
```

Timings are under **Checks** below; `Logic/Basic` against its stock original is 3.68 s vs 2.64 s, 720 MB vs 669 MB.

**All 82 sites compile with zero crashes, zero validation failures and no error other than the classified lines.** `sites` and
`traces` differ because a site under `by_cases <;>` runs once per branch, on a different goal, and each run now has its own trace
(round 9; previously the last branch silently overwrote the rest). Both numbers are the tool's. 24 classified lines: 12 are steps whose
own verdict the trace now carries (`--report` groups them by reason), the rest the transported-proof shape below.
`test/SimpTrace/make_traced.py` generates the traced copies and `check_transcription.py` verifies every source site was converted —
82 of 82, enforced, after an earlier generator silently dropped 9.

**REVIEW-3 items, all confirmed fixed by the round-4 reviewer.** C1 an unattributable firing is an `eq` step, never an
abort; `iota` gained an emitter. C2 fixed by deleting the search: chain depths 4–30 flat. M3 `(disch := omega)` records
`omega`. M4 both Mathlib calls trace. M5 Prop-valued lemmas carry `prop`. M6 no `#N` in any trace.

**Lemma-headed simproc proofs (spec 408a39b).** A simproc whose proof is one lemma applied is an ordinary `rw` naming that lemma, with the
discharged condition as a `side` sub-trace and `"source"` naming the simproc. `classifyProof` is **generic, never a table of simproc
names**: it walks the proof head's arguments against the lemma's own binder telescope, requiring every *explicit* argument to be a subterm
of the position, an instance, or a proof. Plumbing heads (`Eq.trans`/`Eq.mpr`/`Eq.symm`/ `of_eq_true`) are excluded, so those stay `eq`.

| simproc | proof head | verified replay shape |
| --- | --- | --- |
| `reduceIte` / `reduceDIte` | `ite_cond_eq_true`/`_false`, `dite_…` | `rw [ite_cond_eq_true 1 2 (eq_true h)]` |
| `+decide` / `Nat.reduceEqDiff` | `eq_true_of_decide` / `eq_false_of_decide` | `rw [eq_true_of_decide (rfl : decide _ = true)]` |
| `reduceCtorEq` | `eq_false'` | `exact eq_false' nofun` (round 4) |

Each replay shape was run in ordinary Lean; the round-4 reviewer confirmed `classifyProof` resisted all three fooling attempts.

## Earlier rounds (all verified fixed by later reviewers)

**Round 4.** `dsimpT` became a verbatim port of `transformWithCache` (telescope collected and `instantiateRev`'d, post step at
the telescope root, `skipInstances`, `usedLetOnly`, per-node `Core.checkSystem`), fixing `let` handling under every config. The
`Function/Basic:390` PANIC's root cause was `tryAutoCongrTheoremT?` pushing two `subst` entries where upstream pushes three,
leaving loose bvars that reached stock `rewritePost`; copied verbatim. `nofun` implemented from the condition's *type*;
unresolved-by-design cases split into `UnresolvedFixtures.lean`.

**Round 5.** `congr` kind (spec 3b17247): `tryAutoCongrTheoremT?` captures each `CongrArgKind` and emits one `congr` step at the
application's position with nested steps at relative positions. Fixing this exposed that every trace-frame access indexed
`[depth-1]!` under a `>= depth` guard, which panics at depth 0 — all are now total. `simp [h]` carried neither `local` nor
`prop`; `resolveStxOrigin` supplies both from the theorem's *proof*, never the syntax's characters. `propext` was named as the
rewriting lemma; it is plumbing, and the real lemma is the proof inside it. `dsimpT` now enters `withInDSimp`, so `dreduceIte`
can fire.

**Round 6.** User `@[congr]` (spec 2e73661): `trySimpCongrTheoremT?` emits one `rw` naming the theorem with one `side` per
hypothesis in order. Names were classified by *characters*, so every non-ASCII name lost `local`/`prop`. An explicit
class-typed argument was accepted but dropped, so replay synthesised a different instance; it is recorded in `args`. A dsimproc
firing became a `change` with `source`. `close.by` took the erased name where `intros` took the display form.

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

**C4** four stock-provable `Logic/Basic` calls crashed with `unexpected bound variable`: `eqUpToProofs` called `isProof` on
subterms with loose bvars under a dependent `dite`; it now descends with a real local, and a difference confined to a
transported proof is classified, not fatal. **C1** simp stores a quantified or conditional local's proof under a `.lam` and
already applied, so `proofLocal?` walks binders and applications to the head fvar; an origin that is neither a global nor a
local is classified `unresolved:origin`. **C2** a false positive on `exists_prop_congr` — the check unified the sides
left-to-right, stranding a higher-order `?q'`; both sides are now unified together. **C3** `describeProof` mapped any
`of_eq_true` proof to `close: "rfl"`. **M5** `Iff.mp`/`Iff.mpr` are not walked (their last argument proves the iff's left
side); `Eq.symm`/`Iff.symm` flip `dir`. Plus T2's two: every `change` carries `to`, every location `pre`/`post`.

## Round 8 fixes

**C1** 7 of 8 classified side conditions had a spec close form: round 7's `describeProof` asked what *proved* the goal, never
what the goal **was**, so a goal literally `True` or `¬False` was classified. `goalCloseForm?` inspects the goal first.
**C2** every `Ne`-stated lemma was rejected — `Ne` is a definition, so `not?` returned `none` on `0 ≠ 1` and the statement
became `(0 ≠ 1) = False`; unfolded with `whnfR` now. **C3** side-trace positions were the outer traversal's; events diverted
into a side frame are stripped to that frame's root, and the checker gained `check_side_positions`. I also built an in-tactic
replay of side steps against `pre` and **removed it after three attempts**: it produced false positives, and shipping a check
that misclassifies is worse than not having it. **M4** `args` are printed with `pp.proofs` and parenthesised; the checker
rejects any entry containing `⋯` or unbalanced delimiters. **M5** the traced copies silently dropped sites (two in
`Logic/Basic` per the reviewer; writing the checker first found 9 across three modules) — `make_traced.py` plus
`check_transcription.py` now enforce every site, 82 of 82. **m6–m8** the measurement section is the literal output of
`--report`; expected skeletons carry `pre`/`post`; a resolvable origin whose *statement* cannot be read is classified
`unreadable_rw_statement:<name>`.

## Round 9 fixes

Every number is a tool's output. End-to-end replay is the primary test: T4's harness
(`Experiment/pipeline/replay_module.py`) renders each trace and compiles it against T2.

| module | sites | replayed |
| --- | --- | --- |
| `Logic/IsEmpty/Basic.lean` | 17 | 15 |
| `Logic/Nontrivial/Defs.lean` | 1 | 1 |
| `Logic/Function/Defs.lean` | 2 | 1 |
| `Logic/ExistsUnique.lean` | 8 | 8 |
| `Logic/Function/Basic.lean` | 23 | 8 |
| `Logic/Basic.lean` | 31 | 14 |
| **total** | **82** | **47** |

Attribution of the 35 non-replayed: **harness 16, t1 19, t2 0** (T4's first run scored 45/82, t1 21). The 16 are
`render_failed:multiple_invocations`, which T4 attributes to its own renderer and which the per-invocation traces below make
fixable.

**1. Side goals (C1).** One code path: the side goal is the lemma hypothesis's instantiated type, `pre` its pp, positions
relative to it, and the close read off the goal **after** the recorded steps — reading the last step's `after` handed
`goalCloseForm?` a subterm (`False`) rather than the goal (`False = False`). Two further defects surfaced from replay, both
making a trace that elaborates rewrite the wrong thing:

- A simproc's nested `simp` calls *stock* `simpImpl`, so the fork's `withPos` never runs inside it and every diverted event
  arrives at the frame root with `pos = []`. A constant prefix gave three rewrites of three different subterms the same
  position; positions are now recovered from the subterm each event records, threading the goal, and refused when a subterm
  is absent or ambiguous.
- `assumption:<name>` renders as `exact <name>`, so the name must *prove* the goal. Stripping simp's `eq_true` wrapper to
  find the local and then reporting the bare local gave `exact hp` against `P = True`. The wrapper is kept.

**2. `name` is a name (C2, C3).** `rw.name` was the pretty-printed *syntax*, so 11 sites carried whole terms (`heq_comm
(a := a)`, `@forall_eq _ p a`, `if_neg fun h ↦ hb ⟨a, h⟩`). It now comes from the resolved origin — always a bare constant or
a local's display name — with `dir` still from the syntax, which is what carries a leading `←`. Resolving to the head fvar
alone would have lost the projection, so `proofLocal?` returns the path it walks (`h.2.1`, the order written). Arguments at
*implicit* binders are dropped: they cannot be written positionally and unification recovers them.

**3. Steps carry their own verdict.** A classified step was a compile-time `logError` only, invisible to anything reading the
JSON, so T4's renderer emitted six steps this tactic already knew could not replay. `Step` gains `unresolved`. Confirmed with
a scratch copy of T4's renderer honouring it: **t2 6 → 0**, all six were mine.

**4. `.stx` steps were never validated (C2).** `checkRwStep` got the *written* origin, `rwStatement?` reads no statement from
a `.stx`, and the `.stx` branch suppressed the report — so every step from `simp [h]` skipped the safety net entirely. It now
validates against the resolved origin, applies the recorded projection, and checks explicit binders against the **left-hand
side alone**, as `rw` does: unifying `after` too made this validator strictly more permissive than the tactic it protects, so
`dif_pos (hc : c)` shipped and failed at replay. Classified rose 16 → 24, all of it previously-unvalidated steps.

**5. Positions on partial applications (C4).** simp matches a lemma against a *prefix* and reapplies the rest, so
`h : Option.map f = Option.map g` rewrites the *function* of `Option.map f (some x)`: `[0,1]` → `[0,1,0]`, with `before`
trimmed to match. The descent is the surplus over the lemma's own LHS arity. Counting shared trailing arguments instead — my
first attempt — cannot tell this from a lemma rewriting a whole application with an untouched argument, and broke 5
ExistsUnique calls; the fixtures pin both shapes.

**6. Measurements (M5, M6).** `--report` now prints `sites` and `traces` separately and groups every classified step by
reason with its sites and shapes, so RESULT.md needs no hand-written reconciliation. The invented "two sites share a file"
sentence is gone.

New fixtures (72 total, none classified): `ite_cond_eq_false`, `dite_cond_eq_false`, a compound `p = False` side goal,
`heq_comm (a := a)`, `@forall_eq _ p a`, a partial application and a two-level one.

**Checks, all re-run from scratch after the last commit.** `lake build ExplicitLean.SimpTrace` with its oleans deleted: 11 s,
0 errors. `Fixtures.lean` exit 0 (72 fixtures, none classified); `UnresolvedFixtures.lean` exit 1 by design, 4 classified
lines. `python3 -B Experiment/check_simp_trace.py`: `OK: 72 ...`. `check_transcription.py`: OK, 82 of 82. The six modules,
`/usr/bin/time -l`: IsEmpty 2.44 s / 646 MB, Nontrivial 2.38 s / 637 MB, FunctionDefs 2.65 s / 648 MB, ExistsUnique 2.58 s /
651 MB, FunctionBasic 3.39 s / 712 MB, LogicBasic 3.68 s / 720 MB — nothing near 30 min or 40 GB.

**Known limitations.** `simpHaveTelescope` dispatches to *stock* `simp` through `MonadSimp SimpM`, so its inner rewrites have
no position and the whole rewrite is one `change`; redirecting it needs a change to that instance, outside this task. `eta` is
in the spec but never emitted — stock `reduceStep` does not eta-reduce in 4.32.2, so emitting it would diverge. The disabled
result cache costs 1.99x on a 200-identical-subterm pathology. A Lean bump needs a re-sync; the `SOURCE:` annotations give the
file and line range for every copied function.

**Open, not fixed.** 19 sites remain t1-attributed: `eq_true <lemma>` against a quantified Prop-valued lemma with no `args`
(4), unknown free variable from `hh _`/`hf _`-style instantiation (3), `unfold Ne` where the head is `Iff` (1), inaccessible
`h✝` rendering (1), and the `unassigned_explicit_argument` family (6) which is now honestly classified rather than shipped.
