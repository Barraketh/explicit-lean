# T1-trace-capture: adversarial review, round 5 (T1b forked traversal)

Scratch for this round is `/private/tmp/t1r5/`, not committed. Working tree clean before and
after; `git status --porcelain` empty. All Lean compiles run serially.

**All seven REVIEW-4 items reproduce as fixed or classified.** Item 2 — the `Function/Basic:390`
PANIC — is genuinely gone: the theorem now traces with two `congr` steps and no panic
(`lake env lean /private/tmp/t1r5/PanicT3.lean`, exit 0). Items 3, 5, 6, 7 are fixed at the
source (`skipInstances`/`usedLetOnly`/`Core.checkSystem "transform"` restored verbatim;
`nofun` implemented and in the checker's `CLOSE_EXACT`; the `"simproc"` placeholder gone;
`simpLoopT` takes **one** `reduceOnce`). Item 4 is fixed: `Fixtures.lean` exits 0. Item 1(b)
(`letToHave` desync) is fixed. Item 1(a) is not fixed but **reclassified**: it is now a
classified `unresolved` in `UnresolvedFixtures.lean` rather than a validation failure — a
legitimate spec outcome, but see defect 3 for what RESULT.md still claims about it.

The defects below are new. All were found outside the committed corpus.

---

## 1. CRITICAL — `simp_trace [h]` on a local hypothesis emits neither `prop` nor `local`

`ExplicitLean/SimpTrace/Tactic.lean:141-164` (`originName`), with
`ExplicitLean/SimpTrace/Recorder.lean:81-108` (`originIsEquational`/`propFlag?`).

When a local hypothesis is named in the argument list, simp records the origin as
`Origin.stx` (the syntax the user wrote), not `Origin.fvar`. Both `originName` and
`originIsEquational` fall through their `.stx` arms to `(txt, false, none)` and `return true`,
so the step carries **no `local` object and no `prop` flag**. Via `simp [*]` the same rewrite
records both correctly, which is how the gap hid.

The spec is unconditional on both: "when `name` is a local hypothesis rather than a global
constant, the step **also** carries `local`", and the `prop` flag is what tells a replayer to
rewrite with `eq_true name` instead of `name`. Without it a generator elaborates `h : p`,
finds neither an `Eq` nor an `Iff`, and fails — which is exactly REVIEW-3's M5, still open on
the commonest form. `simp [h]` is the dominant shape in Mathlib.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r5/Prop3.lean
```
Observed, same goal `p ∧ True` with `h : p`:
```
simp_trace [*]  ->  rw 'h' prop=true  local={'userName':'h','inaccessible':False,'ctxIndex':2}
simp_trace [h]  ->  rw 'h' prop=None  local=None
```
`/private/tmp/t1r5/Loc1.lean` shows the same split for an equational local (`h : a = b`): `[*]`
carries `local`, `[h]` does not. The `.stx` arm has the fvar in `c.lctx` — the display text is
the hypothesis's own name — so resolving it is a lookup, not a search.

## 2. CRITICAL — `classifyProof` accepts `propext` as the rewriting lemma; the call then fails

`ExplicitLean/SimpTrace/Recorder.lean:150-183` (`classifyProof`), exclusion list at :154-155.

`propext : ∀ {a b : Prop}, (a ↔ b) → a = b` has exactly one explicit argument and it is a
proof, so `classifyProof` classifies any `propext h`-headed simproc proof as `.lemmaApp
propext`. The recorder then emits `{"kind":"rw","name":"propext","source":"<simproc>"}` — a
step no replayer can execute, since `rw [propext]` is not a rewrite — and, because `h` is
neither an fvar nor `rfl`/`decide`/`nofun`, `assumptionName?` returns `none`, so the side
close becomes `unresolved:condition proof not a hypothesis or a recorded discharge` and the
**whole call is reported unresolved**. `propext` is plumbing exactly as `Eq.mpr`/`of_eq_true`
are, and belongs in the same exclusion list; with it excluded the firing falls back to `eq`,
where the scratch check decides `by`.

Stock `simp` proves the goal; `simp_trace` exits 1.
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r5/G04c.lean     # simp_trace: the error below, exit 1
sed 's/simp_trace/simp/' /private/tmp/t1r5/G04c.lean > /private/tmp/t1r5/G04cS.lean
lake env lean /private/tmp/t1r5/G04cS.lean    # stock: exit 0
```
Goal (Mathlib's `existsAndEq` simproc, reached with the ordinary `Finset`/`Function.Basic`
import set):
```
example (a : Nat) (p : Nat → Prop) : (∃ x, x = a ∧ p x) ↔ p a := by simp_trace
```
```
error: simp_trace unresolved: simproc:ExistsAndEq.existsAndEq side condition
`(∃ a_1, a_1 = a ∧ p a_1) ↔ a = a ∧ p a` proved by a term no close form describes
```
and the emitted step is `{"kind":"rw","name":"propext","source":"ExistsAndEq.existsAndEq", …}`.
This is systematic, not specific to `existsAndEq`: every simproc that returns a `propext`-wrapped
`Iff` proof hits it. Note the goal traces cleanly with a smaller import set — the defect is
invisible in the committed corpora because none of them pulls in an `Iff`-returning simproc.

## 3. MAJOR — the round-4 fix for minor 6 turned a good `eq` trace into an unresolved call

`ExplicitLean/SimpTrace/Tactic.lean:226-228`.

Omitting the `"simproc"` placeholder was right. Adding `ur.modify (·.add "simproc firing with
no recordable origin …")` alongside it was not: `source` is an optional provenance field, and
the step the recorder emits in this case is a complete, replayable `{"kind":"eq", …,
"by":"rfl"}`. Marking it unresolved makes `simp_trace` exit 1 on goals stock `simp` proves,
and reintroduces REVIEW-3's C1 ("an unattributable firing is never an abort") through the back
door. RESULT.md:46 nevertheless claims "no panics, no validation failures".

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r5/D18S.lean   # stock: exit 0
lake env lean /private/tmp/t1r5/D18.lean    # traced: exit 1
```
```
example (a : Nat) : (match (some a) with | some x => x | none => 0) + 0 = a := by simp_trace
```
```
error: simp_trace unresolved: simproc firing with no recordable origin
(match some a with | some x => x | none => 0 = a); `source` omitted
```
The trace itself is correct: `{"kind":"eq","pos":[0,1,0,1],"lhs":"match some a with …",
"rhs":"a","by":"rfl"}`. Nothing is unrepresentable. Drop the `markUnresolved`, keep the
omission.

## 4. MAJOR — the fork never enters `withInDSimp`, so `dreduceIte`/`dreduceDIte` can never fire

`ExplicitLean/SimpTrace/Traversal.lean:610-614` (`dsimpT`) against upstream
`Main.lean:517-529` (`dsimpImpl`).

Upstream's last line is `withInDSimpWithCache fun cache => transformWithCache …`
(`Types.lean:279`), which does two things: it swaps the `dsimpCache` (the documented,
accepted cache disablement) **and** it wraps the traversal in `withInDSimp`, setting
`Context.inDSimp := true`. `inDSimp` is not a cache flag; it is read by stock code:
`Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean:43` and `:68` are
```
builtin_dsimproc ↓ [simp, seval] dreduceIte (ite _ _ _) := fun e => do
  unless (← inDSimp) do
    -- If `simp` is not in `dsimp` mode, we should use `reduceIte`
    return .continue
```
`grep -n 'withInDSimp\|inDSimp' ExplicitLean/SimpTrace/Traversal.lean` returns **nothing**, so
in a traced run those two dsimprocs always take the `.continue` arm and the `dsimp`-mode `ite`
reduction upstream performs never happens. This is a fork infidelity outside the four
sanctioned categories (position threading, logging, the `simpT` re-entry substitution, the
documented cache disablement) and it is not mentioned in RESULT.md's "Deliberate departures".

I did not find a goal that exhibits the difference — see **Fidelity** for the four shapes
tried — so this is MAJOR on fidelity grounds rather than on an observed divergence. The fix
is one wrapper: `withInDSimp (visit pos e)`.

## 5. MAJOR — RESULT.md's measurement table and Round 6 claims do not match the tree

`tracking/tasks/T1-trace-capture/RESULT.md:43-46, 133, 145`.

Re-tallied from the traces the five modules actually wrote this round (see **Measurements**):

| file | RESULT.md says | measured |
| --- | --- | --- |
| `ExistsUniqueTraced` steps / bytes | 31 / 5 707 | **29 / 5 601** |
| `FunctionBasicTraced` steps / bytes | 108 / 21 556 | **101 / 20 553** |
| `FunctionBasicTraced` kinds | `proj` 3, `rw` 84 | **`proj` 5, `rw` 80** |
| checker fixture count (:145) | `OK: 40` | **`OK: 43`** |

RESULT.md:46's headline "**Every call stock simp proves traces: 46 of 46, and as of round 6
none is unresolved**" is false as written: `UnresolvedFixtures.lean` exists precisely because
one call is unresolved by design (the `zeta := false` / `simpHaveTelescope` shape, REVIEW-4
1(a)), and defects 2 and 3 above are two more shapes where a call stock `simp` proves is
reported unresolved. RESULT.md:136-139 additionally states the four `exists_prop_congr` /
`dite_congr` calls "return `none` through upstream's `unless modified` guard" — that claim is
**correct** (verified below), but it is offered as evidence for the headline, which it is not.

RESULT.md's "Known limitations" block (:150-153) still says "**User `@[congr]` transports are
recorded as one `change`** (6 of 46 calls)" and calls it "the largest remaining gap" — this
was superseded by the Round 6 work in the same file and is now simply wrong; no `change` step
appears in any measurement trace.

## 6. MINOR — a side trace has no `post`, so `close: null` leaves the replayer nothing to do

`ExplicitLean/SimpTrace/Types.lean:87-95` (`SideTrace`), spec's `rw` bullet.

A `LocationTrace` says how it ended two ways: `post` (the residual) and `close`. A `SideTrace`
has only `close`. When its steps do not reduce the side goal to `True` the recorder writes
`"close": null` and the replayer cannot tell whether the goal is closed, nor what remains.
Every user-congr trace in the tree does this: `FunctionBasicTraced_08`'s first side trace runs
`exists_apply_eq_apply` to `True` and stops at `close: null`; the `ite_congr` battery goals
end their side traces at `f a = f a` with `close: null`, needing an unrecorded `rfl`.

In practice T2 supplies the terminal tactic from its own `with [...]` entry, so this is
survivable, but it is under-determined data and the two sides can disagree. Either add `post`
to `SideTrace` (a spec bump) or always record a close form.

## 7. MINOR — `procDepth` is maintained in four places and read nowhere

`ExplicitLean/SimpTrace/Traversal.lean:173` and `Recorder.lean:296,304,313,375,383,388`.

`grep -n procDepth ExplicitLean/SimpTrace/*.lean` shows it incremented and decremented in
`instrument`, `instrumentD` and `withDivertedEvents`, and read in **no** expression — the
diversion decision in `TraceState.push:191` keys on `procEvents.size`, not on `procDepth`.
Dead state that documents an invariant the code does not enforce; note also that
`captureEvents` (:253-268) pushes a `procEvents` frame **without** bumping `procDepth`, so the
two are already out of step. Either delete the field or make `push` read it.

## 8. MINOR — `simp_trace?` does not parse

`ExplicitLean/SimpTrace/Tactic.lean:59-62`.

The 15-form substitutability battery this round asked for includes `simp?`. There is no
`simp_trace?` syntax, so `explicit_rw`'s "every `simp` argument form" claim in RESULT.md:2 is
slightly overstated. Arguably out of scope — `simp?` is a *suggestion* tactic, not a
simplification form — but it should be stated as an exclusion rather than left to be
discovered. `lake env lean /private/tmp/t1r5/diff/S1T.lean` → `error: unknown tactic`.

---

## Fidelity

**Frame machinery, second pass — no defect.** `grep -n '\[[^]]*\]!\|\.get!\|\.head!\|\.back!\|
\.getLast!\|\.set!' ExplicitLean/SimpTrace/*.lean` returns 12 sites; every one is guarded.
`Position.lean:75,100` are under `pos.size = 0` early returns. `Recorder.lean:164-165` are
bounded by `xs.size < args.size` at :161. `Recorder.lean:266` is under `xs.size == 1`.
`Recorder.lean:293` is under `procGoals.size > 0`. `Recorder.lean:338,402` are under
`news.isEmpty` / `unless news.isEmpty`. `Traversal.lean:715,720` index `args` at `i < args.size`.
`Traversal.lean:948` indexes `argResults[j]!` where `j` advances only on a `CongrArgKind.eq`
arm, one per pushed `argResult`. `Traversal.lean:1061` is `xs[i]!` under `c.hypothesesPos.any
(· ≥ xs.size)` returning `none` at :1043. **No `[i]!` on a possibly-empty structure remains.**
A zero-event trace (`/private/tmp/t1r5/Zero.lean`, three shapes: `-failIfUnchanged` on an
unchanged goal, an immediate assumption close, `singlePass` on `a = a`) produces
`"steps":[]` and exits 0 — no frame panic. Nested-frame stress
(`/private/tmp/t1r5/Frame2T.lean`: a `reduceIte` firing inside a `captureEvents` congr frame; a
discharger frame inside a congr frame; a user-congr hypothesis containing a simproc firing)
traces all three correctly with side sub-traces intact, and matches stock.

**`tryAutoCongrTheoremT?` (Traversal.lean:860-955) — faithful.** The `subst` loop now pushes
three entries on the `eq` arm (`arg`, `argResult.expr`, `argProof`) and the tail destructures
`type.instantiateRev subst |>.eq?`, matching upstream `Types.lean`. The `Function/Basic:390`
PANIC is gone. The added `eqArgEvents` capture and the `hasCast` branch are logging-only: the
`Result` the function returns is byte-identical in construction to upstream's.

**`dsimpT` (Traversal.lean:610-752) — one defect.** Line-by-line against `Transform.lean:98-165`
+ `Main.lean:517-529`: `pre`/`postStep` pipelines verbatim, `visitLambda`/`visitForall`/`visitLet`
collect the telescope and run `visitPost` at the telescope root with `usedLetOnly :=
cfg.zeta || cfg.zetaUnused`, `visitApp` honours `skipInstances := !cfg.instances` through
`getFunInfoNArgs`, `withIncRecDepth` and per-node `Core.checkSystem "transform"` are present.
REVIEW-4's three drops are all restored. The one remaining divergence is `withInDSimp` —
defect 4.

**`trySimpCongrTheoremT?` (Traversal.lean:1035-1092) — faithful.** Every guard is upstream's in
upstream's order: `hypothesesPos.any (· ≥ xs.size)`, the `isDefEq lhs e` gate, the per-hypothesis
`try`/`catch _ => return none`, `unless modified`, `synthesizeArgs`, the `isIff`/`propext` wrap,
`hasAssignableMVar`. The only additions are `origNumArgs` (position threading) and the
`ref.modify (·.push (.rw …))` under `unless eNew == e` (logging). `processCongrHypothesisT`
(:995-1029) reproduces upstream's `progress := r.proof?.isSome || (xs.size > 0 && lhs != r.expr)`
exactly, including the `#1113` comment's `xs.size > 0` test.

**The `unless modified` claim (task 3) — confirmed against upstream.** `Main.lean:614-616` is
`unless modified do trace[…]; return none`, and `modified` is set only from
`processCongrHypothesis`'s return. When every hypothesis is an implicit `rfl` the theorem
returns `none` and `congr` falls through to `congrDefault` — so there is genuinely no
congruence step to record. RESULT.md's claim about the other four calls is correct.

**Differential battery: 46 goals compiled side by side**, `simp` against `simp_trace`, in
`/private/tmp/t1r5/diff/{C1,S1,D1}{S,T}.lean` plus `/private/tmp/t1r5/{DS2,DS3,Frame2}{S,T}.lean`.
The REVIEW-4 set was re-run (`zeta := false`, `zetaDelta`, `+contextual`, `+decide`, `+arith`,
`singlePass`, `maxSteps`, `memoize := false`, `dsimp := false`, `implicitDefEqProofs := false`,
`ground`, `autoUnfold`, `unfoldPartialApp`, `iota/beta/proj := false`, `etaStruct`,
`instances := false`, `zetaUnused`, `letToHave`, matchers, `Nat` literals, dischargers,
`at h ⊢`, shadowed binders, inaccessibles, `mdata`) plus **10 new user-congruence goals**:
`ite` with contextual rewriting in both branches, `dite` with the hypothesis used in a branch,
`∃ x, p x ∧ q`, `∃ x, x = a ∧ p x`, `Exists` under two binders, `Subtype.val`, `Fin`
arithmetic, and three real Mathlib `@[congr]` lemmas found with the grep the task named —
`Finset.filter_congr` (`Mathlib/Data/Finset/Filter.lean:175`), `Finset.fold_congr`
(`Mathlib/Data/Finset/Fold.lean:71`) and `Function.update_congr`
(`Mathlib/Logic/Function/Basic.lean:654`).

**Result: 43 of 46 agree with stock. The 3 divergences are defects 2 and 3 and the known
`zeta := false` reclassification** — all three are `simp_trace` exiting 1 where stock exits 0,
with the goal state itself still correct in every case. **No goal-state divergence from stock
was found anywhere in this round.**

**Trace semantics of the new shapes (task 3) — verified by hand, no defect.**
`FunctionBasicTraced_08` (`dite_congr`): three side traces in hypothesis order h₁/h₂/h₃, the
first establishing `(∃ a_1, f a_1 = f a) = True` by `exists_apply_eq_apply`, the second and
third `intros: ["h"]` — which is exactly `dite_congr`'s `(h : c) → x (…) = u h` binder name at
`Init/SimpLemmas.lean:217-222` — and `close: rfl` on both unchanged branches.
`FunctionBasicTraced_13` (`ite_congr`): h₁ is `(a₂ = a₂) = True` by `eq_self`; h₂/h₃ carry
`intros: ["a✝"]`, correct because `ite_congr`'s `h₂ : c → x = u` (`SimpLemmas.lean:201-206`)
has an anonymous antecedent, and the display form is preserved rather than erased — the
REVIEW-2 hazard stays closed. The `Finset.filter_congr` / `fold_congr` goals record
`intros: ["x","a✝"]`, correct for `∀ x ∈ s, …` desugaring to `∀ x, x ∈ s → …`.
`congr_cast`: `arg: 3` on `cast.{u} α β h a` is the value argument, nested step at relative
`[]`. `congr_nested_cast`: the outer `congr` at `[0,1]` carries an inner `congr` at relative
`[]` with `arg: 3`, whose own step is at `[]` — the recursion is right. All four side-trace
orderings and all nested positions check out.

---

## Measurements

macOS, Lean 4.32.2, `/usr/bin/time -l`, shared `.lake/packages`, serial.

| file | calls | steps | kinds | bytes | wall | peak RSS | exit |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `IsEmptyBasicTraced.lean` | 17 | 76 | `rw` 70, `unfold` 6 | 15 045 | 2.71 s | 677 MB | 0 |
| `NontrivialDefsTraced.lean` | 1 | 6 | `rw` 6 | 1 109 | 2.62 s | 668 MB | 0 |
| `FunctionDefsTraced.lean` | 1 | 12 | `rw` 8, `proj` 4 | 1 878 | 2.71 s | 677 MB | 0 |
| `ExistsUniqueTraced.lean` | 8 | 29 | `rw` 23, `beta` 4, `unfold` 2 | 5 601 | 2.62 s | 683 MB | 0 |
| `FunctionBasicTraced.lean` | 19 | 101 | `rw` 80, `intro_ctx` 8, `beta` 7, `proj` 5, `unfold` 4, `congr` 2 | 20 553 | 3.05 s | 743 MB | 0 |

Kind counts include steps nested inside `congr` and inside `side` sub-traces. The
`IsEmpty`/`Nontrivial`/`FunctionDefs` tallies reproduce RESULT.md exactly; the other two do
not — defect 5.

**Overhead on a real module.** The same `FunctionBasicTraced.lean` with every `simp_trace …
=>trace "…"` rewritten back to `simp …` (`/private/tmp/t1r5/FBStock.lean`, 0 `simp_trace`
tokens remaining): stock 3.01 s / 735 MB against traced 3.05 s / 743 MB — **1.01x wall, 1.01x
RSS**. The disabled result cache costs nothing measurable at real-module scale, confirming
round 4's finding now that no call aborts early.

**Standard checks.** Scratch build with `.lake/build/lib/lean/ExplicitLean/SimpTrace{,.olean,
.ilean,.trace}` deleted: `lake build ExplicitLean.SimpTrace` **clean, no warnings**, exit 0,
10.20 s, 744 MB. `test/SimpTrace/Fixtures.lean`: **exit 0**, 3.44 s, 1 514 MB.
`test/SimpTrace/UnresolvedFixtures.lean`: **exit 1 by design**, one classified line —
`` simp_trace unresolved: `have` telescope simplified as a unit … recorded as one `change` ``.
`python3 -B Experiment/check_simp_trace.py`: `OK: 43 simp_trace fixture(s) match their expected
skeletons, and out-of-root paths (including through symlinks) are refused`, 15.5 s, exit 0.

**Scope.** `git diff --name-only $(git merge-base codex/search-free-mathlib-2026-08-31
task/T1-trace-capture) task/T1-trace-capture` lists 66 files. All fall under
`ExplicitLean/SimpTrace/`, `test/SimpTrace/`, `Experiment/check_simp_trace.py` and
`tracking/tasks/T1-trace-capture/`, plus the new module root `ExplicitLean/SimpTrace.lean`
(12 lines of `public meta import`) — owned, and not `ExplicitLean.lean` or `lakefile.toml`.
No tracked scratch; `out/`, `isempty_out/`, `meas_out/` are gitignored and untracked.

---

## Integration

Four traces hand-translated into the T2 syntax documented at
`/Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw/ExplicitLean/ExplicitRw/Tactic.lean`
and replayed in the T2 worktree (`/private/tmp/t1r5/T2replay.lean`, **exit 0** on the three
that have a T2 form).

**(A) Two ordinary traces replay verbatim at T1's recorded positions.**
`NontrivialDefsTraced_01`'s six steps become
`explicit_rw [nontrivial_iff at [0, 1, 1], not_exists at [0, 1], not_exists at [0, 1, 1],
Classical.not_not at [0, 1, 1, 1], subsingleton_iff at [1], iff_self at []] then exact
True.intro`, and `FunctionDefsTraced_01`'s twelve (including four bare `proj at [...]` steps)
likewise. Every position is copied unchanged from the JSON. This is the strongest evidence
this round that T1's positions are correct: T2 navigates by raw child index with no search,
so a wrong index fails loudly.

**(B) The user-congr trace replays, and T2 already has the recursive side-proof form.**
The task's premise that "T2 does not yet have a recursive side-proof form for
implication-shaped side traces" is **out of date** — `ExplicitRw/Tactic.lean:339-340` declares
`explicitRwSideIntro` (`intro <ident>+ ; <sideProof>`) and `:411-412` declares
`explicitRwSideNested` (a whole `explicit_rw [...] then <closer>` as a side proof), both
dispatched at `:1199-1213`. `FunctionBasicTraced_13`'s `ite_congr` step renders as
```
explicit_rw [ite_congr at [0, 1]
               with [explicit_rw [eq_self at []] then exact True.intro,
                     intro h ; rfl,
                     intro h ; rfl],
             ite_cond_eq_true c c' (eq_self a₂) at [0, 1]] then rfl
```
and is accepted. The `side` array maps one-to-one onto `with [...]` in order; each side trace
with a non-empty `intros` becomes `intro <names> ; <proof>`; a side trace with its own `steps`
becomes a nested `explicit_rw`. **No syntax gap here — the T2 form the task asked me to
specify already exists in that shape.** The one caveat is defect 6: a side trace with
`close: null` gives T2 nothing to put after the nested `explicit_rw`, and I had to supply
`then rfl` / `then exact True.intro` by inspection.

**(C) One mismatch — the `congr` kind has no T2 form at all. Responsible side: T2.**
`congr_cast`'s trace is
`{"kind":"congr","pos":[0,1],"arg":3,"steps":[{"kind":"rw","pos":[],"name":"hfa",…}]}`. T2's
`explicitRwStep` (`Tactic.lean:402-404`) is
`explicitRwUnfold <|> explicitRwRed <|> explicitRwIntroCtx <|> explicitRwChange <|>
explicitRwEq <|> explicitRwRw`; `grep -n congr ExplicitLean/ExplicitRw/Tactic.lean` finds the
kind only in a prose comment at `:316`. Any spelling is a parse error:
```
error: unexpected token '['; expected 'at'
```
on `congr 3 [hfa at []] at [0, 1]`. **The syntax T2 needs** is one step form carrying the
argument index and a nested step list, whose elaboration obtains `Lean.Meta.mkCongrSimp?` for
the head, proves the argument equation from the nested steps and applies the theorem — the
spec's own prescription. Concretely:
```
syntax explicitRwCongr :=
  &"congr " num " [" explicitRwStep,* "]" explicitRwPos
```
rendering T1's step as `congr 3 [hfa at []] at [0, 1]`, with the nested list recursing through
`runSteps` at positions relative to the argument (so a nested `congr` nests again, as
`congr_nested_cast` requires). Two of the nineteen `FunctionBasicTraced` calls and two
committed fixtures are unreplayable until this lands; it is the only T1 kind T2 cannot
express.

**(D) One T2-side bug found in passing, not T1's.** REVIEW-4's `add_zero` instance-stuckness
did not reproduce on the traces I replayed (the monomorphic `Nat.add_zero` and the
`Prod`/`Function` lemmas all elaborate), so I could not confirm or clear it. Separately, T2's
`.olean` was stale in the worktree and `lake build ExplicitLean.ExplicitRw.Tactic` was needed
before any replay; T2's own `test/ExplicitRw/{Basic,Definitional,Lemmas,Binders}.lean` then
compile with zero errors.

---

**Totals: 2 critical, 3 major, 3 minor; 1 T2-side gap (the `congr` step form).** Defects 2 and
3 share a shape — a complete, replayable trace paired with a `markUnresolved` that should not
be there — and both make `simp_trace` fail on goals stock `simp` proves, which is the property
RESULT.md's headline asserts.
