# T1-trace-capture: adversarial review, round 4 (T1b forked traversal)

Scope check passed: `git diff --stat $(git merge-base codex/search-free-mathlib-2026-08-31
task/T1-trace-capture) task/T1-trace-capture` lists 53 files, all under
`ExplicitLean/SimpTrace/`, `test/SimpTrace/`, `Experiment/check_simp_trace.py`,
`tracking/tasks/T1-trace-capture/`. Working tree clean; `scratch/`, `out/`, `isempty_out/`,
`meas_out/` gitignored and untracked. Scratch for this round is `/private/tmp/t1r4/`, not
committed.

**All seven REVIEW-3 items reproduce as fixed.** C1: `FINAL`-shape unattributed firings now
emit `eq`/`by:"rfl"` (`Nat.reduceAdd`), and `Option.getD`/matcher goals trace as
`unfold`+`iota`. **C2 is genuinely fixed and flat**: chain depths 4/6/8/12/30 measured
traced 3.44/3.41/**3.43**/**3.39**/3.50 s against stock 3.40/3.42/3.58/3.59/3.52 s — no
depth dependence, no timeout; the projection-under-binder shape traces in 3.4 s. M3:
`(disch := omega)` records `close:{"by":"omega"}`. M4(a)/(b): both trace. M5: `prop:"true"`
carried on `exists_eq'`. M6: no `#N` in any emitted trace. M7: RESULT.md rewritten.
`classifyProof` resisted all three fooling attempts (below). Four measurement files and both
committed corpora reproduce **exactly** (IsEmpty 17/76/15 045 B; meas 10/47/8 588 B).

The defects below are new, and all but #6 were found by going outside the committed corpus.

---

## 1. CRITICAL — `zeta := false` hard-errors on goals stock `simp` proves (two shapes)

`ExplicitLean/SimpTrace/Traversal.lean:1091-1105` (`simpLetT`) with
`ExplicitLean/SimpTrace/Tactic.lean:364-395` (`validate`).

With `zeta := false` the traversal descends into a `let` via `dsimpT`, which instantiates the
let-binder as an fvar and pushes it on the binder stack — but the event is logged at the
*enclosing* position, so the validator navigates to a position that is not under the binder,
`abstractSimpFVars` abstracts nothing, and the raw fvar surfaces. This is REVIEW-3 M4(b)'s
`_fvar` leak, which RESULT.md:67 calls "structurally impossible now".

(a) rewrite inside the let body (`/private/tmp/t1r4/ZetaT2.lean`):
```
example (f : Nat → Nat) (a : Nat) : (let x := a; f (x + 0)) = (let x := a; f x) := by
  simp_trace (config := { zeta := false })
```
Observed: `error: simp_trace: validation failed: subterm at [] is (let x := a; f (x + 0)) = ...`
/ `but the recorded step's before is _fvar.120 + 0`. Note `pos` is `[]` while `before` is a
subterm several levels down — the position itself is wrong, not merely the abstraction.
Expected: stock's goal state (exit 0). Repro:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r4/ZetaS2.lean   # stock: exit 0, no output
lake env lean /private/tmp/t1r4/ZetaT2.lean   # traced: the abort above
```

(b) `letToHave` rewrites the term before the event is recorded, so `before` is a `have` while
the running term is still a `let` (`/private/tmp/t1r4/Z3S.lean` vs `Diff3.lean:62`):
```
example (a : Nat) : (let x := a; x) + 0 = (let x := a; x) := by
  simp_trace (config := { zeta := false })
```
Observed: `validation failed: subterm at [0, 1] is (let x := a; x) + 0` / `but the recorded
step's before is (have x := a; x) + 0`. Stock exits 0. The `letToHave` rewrite at
`Traversal.lean:1097-1102` changes the term the validator replays against; the fork must
either log that rewrite as a step or validate against the post-`letToHave` term.

## 2. CRITICAL — the fork passes an open term into stock simp: PANIC "loose bvar" on real Mathlib

`ExplicitLean/SimpTrace/Traversal.lean:481-554` (`dsimpT`/`visitChildren`).

Compiling a traced copy of `Mathlib/Logic/Function/Basic.lean` panics inside Lean's own
matcher:
```
PANIC at Lean.Meta.whnfEasyCases Lean.Meta.WHNF:391:22: loose bvar in expression
```
The backtrace is `Simp.postDefault` → `Simp.rewritePost` → `rewrite?.rewriteUsingIndex?` →
`DiscrTree.getMatchWithExtra` → `DiscrTree.reduce` → `whnfEasyCases`: stock `post` was handed
a term with a **loose de Bruijn variable**, which is exactly the invariant the copied code is
supposed to preserve. RESULT.md does not mention a panic, and REVIEW-3's task-2(d) probe
concluded the guard was "not triggerable".

Site: `Mathlib/Logic/Function/Basic.lean:390` (`not_surjective_Type`),
`simp only [g, cast_cast, cast_eq] at this` where `g` is a `let`-bound local — i.e. the same
zeta-delta path as defect 1. Self-contained repro (identical file, one token changed):
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r4/PanicT3.lean   # simp_trace: PANIC, as above
sed -i '' 's/simp_trace only/simp only/' /private/tmp/t1r4/PanicT3.lean
lake env lean /private/tmp/t1r4/PanicT3.lean   # stock simp: clean, no PANIC
```
A panic is not a classified `unresolved:`; it is an abort inside the kernel-facing matcher and
it must not survive a merge.

A second, milder instance of an open/ill-formed term reaching a stock method is the
`simp only [g]` case in `/private/tmp/t1r4/PanicT.lean`, where the error prints `before` and
the subterm **identically** (`(fun s => s + 0) a` both sides) yet `==` fails — an `Expr`-level
difference (mdata or instance) the message cannot show.

## 3. MAJOR — 6 of 20 real Mathlib calls fail; `dsimp` fork drops `skipInstances`, `usedLetOnly`, `checkSystem`

Fork-fidelity defects in `dsimpT` (`Traversal.lean:481-554`) against upstream
`Main.lean:517-529` + `Lean/Meta/Transform.lean:98-165`. Upstream `dsimpImpl` calls
`transformWithCache` with three things the fork's hand-written traversal does not reproduce:

- **`skipInstances := !cfg.instances`** (`Transform.lean:138-150`) — upstream skips instance
  arguments, resolved via `getFunInfoNArgs`. The fork visits *every* argument
  (`Traversal.lean:529`). `simpProjT`/`congrArgs` honour `cfg.instances`
  (`Traversal.lean:660,695`) but the dsimp path does not, so `dsimp` can rewrite inside an
  instance where stock does not.
- **`usedLetOnly := cfg.zeta || cfg.zetaUnused`** (`Transform.lean:122-134`) — governs whether
  `mkLambdaFVars`/`mkLetFVars` drop unused binders. The fork uses `Expr.abstract`
  (`Traversal.lean:537,544,551`) unconditionally, which never drops them.
- **`Core.checkSystem "transform"`** (`Transform.lean:112`) — per-node interrupt/deadline
  check. The fork has `checkSystem` only in `simpLoopT` and `congrArgs`
  (`Traversal.lean:688,1146`), so a long `dsimp` traversal is uninterruptible.

Empirically, a traced copy of `Mathlib/Logic/Function/Basic.lean` (20 executable calls
rewritten to `simp_trace ... =>trace`; original compiles clean under stock) gives **16 traced,
4 hard failures plus 4 classified unresolved**, versus RESULT.md's headline "every call stock
simp proves traces (10/10)":

| outcome | count | sites |
| --- | --- | --- |
| traced | 16 | 87 steps, `rw` 67 / `intro_ctx` 8 / `beta` 5 / `unfold` 4 / `proj` 3, 16 881 B |
| PANIC | 1 | `:390` (defect 2) |
| validation failed | 3 sites (6 errors) | `:848`, `:929`, `:976` (x4) |
| unresolved (classified) | 4 | `:191`, `:317`, `:529`, `:924` — `exists_prop_congr`/`ite_congr`/`dite_congr` |

`:848` and `:929` are a **proof-irrelevance mismatch**: `before` prints
`if h : True then g (Classical.choose ⋯) else e' (f a)` while the subterm has
`Classical.choose h` — structurally different proof terms that are propositionally equal, and
`validate`'s `sub == expected` (`Tactic.lean:386`) rejects them. `:976` records
`before` = `(a, a').fst` at a position whose subterm is the whole
`update (curry f (a, a').fst) (a, a').snd b` — a genuinely wrong position.
Repro:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r4/meas/out lake env lean /private/tmp/t1r4/meas/FunctionBasic.lean
```

## 4. MAJOR — `Fixtures.lean` exits 1; RESULT.md reports it as "pass"

`ExplicitLean/SimpTrace/Tactic.lean:563` (`logError`), reached from the deliberate
`ctor_eq_inductive` fixture (`test/SimpTrace/Fixtures.lean:178-179`).

RESULT.md:108 states "`Fixtures.lean` (33): pass, 4.93 s". Measured: **exit code 1**, 3.47 s,
1 511 MB, with
```
test/SimpTrace/Fixtures.lean:179:2: error: simp_trace unresolved: simproc:reduceCtorEq side
condition `FixtureColor.red = FixtureColor.green → False` proved by a term no close form describes
```
`logError` makes the *file* fail to compile, so the fixture suite is not a green check and
cannot be used as a merge gate as written. Either the fixture must be moved behind an
expected-error mechanism, or RESULT.md must state the file exits 1. Repro:
`lake env lean test/SimpTrace/Fixtures.lean; echo $?`.

Note this is the same fixture defect #5 fixes: once `nofun` lands, the file goes green.

## 5. MAJOR — `nofun` close form is unimplemented; the spec amendment is not in this branch

`ExplicitLean/SimpTrace/Recorder.lean:232-247` (`assumptionName?`).

`grep -c nofun ExplicitLean/SimpTrace/*.lean Experiment/check_simp_trace.py` = **0**. The
branch's merge-base is `6eaed50`, so `tracking/SIMP-TRACE-SPEC.md` here predates both
`408a39b` and `fd4419b`; the `nofun` close form the task names is absent from the worktree's
spec copy, and the checker's close enumeration (`check_simp_trace.py:42-43`,
`CLOSE_EXACT = {"rfl","true_intro","decide","omega"}`) does not list it. `reduceCtorEq` is
therefore still classified `unresolved:`, as RESULT.md:94-98 and the task expected — **confirmed**.

**What implementing `nofun` requires** (verified, small): the side proof `eq_false'` is applied
to is a function `FC.red = FC.green → False`. Add one arm to `assumptionName?` returning
`some "nofun"` when the argument's type is an arrow into `False` whose domain is an equation
between distinct constructors (or, more simply, when the proof term is a `fun` whose body is a
`noConfusion`/`nomatch` elimination); add `"nofun"` to `CLOSE_EXACT` in the checker; drop the
`markUnresolved` for that case in `emitProcStep` (`Recorder.lean:210-221`). Replay is
`exact eq_false' nofun`, which type-checks today (`/private/tmp/t1r4/Nofun2.lean`, exit 0), and
T2 already accepts `nofun` in both `explicitRwSideTac` and `explicitRwCloser`
(`T2 .../ExplicitRw/Tactic.lean:320,370,739,1046`).

## 6. MINOR — `source` is the literal string `"simproc"` when the firing has no origin

`ExplicitLean/SimpTrace/Tactic.lean:222-223`:
```
let src := (src?.map toString).getD (if proofTac == "decide" then "decide" else "simproc")
```
The spec's `eq` bullet says `"source": "<simproc name>"`. When `src?` is `none` the trace
carries `"source":"simproc"` (or `"decide"`) — a placeholder that names no simproc, so
provenance is silently lost rather than classified. Observed in
`/private/tmp/t1r4/R3.lean`: `{"kind":"eq","lhs":"2 + 1","rhs":"3","by":"rfl","source":"simproc"}`
in the same trace where the adjacent step correctly carries `"source":"Nat.reduceAdd"`.
Either omit `source` or record a classified unresolved. Related inconsistency:
`test/SimpTrace/out/decide.json` carries no `source` at all while `ctor_eq.json` does, though
both are simproc-derived.

## 7. MINOR — `reduceT` is a fixpoint where upstream `simpLoop` takes one `reduceStep`

`ExplicitLean/SimpTrace/Traversal.lean:1156` versus upstream `Main.lean:694`. Upstream
`visitPreContinue` calls `reduceStep` (**one** step) and re-enters `simpLoop`; the fork calls
`reduceT`, which loops to a fixpoint before re-entering. `numSteps` (the `maxSteps` budget) is
therefore incremented once per *chain* instead of once per reduction, so a `maxSteps` cutoff
falls in a different place than stock. No divergence observed on the corpus — `maxSteps := 1000`
and the depth-30 chain both match stock — so this is minor, but it is an undocumented
semantic edit outside the four sanctioned categories.

---

## Fork fidelity

Line-by-line diff of all 41 `SOURCE:`-annotated functions against
`~/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Meta/Tactic/Simp/{Main,Types}.lean`.

**Faithful.** The copied helpers (`isOfNatNatLit'`, `isOfScientificLit'`, `isCharLit'`,
`unfoldDefinitionAny?'`, `reduceProjFn?'`, `reduceFVar'`, `isMatchDef'`, `unfold?'`,
`doNotVisitProofs'`, `doNotVisit'`) are **verbatim**, including the
`backward.whnf.reducibleClassField` branch and the `unfoldPartialApp`/`smartUnfolding` logic.
`reduceStepC` preserves every branch and every config gate of `reduceStep`
(`beta`/`proj`/`iota`/`zeta`/`zetaHave`/`zetaUnused`/`unfold?`/`foldRawNatLit`), adding only
the kind tag; the `-- TODO: eta` gap is reproduced deliberately, so `eta` is correctly never
emitted. `withIncRecDepth` is present in `reduceT`, `simpLoopT`, `simpT` and `dsimpT.visit`.
`checkSystem "simp"` is present in `simpLoopT` (matching `Main.lean:686`). `maxSteps`,
`singlePass`, `instances`, `ground`, `zetaDelta`, `unfoldPartialApp`, `autoUnfold`,
`implicitDefEqProofs` and the congruence path (`congrArgs`, `simpAppUsingCongr`,
`tryAutoCongrTheorem?`, `trySimpCongrTheorem?`, `processCongrHypothesis`, `withNewLemmas`,
`simpMatch` via `reduceRecMatcher?`) all match. `Result` composition is stock throughout —
every `mkEqTrans` is Lean's own.

**Differences beyond the four sanctioned categories** (position threading, logging, the
`simpT` re-entry substitution, documented cache disablement):

1. `dsimpT` drops `skipInstances` — defect 3.
2. `dsimpT` drops `usedLetOnly` — defect 3.
3. `dsimpT` drops the per-node `Core.checkSystem "transform"` — defect 3.
4. `simpLoopT` substitutes `reduceT` (fixpoint) for `reduceStep` (one step) — defect 7.
5. `dsimpT` replaces `transformWithCache`'s `checkCache` memo with no memo. Documented as the
   cache disablement; measured cost is acceptable (see **Performance**).
6. `classifyDefChange` (`Traversal.lean:451-457`) is **new code with no upstream counterpart**:
   it guesses a spec kind from the shape of a `dpre`/`dpost` result. It is logging-only and
   cannot change what simp does, so it is within the logging category, but it is a heuristic
   (`before.isLet ⇒ zeta`, `getAppFn` changed ⇒ `unfold`) that can mislabel a step's `kind`.

**Empirical differential: 33 adversarial goals compiled side by side** with `simp` and
`simp_trace`, each pair asserting the same post-state via `guard_target`/`guard_hyp` or an
explicit follow-on tactic (`/private/tmp/t1r4/Diff{1,2,3}.lean`, `R3.lean`, `Pos5.lean`).
Covered: `zeta := false`, `zetaDelta := true`, `+contextual` (incl. nested), `+decide`,
`+arith`, `singlePass := true`, `maxSteps`, `memoize := false`, `dsimp := false`,
`implicitDefEqProofs := false`, `ground := true`, `autoUnfold`/`@[reducible]`,
`unfoldPartialApp := true`, `iota := false`, `beta := false`, `proj := false`, `etaStruct`,
`instances := false`, `zetaUnused`, `letToHave`/`have`, matchers on constructors, `Nat`
literal arithmetic, `decide := true` on a `Decidable` prop, `(disch := assumption)`,
`(disch := omega)`, `simp at h₁ h₂ ⊢`, nested shadowed binders, inaccessible names, `mdata`.

**Result: 31 of 33 agree with stock. The 2 divergences are both `zeta := false` — defect 1.**
Every other config flag, including the ones most likely to expose a fork drift
(`singlePass`, `maxSteps`, `memoize := false`, `iota/beta/proj := false`, `instances := false`),
produced identical goal states.

**Positions and `local` refs (task 5) — no defect.** Nested shadowed binders emit
`beta [0,1,1]` then `add_zero [0,1,1,1]` at the inner binder. Two inaccessibles record
`a✝¹`/`a✝` with distinct `ctxIndex` 4/5 and full hygienic `userName`s. `ctxIndex` after
binder crossings is `LocalDecl.index`, stable within the call. `letE` positions are correct
under default `zeta` (`zeta [0,1]` then `add_zero [0,1,1]`); only `zeta := false` breaks
(defect 1). `mdata` is traversed transparently.

**`classifyProof` (task 4) — resisted every fooling attempt** (`/private/tmp/t1r4/Fool.lean`).
(i) A custom simproc returning `bogus n 999`, where `999` is an explicit argument shaped like a
subterm but absent from the position, was **correctly rejected** — `isSubtermOf`
(`Recorder.lean:143`) uses structural `==` over `Expr.find?`, so it fell back to
`eq`/`by:"rfl"` rather than emitting an unreplayable `rw`. (ii) A lemma with an
instance-implicit argument in non-standard order (`weird_eq (n) [Tag Nat] (m)`) is handled:
the walk is over the lemma's own `forallTelescopeReducing` telescope, so `binderInfo` is read
per position, not assumed. (iii) `Eq.symm`-headed proofs are excluded by name at
`Recorder.lean:152-154` together with `Eq.trans`/`Eq.mpr`/`id`/`of_eq_true`, so the direction
hazard cannot arise.

**Simproc replay verified in plain Lean, no `explicit_rw`** (`/private/tmp/t1r4/Replay.lean`,
exit 0): `rw [ite_cond_eq_true 1 2 (eq_true (by rw [h]))]`,
`rw [dite_cond_eq_true (eq_true (by rw [h]))]`,
`rw [eq_true_of_decide (rfl : decide ((2:Nat)+2=4) = true)]`,
`rw [eq_false_of_decide (rfl : decide ((1:Nat)=2) = false)]`. All four `side` sub-traces are
rooted at the side goal (`"goal":"n = 3"`, `"goal":"true = true"`), matching the spec.

---

## Performance

**Cache disablement is not a performance defect.** All figures `/usr/bin/time -l`, macOS,
Lean 4.32.2, warm `.lake`.

| workload | stock | traced | ratio | peak RSS (stock → traced) |
| --- | --- | --- | --- | --- |
| `Mathlib/Logic/Function/Basic.lean` (1 245 lines, 20 calls) | 4.26 s | 3.50 s | **0.82x** | 669 → 752 MB |
| pathological: 200 identical `f (g x)`, rewrite on `g x` | 3.63 s | 7.22 s | **1.99x** | 1 503 → 1 512 MB |
| chain depth 4 / 6 / 8 / 12 / 30 | 3.40 / 3.42 / 3.58 / 3.59 / 3.52 s | 3.44 / 3.41 / 3.43 / 3.39 / 3.50 s | ~1.0x | — |
| `IsEmptyBasicTraced.lean` (17 calls) | — | 2.80 s | — | 645 MB |

The real-module ratio is **below 1x** only because four calls abort early (defect 3); the
honest reading is that the cache costs nothing measurable at this size. The pathological case
— the one the cache exists for — costs **1.99x**, under the 3x major threshold and far under
10x. RSS is essentially unchanged (+0.6% on the pathological case). Nothing approached the
30-minute / 30 GB caps, so `Mathlib/Logic/Basic.lean` was not additionally needed to settle
the question.

One caveat the numbers do expose: at 200 identical subterms with default `maxSteps`,
`simp_trace` reports `` `simp` failed: maximum number of steps exceeded `` where stock
succeeds (`/private/tmp/t1r4/CacheT.lean` vs `CacheS.lean`). Raising `maxSteps` to 4 000 000
makes both succeed, which is how the 1.99x above was measured. This is defect 7's step
accounting plus the absent result cache; it is a budget difference, not a blow-up.

**Measurement files, all four re-run.** `IsEmptyBasicTraced` exit 0, 2.80 s, 645 MB, 17/17,
0 unresolved. `NontrivialDefsTraced` exit 0, 2.69 s, 637 MB. `FunctionDefsTraced` exit 0,
2.84 s, 645 MB. `ExistsUniqueTraced` **exit 1**, 2.76 s, 649 MB, 1 unresolved
(`exists_prop_congr`, as RESULT.md:51-53 discloses). Committed tallies reproduce exactly:
IsEmpty 17 traces / 76 steps / `rw` 70 + `unfold` 6 / 15 045 B; meas 10 / 47 /
`rw` 37 + `beta` 4 + `proj` 4 + `unfold` 2 / 8 588 B.

**Standard checks.** Scratch build with SimpTrace oleans deleted: **clean, no warnings**,
20.15 s, 735 MB. `python3 -B Experiment/check_simp_trace.py`: `OK: 33 simp_trace fixture(s)
match their expected skeletons, and out-of-root paths (including through symlinks) are
refused`, 6.6 s. `test/SimpTrace/Fixtures.lean`: **exit 1** — defect 4.

---

## Integration

Three traces hand-translated to the T2 syntax at
`/Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw/ExplicitLean/ExplicitRw/Tactic.lean`
and replayed there (`/private/tmp/t1r4/T2b.lean`, exit 0). One covers `iota`, one the `prop`
flag, one a simproc `rw` with a `side` clause — the three kinds the task names.

**(A) `iota` — replays exactly.** T1 trace `unfold G3.mt at [0,1,0,1]`, `iota at [0,1,0,1]`,
`add_zero at [0,1]`, `eq_self at []`, `close true_intro` →
`explicit_rw [unfold mt at [0, 1, 0, 1], iota at [0, 1, 0, 1], Nat.add_zero at [0, 1],
eq_self at []] then exact True.intro`. Positions, the `unfold`→`iota` order and the closer are
all accepted verbatim.

**(B) `prop` flag — replays exactly, and T2's rendering is the spec's.** T1 records
`{"kind":"rw","name":"exists_eq'","prop":"true"}`; the spec says replay rewrites with
`eq_true name`. Written as `eq_true exists_eq' at [0, 1]` it is accepted. REVIEW-3's M5 is
closed on both sides: T1 now emits the flag, T2 consumes the rendering.

**(C) simproc `rw` + `side` — replays exactly.**
`ite_cond_eq_true 1 2 at [0, 1] with [exact eq_true h]`, then `eq_self at []`,
`then exact True.intro`. The `with [...]` clause maps one-to-one onto the `side` sub-trace's
`close`, and the explicit `1 2` come straight from the recorded lemma arguments.

**One mismatch, responsible side T2.** The general Mathlib `add_zero` is rejected:
```
explicit_rw: step 1: typeclass instance problem is stuck
  AddZeroClass ?m.13
```
on `example : (7:Nat) + 0 = 7`, while plain `rw [add_zero]` on the identical goal succeeds
(`/private/tmp/t1r4/T2c.lean`). T2 elaborates the lemma term *before* unifying it with the
subterm at the position, so a class-polymorphic lemma has nothing to fix its instance
argument; `rw` postpones and succeeds. Substituting the monomorphic `Nat.add_zero` replays
fine. **This is a T2-side defect, not T1's** — but it is not narrow: `add_zero` accounts for
many steps across T1's corpora (it is the first step of the `top_level_rfl`, `under_forall`,
`under_lambda` and `shadowed` fixtures), so T2 must resolve instances against the position
before a T1 trace of ordinary Mathlib can replay. No other T1/T2 disagreement was found;
`intro_ctx` remains recognised-but-unimplemented in T2 by design.

---

**Totals: 2 critical, 3 major, 2 minor; 1 T2-side defect.** Defects 1 and 2 share a root
cause (the `let`/zeta-delta path through `dsimpT`), and defect 4 is cleared by defect 5's fix.
