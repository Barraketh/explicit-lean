# T1-trace-capture: adversarial review, round 9

Scratch for this round is `/private/tmp/t1r9/`, not committed. Working tree clean before and
after; `git status --porcelain` empty. All Lean compiles run serially. T2 replays were run in
`/Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw` at tip **`1d8b125`** ("T2:
RESULT.md at the 115-line budget"), ahead of the `69aa441` REVIEW-8 used; T2's tree carries three
untracked files (`tmp18jm3ec0.lean`, `tmpll_o0nbl.lean`, `tracking/tasks/T2-explicit-rw/REVIEW-8.md`).

**All eight REVIEW-8 items reproduce as fixed.** 1: `goalCloseForm?` (`Recorder.lean:603-622`)
exists and the `True`/`¬False` side goals now close (`true_intro`, `nofun`). 2: the `prop: false`
arm unfolds with `whnfR` (`Tactic.lean:471-480`); all three `Ne` shapes in `NeFreq.lean` now
trace clean, and `Ne`-stated *locals* carry `local` and `prop: false` in both goal and `at h`
position (`/private/tmp/t1r9/NeRev.lean`; `← Ne` is refused by **stock** Lean, not by T1). 3:
side steps are rebased (`Recorder.lean:478-483`) and `check_side_positions` was added; corpus-wide
only two side traces keep a non-empty step position and both are correct (`¬P` at `[1]` = `Not`'s
argument). 4: all 32 `args` entries are parenthesised when compound, none contains `⋯`, and
`surjInv ⋯` is now `(surjInv hf.right)`. 5: `check_transcription.py` passes and genuinely fails
when a site is broken back to stock (`/private/tmp/t1r9/ct_broken.py`, exit 1, both assertions
fire). 6: `UnresolvedFixtures.lean` emits **4** classified lines, which is now what RESULT.md:184
says. 7/8: skeletons carry `pre`/`post`, and an unreadable statement classifies as
`unreadable_rw_statement:<name>` rather than passing — observable on `Logic/Basic:974`.

**The measurement side is sound and the fidelity is perfect.** `--report` reproduces RESULT.md:45-53
byte-identically after deleting `meas_out/` and re-running all six modules. Ten fresh real-Mathlib
calls diverge from stock nowhere.

**But the merge gate does not hold. Of 78 mechanically translated traces, 48 replay in T2 and 30
do not, and every failure is T1's.** The dominant cause is a new instance of exactly the frame
error round 8 fixed for positions, now in `pre`/`post`/`close`: a side trace built on the diverted
path records the *subterm the simproc simplified* as its goal and hardcodes `true_intro` as its
close, where the lemma's real side condition is an **equation** about that subterm. The recorder
has the correct code for this two hundred lines earlier and uses it on the non-diverted path, so
the same trace can carry one right side goal and one wrong one.

---

## 1. CRITICAL — a diverted side trace records the wrong goal and a hardcoded `true_intro` close; 16 side traces, 30 replay failures

`ExplicitLean/SimpTrace/Recorder.lean:478-483`.

```lean
let divertedSide : Array SideRec :=
  if diverted.isEmpty then #[]
  else
    let rebased := diverted.map (Event.strip pos)
    #[SideRec.mk (divertedGoal?.getD e) rebased (some "true_intro") evCtx #[]
      (divertedGoal?.getD e) none]
```

`divertedGoal?` is the subterm the simproc chose to simplify (`Recorder.lean:439-441`), and the
close is the literal string `"true_intro"`, written unconditionally. Neither is read off the
lemma. For `ite_cond_eq_false`/`dite_cond_eq_false` the side condition is `c = False`, and for
`ite_cond_eq_true` it is `c = True`; the recorder writes `pre: "P"` and `close: true_intro`, so
the trace claims a goal of `P` closed by `True.intro`.

The recorder already does this correctly elsewhere: `Recorder.lean:343` builds
`SideRec.mk ty …` from the condition proof's **type**, which is the real side goal. Both paths
run in one trace, and the result is visibly inconsistent:

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean test/SimpTrace/LogicBasicTraced.lean
python3 -c "import json;d=json.load(open('test/SimpTrace/meas_out/LogicBasicTraced_21.json'));\
[print(s['name'],[x['pre'] for x in s.get('side',[])]) for s in d['locations'][0]['steps']]"
```
```
congrFun            ['P']            <- diverted path, WRONG frame
dite_cond_eq_false  ['P = False']    <- proof-type path, right frame
```

T2 names it exactly:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t1r9/SideFix3.lean
```
```
error: explicit_rw: step 1: lemma `eq_false h` does not match the subterm at position [].
Expected
  P
but the subterm is
  P = False
```
With the frame corrected — the side step at `[0, 1]` and the close `rfl` instead of
`true_intro` — the identical step replays (`/private/tmp/t1r9/SideFix4.lean`, exit 0). So this is
a recorder defect, not a limit of what can be replayed.

`ite_cond_eq_true` has the mirror-image form, which the `r2` probe below shows as
`Expected f ?x but the subterm is (f a = a) = True`.

**16 side traces corpus-wide** carry it (`FunctionBasic` 3, `LogicBasic` 13), across
`dite_cond_eq_false`, `ite_cond_eq_false`, `dite_congr`, `exists_prop_congr` and `congrFun`. They
are the single largest block of the 30 replay failures.

## 2. CRITICAL — `name` carries raw written syntax, not a name; 16 `rw` steps

The spec says `name` is `"<lemma or hyp name>"`, and the `local` object exists precisely so a
generator can tell a hypothesis from a constant. Sixteen `rw` steps put a whole term there:

| trace | recorded `name` |
| --- | --- |
| `FunctionBasicTraced_02` | `if_neg fun h ↦ hb ⟨a, h⟩` |
| `LogicBasicTraced_07` | `heq_comm (a := a)` |
| `LogicBasicTraced_11` | `@forall_eq _ p a` |
| `LogicBasicTraced_14` (×2) | `@exists_comm (κ₁ _)` |
| `FunctionBasicTraced_17` | `(leftInverse_surjInv hf).comp_eq_id` |
| `FunctionBasicTraced_06` | `dif_pos h` |
| + 9 more | `hh _`, `hf _`, `if_neg ne`, `comp_assoc g _ f`, `@xor_not_right a`, … |

Reproduce:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
python3 -c "import json,pathlib,re
[print(p.name,repr(s['name'])) for p in sorted(pathlib.Path('test/SimpTrace/meas_out').glob('*.json'))
 for l in json.load(open(p))['locations'] for s in l['steps']
 if s.get('kind')=='rw' and not re.fullmatch(r'@?[^\s()\[\]{},]+', s['name'])]"
```

This is not cosmetic. It compounds with `args`: `fid08` below records
`name: "_root_.nontrivial_iff_exists_ne x"` **and** `args: ["(Subtype p)", "x"]`, so a generator
that follows the spec and writes `name` followed by `args` produces
`nontrivial_iff_exists_ne x (Subtype p) x` — two spurious arguments. T2 reports
`Function expected at nontrivial_iff_exists_ne x`. It also puts `↦`, `⟨ ⟩` and named arguments
(`(a := a)`) into a field the spec presents as an identifier; none is in T2's whitelisted
grammar, and three replay failures are plain parse errors because of it
(`FunctionBasicTraced_02`, `FunctionDefsTraced_02`, `LogicBasicTraced_07`).

## 3. CRITICAL — inaccessible names are emitted as un-lexable identifiers, and one shape drops `local` entirely

Two separate problems, 13 fields.

(a) `test/SimpTrace/meas_out/FunctionBasicTraced_08.json`: **eight** `rw` steps with
`name: "a✝"` and **`local: null`**. The spec's remedy for an inaccessible hypothesis is the
`local` object plus `rename_i`, but with no `local` at all a generator cannot know it is a
hypothesis, let alone rename it. (`intro_ctx` steps in the same trace also carry `name: "a✝"`.)

(b) `LogicBasicTraced_18.json` (3 fields) does carry `local`, but
`local.userName` is `h._@.test.SimpTrace.LogicBasicTraced.2759035299._hygCtx._hyg.71` — the raw
hygienic name, where the spec says `"userName": "<name>"`. `FunctionBasicTraced_16` puts `a✝` in
a side trace's `intros`, which T2 parses as a binder name.

`h✝` does not lex at all:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t1r9/Inacc.lean     # error: expected token
```
while the plain-Lean equivalent with `rename_i` succeeds (`/private/tmp/t1r9/Inacc2.lean`, exit 0),
so the information exists and only the rendering is wrong.

## 4. CRITICAL — a position off by one application level, on fresh unmodified Mathlib

`/private/tmp/t1r9/fid07.json` step 1, from `Mathlib/Data/Option/Basic.lean:96`.

The hypothesis is `h : Option.map f = Option.map g`, a rewrite whose LHS is a *partial*
application. T1 records `pos: [0,1]` with `before: "Option.map f (some x)"` — the whole
application, not the function being rewritten.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t1r9/fidrep/fid07.lean
```
```
error: explicit_rw: step 2: lemma `h` does not match the subterm at position [0, 1].
Expected
  Option.map f
but the subterm is
  Option.map f (some x)
```
At `[0, 1, 0]` the same step replays (`/private/tmp/t1r9/Fid07p.lean`, exit 0). Two further
fresh-Mathlib traces fail the same way with a different depth
(`fid04`, `fid05`, `Option.orElse_eq_orElse`: expected `HOrElse.hOrElse`, subterm `o <|> o'`).
Positions are the recorder's core competence and this is a two-file sample that was not chosen to
provoke it.

## 5. MAJOR — RESULT.md's headline site count is wrong by two, and its reconciliation is invented

`RESULT.md:60`, `:64`, `:171`.

All three sentences say **84**. The tool says **82**:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
python3 -B test/SimpTrace/check_transcription.py     # 17+1+2+8+23+31 = 82
ls test/SimpTrace/meas_out/*.json | wc -l            # 82
python3 -B Experiment/check_simp_trace.py --report   # calls total 82
```
`check_transcription.py` never prints a total, so the 84 is hand-arithmetic over its six rows —
the exact class of error RESULT.md:40 says was eliminated ("the count sentences were wrong in
three consecutive rounds, so the numbers are now the tool's output and nothing else"). RESULT.md:60
also reconciles the gap with "(82 traces; two sites run under `by_cases <;>` and share a file)",
which is not true of this corpus: each module's converted count equals its trace count exactly,
so no site shares a file and there is no 84 to reconcile.

## 6. MAJOR — "16 classified lines … are all one shape" is wrong on 8 of the 16

`RESULT.md:60-62` and `:189-197`.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean test/SimpTrace/FunctionBasicTraced.lean   # 6 lines
lake env lean test/SimpTrace/LogicBasicTraced.lean      # 10 lines
```
The counts are right; the shape claim is not. **None** of `FunctionBasic`'s 6 is a transported
proof — all six are `side condition rewritten to True`, every one a `Function.update_of_ne` with
a `≠` side goal. And 2 of `LogicBasic`'s 10 are `unreadable_rw_statement:congrFun`, a third shape
introduced by the round-8 m6–m8 work and not in the list at all. The "transported proof term" shape
accounts for 8 of 16, not 16 of 16. (`:192-195` does list three shapes with counts 8 and 6, so the
prose at `:60-62` contradicts the limitations section two hundred lines below it.)

## 7. MAJOR — `change.to` can carry `have` syntax and embedded newlines, which no replayer can splice

`test/SimpTrace/expected/let_body_zeta_off.json`, `let_operand_zeta_off.json` — 5 fields.

```
'have x : Nat := a;\nf\n  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat …)'
```
`to` is the term a replayer writes into `change t at [pos]`. T2 refuses it by name:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t1r9/ChTo.lean
# error: unexpected token 'have'; expected explicitRwTerm
```
The checker validates `args` for `⋯` and delimiter balance (`check_simp_trace.py:170-176`) but
applies neither test to `to`, which has the same "a replayer writes this" contract.

## 8. MINOR — `check_side_positions` only covers atomic side goals

`Experiment/check_simp_trace.py:280-310`.

`_pp_atomic` returns false for anything containing a space, paren or `¬`, and the check returns
immediately in that case. So it catches the precise shape REVIEW-8 exhibited and nothing else:

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
python3 /private/tmp/t1r9/probe_side_check.py
```
| side `pre` | step `pos` | verdict |
| --- | --- | --- |
| `P` | `[0,1,0,1]` | caught |
| `¬P` | `[1]` | passes (correct) |
| `¬P` | `[0,1,0,1,0,1,0,1]` | **passes (missed)** |

It is a real guard against a regression, but it is not the general check RESULT.md:160-161
presents ("the checker gained `check_side_positions`"), and it did not catch defect 1, whose 16
traces all have `pos: []` and so are invisible to a position test.

---

## Logic/Basic classified

10 classified lines at **5 distinct sites** (each doubled by `<;>` running the call on both
`by_cases` branches), not the 8 at one shape the round was asked to confirm. Reproduce with
`lake env lean test/SimpTrace/LogicBasicTraced.lean` (exit 0 for the module; the lines are
`error:` diagnostics).

Verdict key: **(a)** genuinely unrepresentable, **(c)** validator false positive (replays in plain
Lean).

| # | site | call & goal | classification | verdict |
| --- | --- | --- | --- | --- |
| 1-2 | `:553` ×2 | `imp_forall_iff_forall`, `by_cases h : A <;> simp [h]`, goal `(A → ∀ h : A, B h) ↔ ∀ h : A, B h` | `transported proof term at a rewritten proposition; positions checked, proof identity not` | **(a)** — `rw [eq_true h]` and `rw [eq_false hn]` both fail `motive is not type correct`, and Lean's own hint names `simp`/`conv` (`/private/tmp/t1r9/Transp9.lean`). `B h`'s type depends on the rewritten `A`; neither `rw` nor the `congr` kind (`CongrArgKind.cast` on a *proposition*, not an argument of an application) expresses it. |
| 3-4 | `:974` ×2 | `dite_apply`, `by_cases h : P <;> simp [h]`, goal `(dite P f g) a = dite P (fun h ↦ f h a) fun h ↦ g h a` | `unreadable_rw_statement:congrFun` | **(a)** as a classification, **but a different shape from the other four.** `congrFun` is plumbing (`f = g → ∀ a, f a = g a`) that is missing from `isPlumbingHead` (`Recorder.lean:230-237`), so it escapes as a `rw` and the structural check then correctly cannot read a rewrite out of it. Honest, but it is not "transported proof" and RESULT.md does not list it. Its trace also carries the defect-1 frame error on `congrFun`'s own side (`pre: "P"`). |
| 5-6 | `:1020` ×2 | `dite_prop_iff_and`, `by_cases h : P <;> simp [h, forall_prop_of_false, forall_prop_of_true]`, goal `dite P Q R ↔ (∀ h, Q h) ∧ ∀ h, R h` | `transported proof term …` | **(a)** — `rw [eq_false h]` → `motive is not type correct` (`/private/tmp/t1r9/Transp10.lean`). The `True`/`¬False` halves REVIEW-8 found here are gone, as intended. |
| 7-8 | `:1052` ×2 | `mem_dite`, `by_cases h : p <;> simp [h]`, goal `(a ∈ if h : p then s h else t h) ↔ …` | `transported proof term …` | **(a)** — `rw [eq_false h]` → `motive is not type correct` (`/private/tmp/t1r9/Transp11.lean`). |
| 9-10 | `:1056` ×2 | `dite_mem`, same shape, goal `(if h : p then a h else b h) ∈ s ↔ …` | `transported proof term …` | **(a)** — as 7-8, same file, same failure. |

**No false positive among the ten.** Every replay attempt failed in plain Lean for the reason the
classification names. Four of the five sites are the genuine transported-proof shape; the fifth
(`:974`) is a distinct, also-honest shape that RESULT.md does not account for (defect 6).

**The other five modules.** `IsEmptyBasicTraced`, `NontrivialDefsTraced`, `FunctionDefsTraced` and
`ExistsUniqueTraced` emit **zero** classified lines. `FunctionBasicTraced` emits **6**, at `:665`,
`:684`, `:797` and `:976` ×3 — every one `side condition rewritten to True`, every one a
`Function.update_of_ne` whose side goal is a `≠` (`a ≠ a'`, `b ≠ a`, `j ≠ i` ×2,
`(a, a') ≠ (a₂, a₂')`, `a ≠ a₂`). All genuine: the discharging lemmas are diverted and carry no
position, so no close form names them honestly. **Six-module total 16**, which matches
RESULT.md's count but not its shape claim (defect 6).

## Residual risk

The removed in-tactic replay validated a side trace against its own `pre`. The checker's
replacement (`check_side_positions`) validates only that a *position* can exist in an *atomic*
goal. Everything the tactic and the checker jointly miss is therefore: **a side trace whose goal
is stated in the wrong frame, whose steps all sit at `[]`, and whose close form is wrong for the
real goal.** That is precisely defect 1, and it is invisible to a position test.

Four candidates, all built to pass both gates and all doing so:

| # | shape | traced | tactic | checker | T2 replay |
| --- | --- | --- | --- | --- | --- |
| r1 | side `pre` stated up to instances (`ite_cond_eq_false` under `[inst : Decidable P]`) | exit 0 | pass | pass | **FAIL** — `Expected P but the subterm is P = False` |
| r2 | side goal with a higher-order/metavariable shape (`h : ∀ x, f x = x` discharging `f a = a`) | exit 0 | pass | pass | **FAIL** — `Expected f ?x but the subterm is (f a = a) = True` |
| r3 | nested side trace two levels deep with `intros` at both levels (`dite` + `exists_prop_congr`) | exit 0 | pass | pass | **FAIL** — same, on the outer `dite_cond_eq_false` |
| r4 | side condition discharged under a binder the traversal introduced (`∀ n, if f n then …`) | exit 0 | pass | pass | **FAIL** — `Application type mismatch` on `eq_false h` |

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r9 lake env lean /private/tmp/t1r9/Risk.lean   # exit 0
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
for i in 1 2 3 4; do lake env lean /private/tmp/t1r9/riskrep/r$i.lean; done       # all fail
```

r3 is the sharpest: within one trace, `exists_prop_congr`'s side records `pre: "¬P"` and
`pre: "Q h"` correctly (proof-type path) while `dite_cond_eq_false`'s records `pre: "P"`
(diverted path). The recorder is right and wrong about the same question eight lines apart.

**The implementer's judgement that a misclassifying check is worse than no check was sound; the
conclusion that the positional check covers the same ground was not.** A check that compares a
side trace's `close` form against its own `pre` — `true_intro` requires `pre == "True"` — would
have caught all 16 without running anything, and is not the in-tactic replay that produced false
positives three times.

## Fidelity

**No goal-state divergence from stock anywhere this round.**

**Accumulated battery (REVIEW-4..8 shapes), 16 goals.** `add_zero`, binders, `ite` via
`reduceIte`, literal arithmetic, `Iff` local, `←`, conditional with a discharged side, a `prop`
local, `at h` closing by absurdity, `reduceCtorEq`, `let`/`zeta`, `dite`, projections, contextual
implication:
```
lake env lean /private/tmp/t1r8/AccS.lean                                          # stock  0 errors
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r9 lake env lean /private/tmp/t1r9/AccT.lean    # traced 0 errors
```

**10 fresh real-Mathlib calls** from `Mathlib/Data/Option/Basic.lean` and
`Mathlib/Logic/Nontrivial/Basic.lean` (`/private/tmp/t1r9/Fid{S,T}.lean`):

| # | source | call |
| --- | --- | --- |
| 1-3 | `Option/Basic:48,56,59` | `mem_map`, `forall_mem_map`, `exists_mem_map`, `simp` |
| 4-5 | `Option/Basic:195,198` | `orElse_eq_some`, `orElse_eq_none`, `simp` |
| 6 | `Option/Basic:234` | `getD_comp_some` body, `simp only [Function.comp_apply, getD_some, id_eq]` |
| 7 | `Option/Basic:96` | `map_injective'` body, `simp only [← map_some, h]` |
| 8 | `Nontrivial/Basic:39` | `Subtype.nontrivial_iff_exists_ne`, `simp only [nontrivial_iff_exists_ne x, Subtype.exists, Ne, Subtype.ext_iff]` |
| 9-10 | `Option` shapes | `Option.map f none = none`; `(some a).getD d = a`, `simp` |

```
lake env lean /private/tmp/t1r9/FidS.lean                                          # stock  exit 0, 0 errors
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r9 lake env lean /private/tmp/t1r9/FidT.lean    # traced exit 0, 0 errors
```
**Both exit 0 with zero errors and zero classified lines, and all 10 traces are written.** This is
a clean result and a real improvement on round 8, where the same exercise produced two
classifications. The `Ne` fix (REVIEW-8 2) is load-bearing here: case 8 rewrites with `Ne` and
would have classified before it.

Divergence from stock: **none**, on any of the 26 goals.

## Mechanical replay

Translator: `/private/tmp/t1r9/translate.py` (~130 lines, scratch only, the seed of T4). It reads
a trace JSON and emits `explicit_rw` text. Every token comes from a spec field —
`kind` selects the production, `pos` becomes `at [...]`, `name`+`dir`+`prop`+`args` become the
rewrite term, `side` becomes `with [...]`, `intros` becomes `intro … ;`, `close.by` maps through
one table (`rfl`/`decide`/`omega`/`nofun` direct, `true_intro` → `exact True.intro`,
`assumption:<n>` → `exact <n>`, `absurd:<h>` → `exact <h>.elim`), `congr` becomes
`congr <arg> [...]`, `eq` becomes `eq (lhs = rhs) by <by>`, `change` uses `to`. Nothing is
hand-tuned per trace. Harness: `/private/tmp/t1r9/replay_each.py` rebuilds each traced module with
exactly one call replaced by its translation and every other call reverted to stock, so each
compile tests one trace.

Ran over **all six modules**, replayed in T2 at `1d8b125`:

| module | traces | translated | replay pass | replay fail | responsible side |
| --- | --- | --- | --- | --- | --- |
| `IsEmptyBasicTraced` | 17 | 17 | **15** | 2 | T1 (defect 1 — `eq_true leftTotal_empty` / `rightTotal_empty` frame) |
| `NontrivialDefsTraced` | 1 | 1 | **1** | 0 | — |
| `FunctionDefsTraced` | 2 | 2 | **1** | 1 | T1 (defect 2 — `name: "h (a == b) h"` does not parse) |
| `ExistsUniqueTraced` | 8 | 8 | **8** | 0 | — |
| `FunctionBasicTraced` | 23 | 18 | **9** | 10 | T1 (defects 1, 2, 3; 4 untranslatable by design, 1 multi-location) |
| `LogicBasicTraced` | 31 | 31 | **14** | 17 | T1 (defect 1 ×13, defect 2 ×2, defect 3 ×2) |
| **total** | **82** | **78** | **48** | **30** | **all T1** |

Plus the fresh-Mathlib battery, translated and replayed the same way:

| module | traces | replay pass | replay fail | responsible side |
| --- | --- | --- | --- | --- |
| `Fid` (10 fresh real calls) | 10 | **6** | 4 | T1 (defect 4 ×3: `fid04`, `fid05`, `fid07`; defect 2 ×1: `fid08`) |

**Every one of the 34 failures names a T1 field.** Not one needed a T2 feature that is missing:
every `kind` and every close form in the corpus has an `explicit_rw` production, `at h` locations
replay (`ExistsUniqueTraced_05`, `_07`), `congr` replays, and `intro …;` side proofs replay. The
four untranslatable traces are the classified `unresolved:` closes, which is correct behaviour.

Failure classes, by count:
- **16** defect 1 (side goal / close in the wrong frame) — the largest block.
- **5** defect 2 (`name` is syntax, not a name) — 3 of them plain parse errors.
- **3** defect 3 (`h✝` / `a✝` spliced as identifiers) — `expected token`.
- **3** defect 4 (position off by an application level) — on fresh Mathlib.
- **3** `unknown free variable` on `at h` in `FunctionBasic` (`_03`, `_14`, `_15`), where the
  hypothesis is bound by a `refine … fun … ↦ ?_`. `at h` replays elsewhere, so the trace is
  missing something about the binder context; I could not isolate it to a single field and do not
  assign a side with confidence — it needs the implementer and T2 to look together.

## Checks

- **Scratch build.** `ExplicitLean/SimpTrace*` oleans and ileans deleted, then
  `lake build ExplicitLean.SimpTrace`: **clean, no warnings, exit 0, 10.93 s, 754 MB**
  (RESULT.md:183 says 10.66 s / 752 MB — consistent).
- **`test/SimpTrace/Fixtures.lean`: exit 0.** One `unusedVariables` linter warning at `:368`, no
  errors.
- **`test/SimpTrace/UnresolvedFixtures.lean`: exit 1 by design**, with **4** classified lines
  (`:30` have-telescope, `:56` `unresTagProc`, `:89` `fixturePlumbProc`, `:101` side-condition)
  plus the unclassified kernel type mismatch at `:88`. RESULT.md:184 now says 4 — defect 6 of
  round 8 is fixed.
- **`python3 -B Experiment/check_simp_trace.py`: `OK: 65 …`, exit 0**, 18.50 s. Matches
  RESULT.md:184-185. Re-run after regenerating every module: still `OK: 65`.
- **`python3 -B test/SimpTrace/check_transcription.py`: exit 0**, every module's converted count
  equal to its source sites. Genuinely fails when a site is reverted to stock
  (`/private/tmp/t1r9/ct_broken.py`: exit 1, both the "still stock" and the "converted ≠ sites"
  assertions fire). The total it implies is 82, not RESULT.md's 84 — defect 5.
- **`--report` reproduces RESULT.md:45-53 exactly**, and genuinely: `meas_out/` deleted, all six
  modules re-run serially, report byte-identical on every data row and the total row.
- **Scope.** `git diff --name-only $(git merge-base codex/search-free-mathlib-2026-08-31
  task/T1-trace-capture) task/T1-trace-capture` lists **95 files, every one owned** (65 under
  `test/SimpTrace/expected/`, 13 elsewhere under `test/SimpTrace/`, 10 under
  `tracking/tasks/T1-trace-capture/`, 5 under `ExplicitLean/SimpTrace/`, plus
  `ExplicitLean/SimpTrace.lean` and `Experiment/check_simp_trace.py`). `ExplicitLean.lean`,
  `lakefile.toml` and `tracking/SIMP-TRACE-SPEC.md` are **not** in the list.
- **No tracked scratch.** `git ls-files test/SimpTrace/` shows only `.lean`, `.py`,
  `expected/*.json` and `.gitignore`; no `out/`, `meas_out/` or `isempty_out/` file is tracked.
  Working tree clean before and after.
- **RESULT.md honesty.** The measurement table, the build figures, `OK: 65`, `Fixtures` exit 0,
  the `UnresolvedFixtures` count and the `--report` mechanisation all reproduce, and the round-8
  section's claims about C1, C2, C3 and M4 are accurate. Three do not hold: the 84 site count
  (defect 5), "16 classified lines … are all one shape" (defect 6), and — less sharply —
  RESULT.md:160-161's description of `check_side_positions` as the general guard the removed
  replay was replaced by (defect 8).

---

**Totals: 4 critical, 3 major, 1 minor; 0 T2-side gaps.**

The round fixed all eight of round 8's items, and the two hardest results in the task are good:
the measurement pipeline is mechanised and reproduces byte-for-byte from a cold regeneration, and
ten fresh real-Mathlib calls now trace with zero divergence and zero classifications where round 8
got two. The `Logic/Basic` classifications are all honest — I could not replay any of the ten.

What does not hold is the merge gate. **48 of 78 mechanically translated traces replay; 30 do
not, and every failure is a T1 field.** Defect 1 is the round's own principle turned on its
head: round 8's C3 rebased side *positions* onto the side goal, but left the side *goal itself*
as the subterm the simproc picked and the close hardcoded to `true_intro`, so the frame error
moved from `pos` into `pre`/`close` and grew from 11 steps to 16 traces. The recorder computes
the right answer forty lines away, on the other path into the same field. Defects 2 and 3 are the
same failure of the "name exactly what you observed" rule in a different field: `name` holds
written syntax and inaccessible names go out as tokens that do not lex. Defect 4 is a genuine
positional error on unmodified Mathlib, which is the one class this task cannot ship with.

Defect 1 also answers the round's own open question about the removed in-tactic replay: the
positional check that replaced it cannot see this class at all, but a one-line consistency test
between a side trace's `close` and its `pre` would catch all sixteen without running a tactic.
