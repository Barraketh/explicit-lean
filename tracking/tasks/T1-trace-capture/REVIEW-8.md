# T1-trace-capture: adversarial review, round 8

Scratch for this round is `/private/tmp/t1r8/`, not committed. Working tree clean before and
after; `git status --porcelain` empty. All Lean compiles run serially.

**All eight REVIEW-7 items reproduce as fixed, and both T2 findings hold.** C1: quantified and
conditional locals now carry `local`, and `simp [h]` agrees with `simp [*]` on every shape
(`/private/tmp/t1r8/Attack4.lean`). C2: `exists_prop_congr` is accepted and back in
`Fixtures.lean`. C3: `describeProof` no longer writes `rfl` for an opaque `of_eq_true`. C4: the
four `Logic/Basic` crash sites no longer crash. M5: `Iff.mp`/`Iff.mpr` are not walked, and
`h.symm` records `dir: "rev"`. M6: `UnresolvedFixtures.lean` still emits **4** classified lines
and the kernel mismatch at `:88`, unchanged from round 7. T2's two: every `change` carries `to`
(12/12) and every **emitted** location carries `pre`/`post` (143/143), both pinned by the checker
(`Experiment/check_simp_trace.py:167,266-271`).

**But the round-7 fixes traded four defects for four new ones, three of them on the same
principle: the recorder now classifies work it could describe, and the check now rejects steps
that replay.** The C3 fix over-corrected into a false positive that accounts for 7 of the 8
classified side conditions in the corpus (defect 1). The structural check rejects every
`Ne`-stated lemma (defect 2), which fires on fresh real Mathlib. Side traces carry positions
from the outer goal (defect 3) — T2 refuses them by name. And the `Logic/Basic` module the
round added silently drops 2 of the file's 31 call sites (defect 5).

---

## 1. CRITICAL — 7 of the 8 classified side conditions are `True` or `¬False`, both of which have spec close forms and both of which replay

`ExplicitLean/SimpTrace/Recorder.lean:614-624` (`describeProof`'s `of_eq_true` arm).

The C3 fix replaced "always `rfl`" with "`rfl` when `goalIsRfl`, else classify". `goalIsRfl`
(`Recorder.lean:589-597`) only tests `Eq`/`Iff` defeq, so a side goal that is literally `True`,
or `¬False`, matches neither arm and is classified — although the spec has a close form for each
(`true_intro`, and `nofun` for `¬False`, spec lines 11 and 13-15) and `assumptionName?`
(`:393,:398`) already knows how to name both. The arm never asks what the *goal* is.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean test/SimpTrace/LogicBasicTraced.lean      # exit 1, 12 classified lines
lake env lean /private/tmp/t1r8/SideReplay.lean         # exit 0 — all four replay
```
Corpus-wide tally of classified side goals (`meas_out/` + `isempty_out/`):

| side goal `pre` | count | provable in plain Lean by | spec close form |
| --- | --- | --- | --- |
| `True` | 4 | `True.intro` | `true_intro` ✓ |
| `¬False` | 3 | `not_false` / `nofun` | `nofun` ✓ |
| `b ≠ a` | 1 | (genuinely diverted) | — |

`/private/tmp/t1r8/SideReplay.lean` replays all four shapes as plain `rw` with the side supplied
explicitly — `rw [exists_prop_of_true True.intro]`, `rw [forall_prop_of_false not_false]`,
`rw [forall_prop_of_true True.intro]`, and `exists_prop_of_false not_false` — **exit 0**. So
seven of the eight are validator false positives, not "gaps in what the validator can confirm"
as RESULT.md:174-180 describes them.

This inflates the headline figure: of `Logic/Basic`'s 12 classified lines, **6 are this defect**
(`:900`, `:1012` and half of `:1020`, each doubled by `<;>`), and both of
`FunctionBasicTraced.lean`'s 2 (`:684`'s `b ≠ a` is genuine, `:848`'s `True` is not). Fixing it
takes 12 classified lines to 6 and the corpus's 14 to 7.

## 2. CRITICAL — the structural check rejects every `Ne`-stated simp lemma; it fires on fresh real Mathlib

`ExplicitLean/SimpTrace/Tactic.lean:453-458` (`rwStatement?`'s `| some false` arm).

For a `prop: "false"` step the arm reads the conclusion with `concl.not?` and falls back to
`(concl, False)` when that fails. `Ne` is a *definition* (`a = b → False`), so `not?` returns
`none` on `0 ≠ 1` without unfolding it, and the statement becomes `(0 ≠ 1) = False` — which
cannot unify with the recorded `before: "0 = 1"`. The step is then classified
`unresolved:unreplayable_rw:<name>`. The `| none =>` arm immediately below (`:459-473`, `whnfR` at `:466`) *does*
apply `whnfR` as a fallback for exactly this reason; the `some false` arm does not.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r8/NeProbe.lean    # not? = false ; after whnfR, not? = true
lake env lean /private/tmp/t1r8/ZNO.lean        # exit 0 — the rejected step replays
lake env lean /private/tmp/t1r8/NeFreq.lean     # 3 classifications, all this shape
```
`NeProbe.lean` prints the root cause exactly:
```
type: 0 ≠ 1          not? = false
whnfR: ¬0 = 1        not? = true
```
`ZNO.lean` is the step the check calls unreplayable, on its own —
`example : (0 = 1) = False := by rw [eq_false Nat.zero_ne_one]` — **exit 0**, both bare and under
a rewritten hypothesis. The classification is a false positive, contradicting the round-7 fix
whose stated point was that C2 "was my false positive".

**It fires on fresh, unmodified Mathlib.** Two of the ten new real calls in the Fidelity section
(`Mathlib/Data/Nat/Init.lean:77` and `:78`, the `two_le_iff` branches) classify:
`unreplayable_rw:Nat.zero_ne_one` and `unreplayable_rw:Nat.succ_ne_self`. A third independent
hit appeared while probing `describeProof` (`/private/tmp/t1r8/Close5.lean:29`). `Ne` is one of
the most common shapes in Mathlib's simp set, so this is a systematic 20% classification rate on
a two-file sample that was not chosen to provoke it.

`Nat.succ_ne_self` additionally needs its explicit `0`, which `args` omits — see defect 4.

## 3. CRITICAL — side-trace steps carry positions from the outer goal, not relative to the side goal; T2 rejects them by name

Visible in `test/SimpTrace/meas_out/LogicBasicTraced_19.json` and ten others.

The spec says `POS` is "a JSON array of child indices **from the root of the location**", and a
side trace "a nested trace object with the same `steps`/`close` shape and, like a location, `pre`
and `post`" — so its steps' positions are rooted at the side goal. They are not: they are the
position the outer traversal happened to be at when the discharger ran.

`LogicBasicTraced_19.json`'s first step has a side trace whose goal is `pre: "P"` — an atom, whose
only valid position is `[]` — carrying a step at `pos: [0,1,0,1]`.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t1r8/T2rep3.lean
```
T2 names the defect precisely:
```
error: explicit_rw: step 1: position [0, 1, 0, 1] does not exist: the subterm at
prefix [0, 1] is a free variable (no children), so it has no child 0.
```
**11 side steps corpus-wide** have a position that cannot exist in their own side goal — every
one a `dite_cond_eq_false`/`ite_cond_eq_false`/`congrFun`/`exists_prop_congr` whose side goal is
an atomic `P`, `p` or `¬P`:

| trace | outer lemma | side goal | recorded `pos` |
| --- | --- | --- | --- |
| `LogicBasicTraced_19` | `dite_cond_eq_false` | `P` | `[0,1,0,1]` |
| `LogicBasicTraced_17` | `dite_cond_eq_false` | `P` | `[0,1,0,1]` |
| `LogicBasicTraced_17` | `exists_prop_congr` | `¬P` | `[1]` |
| `LogicBasicTraced_20` | `congrFun` | `P` | `[0,1]` |
| `LogicBasicTraced_23,24,25,26` | `(d)ite_cond_eq_false` | `P` | `[0,1]` |
| `LogicBasicTraced_27` | `dite_cond_eq_false` | `p` | `[0,1,0,1]` |
| `LogicBasicTraced_28` | `dite_cond_eq_false` | `p` | `[0,1,1]` |
| `LogicBasicTraced_24` | `exists_prop_congr` | `¬P` | `[1]` |

Round 7 added side `pre`/`post` as a validation channel, and it is `pre` that makes this visible:
a side goal pp'd as `P` cannot host a child index. Nothing checks the two against each other —
`check_simp_trace.py` validates a side trace's `intros`, `pre` and `post` but never navigates its
positions, and `validateNested` (RESULT.md:94) recurses through `congr`, not through `side`. The
responsible side is **T1**: T2 navigates by raw child index, which is what the spec tells it to do.

## 4. MAJOR — `args` are pretty-printed without parentheses and can contain elided proofs, so splicing them as the spec prescribes is a parse error

`test/SimpTrace/meas_out/LogicBasicTraced_21.json` and four others.

The spec calls `args` a list of `"<explicit arg term>"`, i.e. terms a replayer writes. Five
recorded values across four traces are compound pp output with no enclosing parentheses:

| trace | lemma | recorded `args` entry |
| --- | --- | --- |
| `LogicBasicTraced_21`, `_22` | `ite_cond_eq_false` | `'if Q then a else b'` |
| `FunctionBasicTraced_05` | `h.choose_spec` | `'fun a => f a = b'` |
| `FunctionBasicTraced_14` | `(leftInverse_surjInv hf).comp_eq_id` | `'leftInverse_surjInv hf'` |
| `FunctionBasicTraced_14` | same | `'surjInv ⋯'` |

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r8/ArgParen.lean
```
Splicing `_21`'s two args into the application the spec describes gives
`rw [ite_cond_eq_false if Q then a else b b (eq_false hp)]` →
`error: unexpected token 'if'; expected ']'`. The last entry is worse: `surjInv ⋯` carries the
`⋯` proof elision REVIEW-7 8 flagged on `before`/`after`, where it was *within* the spec because
those are debug fields. `args` is not a debug field — a replayer is told to write it — so `⋯`
there is a term that cannot be elaborated at all.

Also in this class: `simp_trace [h.mp hp]` records `args: ["p","q","h","hp"]`, which are the
lemma's *implicits* rather than explicit arguments; applying them as written fails
(`/private/tmp/t1r8/MpReplay.lean`, "Function expected at h.mp hp"). Ignoring `args` and writing
`rw [eq_true (h.mp hp)]` succeeds, so the step is replayable and the recorded `args` are the only
thing wrong.

## 5. MAJOR — `LogicBasicTraced.lean` silently drops 2 of the file's 31 call sites, and both still run stock `simp`

`test/SimpTrace/LogicBasicTraced.lean:498` and `:1072`.

**Reconciling the counts** (the round's main question): `Mathlib/Logic/Basic.lean` contains
**31 tactic-position `simp`/`simp only` call sites** (`/private/tmp/t1r8/orig_simp_lines.txt`;
72 lines mention `simp`, of which 41 are `@[simp]` attributes, comments, doc text, declaration
names or the two term-position `Simp.simp` API calls at `:55,:86`). REVIEW-7's "42 calls" counted
**executions**, not sites: eleven sites are under `<;>` after `by_cases`, so each runs twice
(31 + 11 = 42). Both figures were right about different things; RESULT.md's "29 calls" is a third
quantity — the sites the traced copy actually converted.

**Two sites were dropped by the transcription.** Both have the shape `<tactic>; simp` — a
semicolon-sequenced trailing call — which the generator's rewrite missed:

| original | text | traced copy |
| --- | --- | --- |
| `:497` `heq_of_eq_cast` | `by rintro rfl; simp` | `:498`, **still `simp`** |
| `:1071` `beq_eq_beq` | `by rw [Bool.eq_iff_iff]; simp` | `:1072`, **still `simp`** |

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
grep -c simp_trace test/SimpTrace/LogicBasicTraced.lean          # 29
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r8 lake env lean /private/tmp/t1r8/LBdropped.lean
```
`LBdropped.lean` is the module with those two converted as well: **both trace cleanly** — no new
error at `:498` or `:1072`, and `dropA.json`/`dropB.json` are written. So this is not a recorder
limitation being hidden; it is a measurement gap. Two consequences: the module reports 29/31
coverage as though it were complete, and a file whose stated purpose is to demonstrate removing
the simp family from a Mathlib file still contains two live `simp` calls, which the governing
rule (`AGENTS.md:22-28`) forbids in translated source.

## 6. MINOR — RESULT.md's classified-line count is wrong for the third consecutive round

`tracking/tasks/T1-trace-capture/RESULT.md:169`.

"`UnresolvedFixtures.lean`: exits 1 by design, 2 classified lines." It emits **4**, plus the
unclassified kernel type mismatch:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean test/SimpTrace/UnresolvedFixtures.lean; echo $?   # 1
```
```
:30  `have` telescope simplified as a unit … recorded as one `change`
:56  simproc:…unresTagProc (UnresTag k = True)
:89  simproc:…fixturePlumbProc side condition … proved by a term no close form describes
:101 side condition rewritten to `True` by lemmas whose steps carry no position
:88  (kernel) declaration type mismatch …            <- unclassified
```
This is verbatim REVIEW-7 6, which reported the same wrong number in the same sentence; the
round-7 work moved one line (`:69` → back to `Fixtures.lean`) and added another (`:89`) without
touching the count. RESULT.md:161 says "The count sentences are regenerated rather than
hand-written" — the measurement table is (verified below), but this sentence is not.

## 7. MINOR — RESULT.md overstates where `pre`/`post` is pinned, and understates the round-7 outcome at three sites

`RESULT.md:161-163` and `:166`.

(a) ":161-163" says "every `change` carries `to` and every location carries `pre`/`post` — both
were already emitted (6/6 and 61/61) but the *expected skeletons* omitted them". The skeletons
**still** omit them: all 67 `expected/*.json` locations lack `pre`/`post`. What the round added
is `check_location_fields` (`check_simp_trace.py:266-271`), which requires them on the *emitted*
trace — which is the right place and does pin them (143/143 emitted locations carry both). The
claim as written describes a change to the skeletons that did not happen.

(b) ":166" says "The four sites REVIEW-7 4 found crashing now trace." They no longer crash, which
was the critical part, but three of the four (`:1020`, `:1052`, `:1056`) now emit a *classified*
outcome rather than a clean trace. "Trace" is the word RESULT.md uses elsewhere in opposition to
"classified" (`:53`, `:165`), so the sentence reads as a stronger result than was achieved.

## 8. MINOR — `Tactic.lean:493-497` still treats an unresolvable statement as a pass, and its comment still says so

`ExplicitLean/SimpTrace/Tactic.lean:493-497`.

RESULT.md:143 states the new rule as "**'none' is never a pass**". The code still has

```
let some (lhs, rhs) ← rwStatement? o args prop?
  -- No statement to check against: … The positional check on `before`/`after`
  -- still applies; we do not claim more than we verified.
  | return none
```

— the same `| return none` and the same comment REVIEW-7 1 quoted. What the round actually added
is earlier and narrower: `rwStatement?` (`:415-425`) classifies an origin that resolves to
neither a global constant nor a local fvar, so `simp_trace [show a = b from h]` now reports
`unresolved: origin` (`/private/tmp/t1r8/Unres.lean:13`, confirmed). But a resolvable origin whose
*statement* cannot be read still returns `none` and still passes unchecked, and
`simp_trace [h.mp hp]` reaches that path: it emits a `rw` with no `local`, unverified, with the
wrong `args` (defect 4). The rule holds for origins, not for statements; RESULT.md states it
without that qualification.

---

## Logic/Basic classified calls

29 `simp_trace` calls, 12 classified lines at **6 distinct sites** (each doubled by `<;>` running
the call on both `by_cases` branches). Reproduce with
`lake env lean test/SimpTrace/LogicBasicTraced.lean` (exit 1).

Verdict key: **(a)** genuinely unrepresentable, **(b)** representable but not emitted (recorder
defect), **(c)** validator false positive (replays in plain Lean).

| # | site | original call & goal | classification line | verdict |
| --- | --- | --- | --- | --- |
| 1-2 | `:553` ×2 | `Mathlib:552` `by_cases h : A <;> simp [h]`, goal `(A → ∀ h : A, B h) ↔ ∀ h : A, B h` | `transported proof term at a rewritten proposition; positions checked, proof identity not` | **(a)** — `h : A` is rewritten to `False` while a proof of `A` is carried into `B ⋯`. `rw` refuses it: `/private/tmp/t1r8/Transp.lean` → `motive is not type correct`, and Lean's own hint names `simp`/`conv`. A `CongrArgKind.cast` dependent; the spec's `congr` kind covers this shape but the recorder does not reach for it here. Honest as recorded. |
| 3-4 | `:900` ×2 | `Mathlib:899` `by_cases P <;> simp [*, exists_prop_of_true, exists_prop_of_false]`, goal `dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c` | `side condition rewritten to `True` by lemmas whose steps carry no position` | **(c)** — the two side goals are `¬False` and `True`. `/private/tmp/t1r8/SideReplay.lean` replays both steps as `rw [exists_prop_of_false not_false]` and `rw [exists_prop_of_true True.intro]`, **exit 0**. Defect 1. |
| 5-6 | `:1012` ×2 | `Mathlib:1011` `by_cases h : P <;> simp [h, exists_prop_of_false, exists_prop_of_true]`, goal `dite P Q R ↔ (∃ p, Q p) ∨ ∃ p, R p` | same | **(c)** — identical shape to 3-4, side goals `¬False` and `True`. Defect 1. |
| 7-8 | `:1020` ×2 | `Mathlib:1019` `by_cases h : P <;> simp [h, forall_prop_of_false, forall_prop_of_true]`, goal `dite P Q R ↔ (∀ h : P, Q h) ∧ ∀ h : ¬P, R h` | `side condition rewritten to `True` …; transported proof term …` | **(c) + (a)** — two reasons on one line. The side half is `¬False`/`True`, replayed by `rw [forall_prop_of_false not_false]` / `rw [forall_prop_of_true True.intro]`, exit 0 (defect 1). The transported half is genuine, as 1-2. |
| 9-10 | `:1052` ×2 | `Mathlib:1051` `mem_dite`, `by_cases h : p <;> simp [h]`, goal `(a ∈ if h : p then s h else t h) ↔ …` | `transported proof term …` | **(a)** — `dite_cond_eq_false` leaves `t ⋯`, a proof of `p` transported where the running term has `False`. Same class as 1-2. |
| 11-12 | `:1056` ×2 | `Mathlib:1055` `dite_mem`, same shape, goal `(if h : p then a h else b h) ∈ s ↔ …` | `transported proof term …` | **(a)** — as 9-10. |

**Summary: 6 of the 12 lines are (c), a validator false positive** (sites `:900`, `:1012`, and
the side half of `:1020`); the other 6 are (a), genuine dependent-proof transport. None is (b).
Correcting defect 1 takes `Logic/Basic` from 12 classified lines to 6, at 3 sites.

**The other five traced modules.** `IsEmptyBasicTraced`, `NontrivialDefsTraced`,
`FunctionDefsTraced` and `ExistsUniqueTraced` emit **zero** classified lines.
`FunctionBasicTraced` emits 2:

| site | side goal | verdict |
| --- | --- | --- |
| `:684` (`FunctionBasicTraced_06`, `simp_trace +contextual`, lemma `Function.update_of_ne`) | `b ≠ a` | **(a)** — a real hypothesis discharged by diverted lemmas; no close form names it honestly. |
| `:848` (`FunctionBasicTraced_08`, `simp_trace only [extend_def, dif_pos, …]`, lemma `dif_pos`) | `True` | **(c)** — defect 1; `True.intro` closes it. |

Corpus-wide that is **7 of 14 classified outcomes** removable by fixing defect 1, and **1 of 14**
(`Nat.zero_ne_one`-class) not present here only because these six modules happen not to use a
`Ne`-stated lemma in a `prop: false` position — defect 2 adds more as soon as they do.

## eqUpToProofs attack (task 3)

`/private/tmp/t1r8/Attack3.lean`, **exit 0 — no crash, no classification, all six traced.**
```
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r8 lake env lean /private/tmp/t1r8/Attack3.lean
```
| probe | result |
| --- | --- |
| nested `dite` with dependent proofs (`if h : p then if h2 : q then f h h2 else g h else 0`) | traced |
| `Subtype.mk` with a rewritten proposition (`(⟨k, hk⟩ : {n // P n}).1`) | traced |
| `Fin.mk` with a rewritten bound | traced |
| `Exists.intro` with a rewritten witness type | traced |
| `cast` in the goal | traced |
| `HEq` in the goal | traced |

The round-7 change (descend under binders with a real local; classify transported proofs rather
than abort) holds up: the loose-bvar crash class did not recur on any of these, and the
`Logic/Basic` sites that used to crash now produce output. **No defect.**

## Origin resolution (task 4)

`/private/tmp/t1r8/Attack4.lean`. Every rewrite below carries `local` with the right `userName`
and `ctxIndex`, the right `dir`, and `prop` where the lemma is Prop-valued:

| written | recorded |
| --- | --- |
| `[h]`, `h : ∀ x, F x = G x` | `local` ✓ `dir fwd` ✓ |
| `[*]`, same | **identical** to `[h]` ✓ (the round-5/6/7 disagreement is gone) |
| `[h, hp]`, `h : ∀ x, P x → F x = G x` | `local` ✓ |
| `[h]`, `h : ∀ x, P x` | `local` ✓ `prop: true` ✓ |
| `[*]`, same | identical ✓ |
| `[h.symm]`, `h : b = a` | `local: h` ✓ **`dir: rev`** ✓ (M5 fixed) |
| `[h.2.1]` | `local: h` ✓ `prop: true` ✓ |
| `[(h k).1]` | `local: h` ✓ `args: ["k"]` ✓ |
| `[h, ← h]` | stock `simp` also fails (maximum recursion depth) — not a fidelity gap |
| `[h.mp hp]` | **no `local`**, unverified, `args` are implicits — defect 4 / defect 8 |

**"none = pass":** `grep` finds no such literal, and an unresolvable *origin* now classifies —
`simp_trace [show a = b from h]` → `unresolved: origin` (`/private/tmp/t1r8/Unres.lean`, exit 1).
But an unresolvable *statement* still returns `none` and still passes; `[h.mp hp]` and
`[h.mpr hq]` both take that path. Defect 8.

## describeProof / closes (task 5)

| requirement | result |
| --- | --- |
| `rfl` only when defeq | ✓ — `goalIsRfl` gates it (`Recorder.lean:589`); the opaque `P k` of REVIEW-7 3 no longer gets `rfl` |
| opaque `of_eq_true` classifies | ✓ — but it now classifies `True` and `¬False` too (defect 1) |
| `true_intro` | ✓ — `Recorder.lean:393`, and as the location close on all five probes |
| `absurd:<h>` with display names | ✓ — `expected/absurd.json` pins `"by": "absurd:h"`; the display form is used, per REVIEW-6 5 |
| `nofun` | ✓ — `expected/ctor_eq_inductive.json` pins `"by": "nofun"`, decided from the condition's *type* (`isNofunProof`, `Recorder.lean:409-419`) |

## Fidelity

**No goal-state divergence from stock anywhere this round.**

**Accumulated battery (REVIEW-4..7 shapes), 16 goals** — `add_zero`, binders (`∀`/`fun`),
`ite` via `reduceIte`, literal arithmetic, `Iff` local, `←`, conditional with a discharged side,
a `prop` local, `at h` closing by absurdity, `reduceCtorEq`, `let`/`zeta`, `dite`, projections,
contextual implication:
```
lake env lean /private/tmp/t1r8/AccS.lean                                    # stock  exit 0
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r8 lake env lean /private/tmp/t1r8/AccT.lean   # traced exit 0
```
Both **exit 0, zero errors, zero classified lines** — identical outcome on every goal.

**10 fresh real-Mathlib calls**, copied with their goals from `Mathlib/Order/Basic.lean` and
`Mathlib/Data/Nat/Init.lean` (`/private/tmp/t1r8/Fid{S,T}.lean`):

| # | source | call |
| --- | --- | --- |
| 1-4 | `Order/Basic:544-547` | `compl_lt`/`_le`/`_gt`/`_ge`, `simp [compl]` |
| 5 | `Order/Basic:668` | `const_le_const`, `simp [Pi.le_def]` |
| 6 | `Order/Basic` lattice shape | `simp` |
| 7-9 | `Nat/Init:77,78,79` | `two_le_iff` branches, `simp` |
| 10 | `Order/Basic:131` shape | `simp [Nat.not_le] at h` |

```
lake env lean /private/tmp/t1r8/FidS.lean                                    # stock  exit 0, 0 errors
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r8 lake env lean /private/tmp/t1r8/FidT.lean   # traced exit 1
```
**Goal states agree on all ten** — the traced run produces no `unsolved goals` and no tactic
failure. Its exit 1 is two *classifications*, at `Nat/Init:77` and `:78`:
`unreplayable_rw:Nat.zero_ne_one` and `unreplayable_rw:Nat.succ_ne_self`, both defect 2, both
false positives (`/private/tmp/t1r8/ZNO.lean`, exit 0). All 10 traces written. (A first attempt
at case 6 used `Nat.lt_iff_le_not_le`, which loops under **stock** simp — replaced, not a
finding.)

**The six modules, all regenerated from scratch.** `meas_out/` and `isempty_out/` deleted, every
module re-run, then `--report`:

| file | calls | steps | kinds | bytes | wall | peak RSS | unres. | vs RESULT.md |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `IsEmptyBasicTraced.lean` | 17 | 76 | `rw` 70, `unfold` 6 | 15045 | 2.48 s | 646 MB | 0 | ✓ exact |
| `NontrivialDefsTraced.lean` | 1 | 6 | `rw` 6 | 1109 | 2.75 s | 638 MB | 0 | ✓ exact |
| `FunctionDefsTraced.lean` | 1 | 12 | `rw` 8, `proj` 4 | 1878 | 2.82 s | 646 MB | 0 | ✓ exact |
| `ExistsUniqueTraced.lean` | 8 | 29 | `rw` 23, `beta` 4, `unfold` 2 | 5601 | 2.79 s | 649 MB | 0 | ✓ exact |
| `FunctionBasicTraced.lean` | 19 | 106 | `rw` 80, `intro_ctx` 8, `beta` 7, `proj` 5, `unfold` 4, `congr` 2 | 21386 | 3.28 s | 710 MB | 2 | ✓ exact |
| `LogicBasicTraced.lean` | 29 | 159 | `rw` 156, `unfold` 3 | 33034 | 3.84 s | 720 MB | 12 | ✓ exact |
| **total** | **75** | **388** | `rw` 343, `unfold` 15, `beta` 11, `proj` 9, `intro_ctx` 8, `congr` 2 | **78053** | — | — | **14** | ✓ exact |

**Every generated column matches RESULT.md:45-51 line by line**, and does so after full
regeneration, so the `--report` mechanisation is genuine (wall/RSS are hand-transcribed per
RESULT.md:41 and land within noise of the recorded figures). Nothing came near 30 minutes or
40 GB. The `calls` column is what it says — calls *converted* — not the file's call sites; for
`Logic/Basic` those differ, which is defect 5.

## Integration

Replayed against T2 at its current tip **`69aa441`** ("T2: plain antiquotation errors everywhere;
readable congr refusal") — note this is ahead of the `dee3d5d` REVIEW-7 used, and T2's tree is
**dirty** (`Experiment/check_explicit_rw.py`, `RESULT.md`, untracked `test/ExplicitRw/sweep/` and
`tmp9zsj77s9.lean`). `lake build ExplicitLean.ExplicitRw.Tactic` exit 0.

Translation is **mechanical**: `/private/tmp/t1r8/translate.py` (~60 lines, written this round as
the seed of T4) reads a trace JSON and emits the `explicit_rw` step list. Every position, lemma
name, direction, `prop` wrapper, `args` splice and close form comes from the JSON; nothing is
hand-tuned per trace. Five `Logic/Basic` traces:

| # | trace | shape | result |
| --- | --- | --- | --- |
| 1 | `LogicBasicTraced_11` | plain, no local (`forall_eq'`) | **exit 0** |
| 2 | `LogicBasicTraced_04` | `←` with an `@`-applied lemma | **exit 0** |
| 3 | `LogicBasicTraced_19` | **quantified local** `h`, `prop: false` side traces | **MISMATCH — T1 side** (defect 3) |
| 4 | `LogicBasicTraced_18` | **user-congr** (`exists_prop_congr` with `intros`) | translated; blocked behind the same side-position defect |
| 5 | `LogicBasicTraced_21` | `args` on `ite_cond_eq_false` | **MISMATCH — T1 side** (defect 4) |

Files: `/private/tmp/t1r8/T2rep.lean`, `T2rep2.lean` (case 1 with the theorem the trace came
from — my first attempt used `Logic/Basic:658` where the trace is from `:655`; my error, not a
finding), `T2rep3.lean` (case 3).

**Both mismatches are T1's.** Case 3: T2 reports `position [0, 1, 0, 1] does not exist: the
subterm at prefix [0, 1] is a free variable (no children)` — the side trace's position is rooted
at the outer goal, defect 3. Case 5: the translator emits
`ite_cond_eq_false if Q then a else b b at [1]`, which does not parse, because the recorded `arg`
is unparenthesised pp — defect 4. Cases 1 and 2 replay with no mismatch at all.

**No T2-side gaps.** Every kind and every close form in the T1 corpus has an `explicit_rw` form,
the translator needed no T2 feature that is missing, and both failures name a T1 field. The
round-7 note about `close: null` on a congruence side trace still stands: the translator supplies
`then rfl` by rule, which happens to be right, but the trace does not say so.

## Checks

- **Scratch build.** `ExplicitLean/SimpTrace*` oleans deleted, then
  `lake build ExplicitLean.SimpTrace`: **clean, no warnings, exit 0, 11.01 s, 752 MB**
  (RESULT.md:168 says 10.66 s / 752 MB — consistent).
- **`test/SimpTrace/Fixtures.lean`: exit 0.** One `unusedVariables` linter warning at `:368`, no
  errors.
- **`test/SimpTrace/UnresolvedFixtures.lean`: exit 1 by design**, with **4** classified lines
  plus the unclassified kernel type mismatch at `:88`. RESULT.md says 2 — defect 6.
- **`python3 -B Experiment/check_simp_trace.py`: `OK: 65 …`, exit 0**, 18.01 s, 1527 MB. Matches
  RESULT.md:170. Re-run after regenerating every module: still `OK: 65`.
- **`--report` reproduces RESULT.md:45-51 exactly**, and genuinely: all six modules re-run from
  deleted output directories, report byte-identical on the data rows.
- **Scope.** `git diff --name-only $(git merge-base codex/search-free-mathlib-2026-08-31
  task/T1-trace-capture) task/T1-trace-capture` lists **92 files, every one owned** (under
  `ExplicitLean/SimpTrace/`, `ExplicitLean/SimpTrace.lean`, `test/SimpTrace/`,
  `Experiment/check_simp_trace.py`, `tracking/tasks/T1-trace-capture/`). `ExplicitLean.lean`,
  `lakefile.toml` and `tracking/SIMP-TRACE-SPEC.md` are **not** in the list.
- **No tracked scratch.** `git ls-files` shows only `expected/*.json` skeletons (intentional);
  no `out/`, `meas_out/` or `isempty_out/` file is tracked. Working tree clean before and after.
- **RESULT.md honesty.** The measurement table, build figures, `OK: 65`, `Fixtures` exit 0 and
  the `--report` mechanisation all reproduce, and the two claims the implementer corrected
  (round-6's "no false positives", and the args-reversed `exists_prop_congr` command) are
  correctly retracted at `:146-149`. Four claims still do not hold: the classified-line count
  (defect 6), "expected skeletons now carry `pre`/`post`" (defect 7a), "the four crashing sites
  now trace" (defect 7b), and "'none' is never a pass" (defect 8). The "14 classified unresolved
  … gaps in what the validator can confirm rather than wrong traces" framing at `:174-180`
  survives for 7 of the 14; the other 7 are false positives (defect 1).

---

**Totals: 3 critical, 2 major, 3 minor; 0 T2-side gaps.**

The round-7 work fixed every defect round 7 raised — the crash class is gone, quantified locals
resolve, `Iff.mp` no longer misattributes, `exists_prop_congr` is accepted. What it did not do is
hold the line the previous three rounds kept drawing: **the recorder should name exactly what it
observed, and the check should reject exactly what cannot replay.** Defect 1 classifies two goals
the spec already has close forms for; defect 2 rejects a lemma family that replays in one line;
defect 3 emits positions that are meaningless in the frame they are written in, which T2 rejects
by name; defect 4 emits `args` that do not parse. Each is narrow and each is mechanical.

The measurement side is now genuinely mechanised and reproduces exactly — the one gap is defect
5, where two of `Logic/Basic`'s 31 call sites never became `simp_trace` and still run stock simp,
so the module's headline is 29/31 rather than the complete conversion it reads as.
