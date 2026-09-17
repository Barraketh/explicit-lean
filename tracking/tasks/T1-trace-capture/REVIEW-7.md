# T1-trace-capture: adversarial review, round 7 (structural `rw` validation)

Scratch for this round is `/private/tmp/t1r7/`, not committed. Working tree clean before and
after; `git status --porcelain` empty. All Lean compiles run serially.

**All eight REVIEW-6 items reproduce as fixed.** 1: `hα`, `h₃`, `h'`, `hβ.1` all carry `local`
and `prop` — the character whitelist is gone. 2: `args_instance.json` records
`"args": ["fixtureW2", "k"]`, the instance simp actually used. 3: the allowlist is no longer
load-bearing (see below). 4: `dreduce_ite.json`'s first step is
`{"kind":"change","source":"dreduceIte", …}` and **replays in T2** (`/private/tmp/t1r7/T2rep2.lean`,
exit 0), closing REVIEW-6 4 on both sides. 5: `user_congr_ite.json` now has `intros: ["a✝"]` and
`close: {"by":"assumption:a✝"}` — the same display form for the same hypothesis. 6: `zeta` carries
`"name": "g"`. 7: `reverse`/`chained`/`local_eq` expected files carry `local`, and the checker's
unexpected-field tuple at `Experiment/check_simp_trace.py:93` includes `local`/`arg`/`args`.
8: exactly one "Checks" paragraph. Side `pre`/`post` is universal: 91 locations scanned across
`out/` and `meas_out/`, **0 missing**.

**But the new structural check is not the backbone RESULT.md says it is.** It has a false
positive on a real Mathlib shape that fires four times in `Logic/Basic` (defect 2), it passes
every step whose origin did not resolve — which is now a large class (defect 1) — and it does
not cover side-condition closes at all, where the recorder writes a `rfl` it never observed
(defect 3). Separately, four stock-provable `Logic/Basic` calls **crash** the recorder with a
loose bound variable rather than being traced or classified (defect 4).

---

## 1. CRITICAL — every ∀-quantified or conditional local hypothesis loses `local` and `prop`, and the structural check cannot see it

`ExplicitLean/SimpTrace/Recorder.lean:87-94` (`proofFVar?`), with
`ExplicitLean/SimpTrace/Tactic.lean:422-424` (`rwStatement?`'s `| _ => pure none`).

REVIEW-6 1 replaced the character whitelist with a walk over the stored proof term. That fixed
non-ASCII *unquantified* names. It did not fix the general case: simp stores a **quantified**
hypothesis's proof under a binder, so `proof.getAppFn` is a `.lam`, `proofFVar?` falls through
its `| _ => none` arm, `resolveStxOrigin` returns the unresolved `.stx`, and the step carries
neither `local` nor `prop`. `simp [*]` on the identical rewrite records both. This is exactly
the disagreement REVIEW-5 1 and REVIEW-6 1 each closed for a narrower case.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r7 lake env lean /private/tmp/t1r7/FN3.lean
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r7 lake env lean /private/tmp/t1r7/FN3b.lean
```
Four shapes, all losing `local`, none flagged (exit 0, no `unresolved` line):

| goal | written | recorded |
| --- | --- | --- |
| `hf : ∀ x, f x = x` | `simp_trace [hf]` | `{'kind':'rw','name':'hf','dir':'fwd'}` |
| `hf : ∀ x y, f x y = x` | `simp_trace [hf]` | same, no `local` |
| `hf : ∀ {x}, f x = x` | `simp_trace [hf]` | same, no `local` |
| `hf : 0 = 0 → f c = c` | `simp_trace [hf]` | same, no `local` |

The Prop-valued case additionally loses `prop`, which is REVIEW-3 M5 verbatim. On
`(P : Nat → Prop) (hp : ∀ x, P x) ⊢ P c ∧ True`:
```
simp_trace [hp]  ->  {'kind':'rw','name':'hp','dir':'fwd'}                    # P c ↝ True, no prop
simp_trace [*]   ->  {'kind':'rw','name':'hp','dir':'fwd','prop':'true',
                      'local':{'userName':'hp','inaccessible':False,'ctxIndex':3}}
```
A generator handed the `[hp]` trace elaborates `hp : ∀ x, P x`, finds neither an `Eq` nor an
`Iff`, and fails.

**Why the structural check does not catch it, and why that matters more than the defect.**
`rwStatement?` returns `none` for a `.stx` origin that did not resolve, and `checkRwStep`
treats `none` as **pass** (`Tactic.lean:492-497`, "we do not claim more than we verified").
So the check's blind spot is *exactly* the set this defect creates, and the two compound: the
recorder drops the identity, and the validator then declines to check the step because the
identity is missing. Every `simp [h]` on a quantified hypothesis in real Mathlib is in that
set. RESULT.md:155-157 presents the check as making "a misclassified plumbing head impossible
to *ship*"; it is impossible to ship only for origins that resolve.

## 2. CRITICAL — `unreplayable_rw:exists_prop_congr` is a false positive; the step replays in plain Lean

`ExplicitLean/SimpTrace/Tactic.lean:480-537` (`checkRwStep`), with
`test/SimpTrace/UnresolvedFixtures.lean:58-69` and `RESULT.md:165-170`.

RESULT.md justifies moving `exists_prop_congr` to `UnresolvedFixtures.lean` with
"`rw [exists_prop_congr hpq (fun _ => rfl)]` fails in plain Lean, so the step is genuinely
unreplayable as written". That command passes the arguments in the **wrong order**.
`exists_prop_congr` takes the function argument *first*:
```
@exists_prop_congr : ∀ {p p' : Prop} {q q' : p → Prop},
  (∀ (h : p), q h ↔ q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ h, q' ⋯
```
With the arguments in signature order it succeeds:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r7/EPC.lean    # exit 0
lake env lean /private/tmp/t1r7/EPC3.lean   # correct order ok; RESULT.md's order errors
```
`EPC.lean` is `rw [exists_prop_congr (fun _ => Iff.rfl) hpq]` on
`(∃ _ : p, True) ↔ (∃ _ : q, True)` — **exit 0**. `EPC3.lean` runs both forms: the
signature-order one closes the goal, RESULT.md's order gives
"Application type mismatch: the argument `hpq` … is expected to have type
`∀ (h : ?m.4), ?m.6 h ↔ ?m.7 h`". The higher-order `?q'` is not the obstruction; argument order
was.

**The recorded trace is already right.** `test/SimpTrace/out/user_congr_exists.json` carries the
two `side` traces in signature order — the function hypothesis (`r = r`, with `intros: ["h"]`)
first, then `p = q`. So the data needed to emit `rw [exists_prop_congr (fun _ => Iff.rfl) hpq]`
is in the trace; only the check rejects it.

**Answering task 2c directly:** plain Lean *can* replay it, and recording `args` for the function
argument is not needed to make it replayable — the `side` traces already determine it, and
`fun _ => Iff.rfl` is what the first side trace (`pre: "r"`, `post: "r"`, `close: rfl`) says.
Recording it in `args` would make the replay term fully explicit and is worth doing, but the
classification should be lifted either way.

**This is a false positive on the corpus, contradicting RESULT.md:165-166** ("the check added
no false positives"). Stock simp proves the fixture's goal:
`lake env lean /private/tmp/t1r7/EPC4.lean` → exit 0. At scale it fires on **four**
`Mathlib/Logic/Basic.lean` call sites (see **Logic.Basic measurement**).

## 3. CRITICAL — a side condition discharged by a simp lemma is recorded as `close: {"by": "rfl"}`, which cannot prove it

`ExplicitLean/SimpTrace/Recorder.lean:563` (`describeProof`'s `of_eq_true` arm).

`describeProof` maps any proof headed by `of_eq_true` to the close form `"rfl"`, unconditionally,
whenever no nested events were recorded. But simp's default discharger proves a side condition by
*rewriting it to `True` with other simp lemmas* and wrapping the result in `of_eq_true`. Those
inner rewrites are diverted (they carry no position), so `nested` is empty and the recorder
writes `rfl` — a close form it never observed and that does not hold.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r7 lake env lean /private/tmp/t1r7/FP3.lean   # exit 0, no unresolved
lake env lean /private/tmp/t1r7/FP3check.lean                                    # the recorded close
```
`FP3.lean` makes the side condition `P k` where `P` is **`opaque`** and the discharging lemma is
`pk_simp : ∀ n, P n`. Recorded:
```
"side": [{"goal":"P k","pre":"P k","post":null,"steps":[],"close":{"by":"rfl"}}]
```
`rfl` cannot prove an opaque `P k` under any reading, and `FP3check.lean` confirms:
```
error: Tactic `rfl` failed: Expected the goal to be a binary relation
k : Nat
⊢ P k
```
The lemma that actually discharged it (`pk_simp`) is discarded entirely, so the trace is not
merely under-determined — it asserts a falsehood, with `steps: []` claiming nothing was needed.

Two further instances, same root:
- `/private/tmp/t1r7/FP2.lean`: side condition `CCond k` (a definition unfolding to `n + 0 = n`)
  → `close: {"by":"rfl"}`, `steps: []`. Here `rfl` happens to succeed
  (`/private/tmp/t1r7/FP2check.lean`, exit 0), which is worse — it makes the bug look benign.
- `/private/tmp/t1r7/FP.lean` (`apTag_eq`): an **`autoParam`** hypothesis whose auto-tactic is
  `omega` → the side goal is recorded as `autoParam (0 ≤ k) apTag_eq._auto_1` with
  `close: {"by":"rfl"}`. `lake env lean /private/tmp/t1r7/APcheck.lean`:
  ```
  error: Tactic `rfl` failed: The left-hand side 0 is not definitionally equal to … k
  ⊢ autoParam (0 ≤ k) apTag_eq._auto_1
  ```
  The spec has an `omega` close form for exactly this and it is not used; the recorded goal also
  leaks the raw `autoParam` wrapper rather than its payload `0 ≤ k`.

The structural `rw` check does not cover this: it validates the `rw` step, never a side trace's
`close`. This is the round-3 principle (`eq` steps' `by` must not be invented) violated on the
`close` field.

## 4. CRITICAL — four stock-provable `Mathlib/Logic/Basic.lean` calls crash with `unexpected bound variable #0`

Reproduced minimally at `/private/tmp/t1r7/BV.lean`; sites are `LBTraced.lean:553, 1020, 1052,
1056` (`imp_forall_iff_forall`, `dite_prop_iff_and`, `mem_dite`, `dite_mem`).

All four are `by_cases h : X <;> simp_trace [h]` on a goal with a **dependent `dite`/`∀`**. Stock
`simp [h]` proves every one of them; `simp_trace [h]` throws a loose-bound-variable error, which
is neither a trace nor a classified `unresolved:` outcome — it is a hard failure, so the
"every stock-provable call is traced or classified" property does not hold.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r7/BVstock.lean   # stock: exit 0
lake env lean /private/tmp/t1r7/BV.lean        # traced: 2 errors
```
`BV.lean` holds both versions of `mem_dite` side by side; the stock one compiles silently and the
traced one gives
```
/private/tmp/t1r7/BV.lean:13:21: error: unexpected bound variable #0
/private/tmp/t1r7/BV.lean:13:21: error: unexpected bound variable #0
```
(two errors per site because `<;>` runs the tactic on both `by_cases` branches). Nothing is
written for these calls. This is the same *class* as the `Function/Basic:390` PANIC that round 4
fixed in `tryAutoCongrTheoremT?` — a loose bvar reaching a consumer — recurring on the
`dite`-with-dependent-branches shape.

## 5. MAJOR — `proofFVar?` walks into `Iff.mp`/`Iff.mpr`, reaching a hypothesis that does not state the rewrite

`ExplicitLean/SimpTrace/Recorder.lean:87-94`.

`proofFVar?` recurses into `appArg!` for `Iff.mp`, `Iff.mpr` and `Eq.symm`. For the wrappers simp
itself adds (`eq_true h`, `And.left h`, `propext h`) the last explicit argument *is* the
hypothesis being used. For `Iff.mp` it is not: `Iff.mp h hp` takes the *iff* `h` and a proof `hp`
of its left side, and the rewrite is by `h`'s **right** side. Walking to `appArg!` reaches `hp`.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r7 lake env lean /private/tmp/t1r7/PF.lean
lake env lean /private/tmp/t1r7/PFcheck2.lean
```
On `(h : p ↔ q) (hp : p) ⊢ q ∧ True`, `simp_trace [h.mp hp]` records
```
{'kind':'rw','name':'h.mp hp','dir':'fwd','prop':'true','before':'q','after':'True',
 'local':{'userName':'hp','inaccessible':False,'ctxIndex':4}}
```
`local` names `hp : p` while the step rewrites `q`. A generator following `local` + `prop` emits
`rw [eq_true hp]`, which fails outright:
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  p
in the target expression
  q ∧ True
```
The step passes the structural check, because `rwStatement?` builds the statement from the
resolved fvar `hp` and `prop: true` makes it `(p) = True`, which unifies with… nothing here —
but the check never runs, since the origin is `.stx` and unresolved-to-a-different-fvar still
returns a head. Either way no `unresolved` line is emitted and the call exits 0.

`Eq.symm` is the same shape and visible in the same run: `simp_trace [h.symm]` with `h : b = a`
records `name: "h.symm"`, `local.userName: "h"`, `dir: "fwd"`, `before: "a"`, `after: "b"` —
`local` plus `dir` says `rw [h]`, which rewrites `b → a`, the opposite direction.
`lake env lean /private/tmp/t1r7/PFcheck.lean` leaves `⊢ a + 0 = a` unsolved. `Eq.symm` should
flip `dir` when it is unwrapped (the round-6 change does this for the *simproc* path at
`Recorder.lean` but not in `proofFVar?`), and `Iff.mp`/`Iff.mpr` should not be walked at all.

**The rest of the wrapper walk is correct.** `h.2.1` resolves to `h` with `prop: true`;
`(h c).1` resolves to `h`; `h'` and `hβ.1` were already pinned by fixtures. `simp_trace [h, ← h]`
diverges from nothing: stock `simp [h, ← h]` also fails on that goal
(`/private/tmp/t1r7/PFstock.lean`, "maximum recursion depth"), so it is not a fidelity gap. A
`let`-bound local is defect 6 of round 6 and is now fixed (`zeta` carries `name`).

## 6. MAJOR — RESULT.md's "2 classified lines" is wrong, and the "no false positives" claim is contradicted

`tracking/tasks/T1-trace-capture/RESULT.md:173-174` and `:165-166`.

`UnresolvedFixtures.lean` emits **four** classified lines, not two:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean test/SimpTrace/UnresolvedFixtures.lean; echo $?   # 1
```
```
:30  `have` telescope simplified as a unit … recorded as one `change`
:56  simproc:…unresTagProc (UnresTag k = True)
:69  unreplayable_rw:exists_prop_congr
:101 simproc:…fixturePlumbProc side condition … ; unreplayable_rw:…fixturePlumb
```
This is the round-5 and round-6 measurement-drift defect recurring in the same file for the third
round: two lines were added (`:69`, `:101`) by the round-6 work and the count sentence was not
updated. RESULT.md:165-166's "the check added no false positives" is contradicted by defect 2.

The run also prints a fifth, *unclassified* line at `:100`:
```
:100:0: error: (kernel) declaration type mismatch, '…UnresolvedFixtures._example' has type
  ∀ (k : Nat), True    but it is expected to have type    (k : Nat) → FixturePTag k
```
A kernel type mismatch is not a classified outcome. It is benign here — the fixture is designed
to fail and the file exits 1 regardless — but it means the file's exit 1 does not distinguish
"classified unresolved" from "the recorder built a bad proof term", which is the property the
gate is supposed to have.

## 7. MINOR — `local.userName` carries raw hygienic machinery for inaccessible hypotheses

`test/SimpTrace/out/{inaccessible,name_unicode_inaccessible,local_named_inaccessible,shadow_inaccessible}.json`.

Four fixtures record
`"local": {"userName": "a._@._internal.0.test.SimpTrace.Fixtures.2021293447._hygCtx._hyg.14", …}`
while the same step's `name` is the display form `a✝`. REVIEW-6 5 established that the recorder
uses the display form for `name`, `intros` and `close.by`; `userName` is the one site still
emitting the raw name. The spec (`:89-95`) says `ctxIndex` is what identifies the declaration and
that a generator derives `rename_i` names from context order, so nothing is *broken* — but a
field called `userName` holding `_hygCtx._hyg.14` is the kind of inconsistency the previous three
rounds each had to chase somewhere else. Either use the display form or state in the spec that
`userName` is raw.

## 8. MINOR — `before`/`after` elide proof terms as `⋯`, so a validator cannot round-trip them

Visible in `/private/tmp/t1r7/out/` for the `dite` shapes, e.g.
`"before": "∃ hh, A hh = c"`, `"after": "∃ h_1, A ⋯ = c"`.

The spec calls `before`/`after` "debug fields … used by validation; replay must not depend on
them", so this is within the letter of the spec. Worth noting because the round-6 open question
proposed `pre`/`post` on side traces as a *validation* channel, and `⋯` means those fields cannot
serve that purpose for any term containing a proof — which is every `dite` and every conditional
rewrite. If side `pre`/`post` is meant to reconcile the two sides (which is the argument that won
the spec bump), the pp needs `pp.proofs` set.

---

## Validation attack

**(a) Can a step pass the check yet not replay?** Yes, three ways, two of them on real shapes.

| probe | result |
| --- | --- |
| instance argument where unification picks a different defeq instance | **no defect** — `args_instance.json` records `fixtureW2`, and T2 replays it (`T2rep.lean`, exit 0) |
| metavariable-headed LHS (`?f ?x`) | **no defect** — the peel guard at `Tactic.lean:520-522` is correctly conditioned on a rigid LHS; `/private/tmp/t1r7/FN.lean` (`fn_mtag`) records a clean `rw` |
| universe param determined only by the RHS | **not reachable** — the construction makes no progress under stock simp either, so there is nothing to record |
| `←` step | **no defect** — `fn_rev` keeps `dir: "rev"` with `local`, and T2 replays it (`T2rep.lean`, exit 0) |
| `prop`-flagged local | **no defect** for an unquantified local (`fn_prop_local` carries `prop` + `local`, T2 replays it); **defect 1** for a quantified one |
| user-congr with `intros` | **no defect** — replays in T2 (`T2rep4.lean`, exit 0) |
| step under a binder using a binder local in `args` | **defect 1** — `fn_binder`/`fn2_forall_local` lose `local` |
| `before` contains `mdata` | **not reachable** by construction in this corpus |
| `Iff.mp` / `Eq.symm` wrapper | **defect 5** — passes, does not replay |

The two structural holes behind these: `rwStatement?` returns `none` (⇒ pass) for every
unresolved `.stx` and `.other` origin, and the check never inspects a side trace's `close`.

**(b) Can a legitimately replayable step fail the check?** Yes — **defect 2**, on a real Mathlib
shape, four times in `Logic/Basic`. The implementer's four listed subtleties are each sound and I
could not break any of them:

| edge | probe | result |
| --- | --- | --- |
| proof args excluded from `args` | `ite_cond_eq_true` via `reduceIte` | correct — `args` holds values only, the condition is a `side` |
| explicit binder positions, not `mkAppN` | `args_instance` (`fixtureW2` at the instance's explicit slot) | correct |
| `forallMetaTelescope` without reducing | `fp_iff_under_not` (`Iff` in a Prop position under `¬`) | correct — records a clean `rw`, exit 0 |
| peel only on rigid LHS | `fn_mtag` (metavariable-headed) | correct |
| **beyond:** `let` in the lemma's statement | `/private/tmp/t1r7/FP.lean` `letT_eq` | **passes** — no false positive |
| **beyond:** `autoParam` hypothesis | same file, `apTag_eq` | passes the `rw` check, but the side `close` is wrong — **defect 3** |
| **beyond:** `optParam` hypothesis | same file, `opTag_eq` | not reachable (no progress under stock simp) |

**(c) `exists_prop_congr`.** Plain Lean **can** replay it; the classification is a false
positive and RESULT.md's supporting command has its arguments reversed. Recording `args` for the
function argument would make the replay term fully explicit but is not what makes it replayable —
the `side` traces already determine `fun _ => Iff.rfl`. Reported, not fixed. Full detail in
defect 2.

---

## Fidelity

**25 differential goals, goal states byte-identical.** `/private/tmp/t1r7/Diff{S,T}.lean` run the
same goals under `simp` and `simp_trace`, each wrapped in a `first` that reports CLOSED or prints
`trace_state` and reports OPEN.
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r7/DiffS.lean > /private/tmp/t1r7/diffS.out 2>&1
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r7 lake env lean /private/tmp/t1r7/DiffT.lean > /private/tmp/t1r7/diffT.out 2>&1
diff /private/tmp/t1r7/nS2.txt /private/tmp/t1r7/nT2.txt     # 0 lines
```
Ten are new, copied from real Mathlib simp calls with their imports: `Logic/Basic.lean:330,331`
(`and_symm_right`/`_left`, `simp [eq_comm]`), `:589,593` (`forall₂_true_iff` and its ternary
companion), `:655,658` (the two `forall_eq'` shapes), `:428,430` (`xor_iff_iff_not`,
`xor_iff_not_iff'`, both `simp only [← …, not_not]`), and `Order/Basic.lean:646`
(`lt_iff_le_not_ge`) plus `not_lt`. The other fifteen are the accumulated REVIEW-4/5/6 shapes
(binders, `ite`/`dite`, `let`, `prop` locals, projections, literal arithmetic, `←`, contextual).

**Both sides agree exactly**: same CLOSED/OPEN partition (48 CLOSED markers each, identical
23-entry OPEN set), identical `trace_state` output after normalising only the echoed tactic text,
and the same two `unsolved goals` errors at the same positions. **All 25 traces are written,
with zero `unresolved` lines in the traced run** (`grep -c unresolved diffT.out` → 0). Kind
coverage: `rw` 56, `zeta` 1, `eq` 1.

**No goal-state divergence from stock was found anywhere this round**, as in rounds 5 and 6.
Every defect above is a trace-content or robustness defect, not a fidelity one — with the single
exception of defect 4, where the traced run does not reach a goal state at all.

---

## Logic.Basic measurement

Traced copy at `/private/tmp/t1r7/LBTraced.lean`, generated mechanically from
`Mathlib/Logic/Basic.lean` (1087 lines) by rewriting `simp`/`simp only` in **tactic position**
only — attribute brackets, declaration names and the two `Simp.simp` *term*-position API calls at
`:56,:87` are left alone (rewriting those was my generator's artifact, not a defect, and is
excluded from the figures).

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
/usr/bin/time -l lake env lean /private/tmp/t1r7/LB_orig.lean    # stock baseline
/usr/bin/time -l lake env lean /private/tmp/t1r7/LBTraced.lean   # traced
```

| | calls | traced | classified unresolved | hard errors | wall | peak RSS | exit |
| --- | --- | --- | --- | --- | --- | --- | --- |
| stock | — | — | — | 0 | 2.58 s | 667 MB | 0 |
| traced | 42 | **39** | **4** | **8** (at 4 sites) | 3.43 s | 755 MB | 1 |

**1.33x wall, 1.13x RSS.** Nothing came near 20 minutes or 30 GB.

**Unresolved, with reasons.** All four are `unreplayable_rw:exists_prop_congr`, at
`LBTraced.lean:509` (`heq_iff_exists_cast_eq`), `:900` (`dite_eq_iff`, twice — `by_cases P <;>`)
and `:918` (`dite_ne_right_iff`). Per defect 2 these are **false positives**: the step replays in
plain Lean. So the honest reading is 39 traced + 4 mis-classified, and a corrected check should
reach 43 of 43 on the non-crashing sites.

**Not every stock-provable call is traced or classified.** The 8 hard errors are defect 4: four
sites (`:553`, `:1020`, `:1052`, `:1056`), each `by_cases h : X <;> simp_trace [h]` on a
dependent `dite`/`∀`, each producing `unexpected bound variable #0` on both `<;>` branches.
`LB_orig.lean` — the same four theorems, unmodified — compiles **stock with exit 0**, so all four
are stock-provable and none is traced or classified. That is the acceptance property for this
task failing on 4 of 43 real call sites (9%).

---

## Integration

Replayed in `/Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw` at its current tip
`dee3d5d` ("T2: record exact round 6 sweep figures in RESULT.md"), working tree clean, after
`lake build ExplicitLean.ExplicitRw.Tactic` (exit 0). **All five required shapes replay with no
mismatch.** Every position and every lemma name is copied unchanged from the JSON; T2 navigates
by raw child index, so a wrong index fails loudly.

| # | shape | trace | replay | result |
| --- | --- | --- | --- | --- |
| 1 | `args` with an explicit instance | `args_instance.json` | `explicit_rw [fixtureTagE_lem fixtureW2 k at []] then exact True.intro` | **exit 0** |
| 2 | `local` + `prop` + `←` | `local_named_rev.json` / `fn_prop_local` | `explicit_rw [← h at [0,1,0,1], Nat.add_zero at [0,1], eq_self at []]`, and the `eq_true hp` form | **exit 0** (both) |
| 3 | `change` with `source` | `dreduce_ite.json` | `explicit_rw [change 3 at [0,1], unfold ite at […], unfold ite at […], eq_self at [1], implies_true at []]` | **exit 0** |
| 4 | user-congr with `intros` | `user_congr_ite.json` | `explicit_rw [ite_congr at [0,1] with [explicit_rw [hpq at [0,1]] then rfl, intro hq ; explicit_rw [hb at [0,1] with [exact hq]] then rfl, intro hq ; rfl], eq_self at []]` | **exit 0** |
| 5 | `congr` | `congr_cast.json` | `explicit_rw [congr 3 [hfa at []] at [0,1], eq_self at []]` | **exit 0** |

Files: `/private/tmp/t1r7/T2rep.lean` (1, 2), `T2rep2.lean` (3), `T2rep4.lean` (4),
`T2rep5.lean` (5).

**REVIEW-6 4 is closed on both sides.** The `dreduce_ite` step is now a `change`, and T2 accepts
it at the dependent-`∀` domain that it refused as an `eq` last round. No responsibility remains
split on that item.

**One T1-side note on the side-trace shape.** For case 4 the recorded side goal is `p = q` with
`pre: "p"`, `post: "q"`, but the goal T2 presents at that point is `p = ?c` — the congruence
theorem's RHS is still a metavariable. The trace's `steps` rewrite the LHS and the replay must
supply `then rfl` to close it, which the trace does not record (`close: null`). This is the
round-6 open question ("should a side trace carry `pre`/`post`") answered affirmatively and
implemented, yet `close: null` still leaves the finisher to the replayer's judgement — I supplied
`then rfl` by inspection for all three side traces. Not a defect against the current spec;
flagged because it is the one place where the two sides still each decide independently.

**No T2-side gaps.** Every kind in the current T1 set has a T2 form, and nothing in the five
traces was inexpressible.

---

## Checks

Standard gates, all re-run from scratch this round:

- **Scratch build.** Oleans, ilean, trace and hash files deleted, then
  `lake build ExplicitLean.SimpTrace`: **clean, no warnings, exit 0, 9.23 s, 749 MB**
  (RESULT.md says 9.71 s / 750 MB — consistent).
- **`test/SimpTrace/Fixtures.lean`: exit 0**, no errors.
- **`test/SimpTrace/UnresolvedFixtures.lean`: exit 1 by design**, with **4** classified lines
  (listed in defect 6), plus one unclassified kernel type mismatch at `:100`. RESULT.md says 2 —
  defect 6.
- **`python3 -B Experiment/check_simp_trace.py`: `OK: 59 …`, exit 0**, 15.33 s, 1523 MB.
  Matches RESULT.md:174.
- **`--report` reproduces RESULT.md:45-50 exactly**, and genuinely so: I deleted `meas_out/` and
  `isempty_out/`, re-ran all five measurement modules (each exit 0, zero `unresolved` lines,
  2.13–2.96 s, 668–746 MB — matching the RESULT.md table), and re-ran `--report`; the output is
  byte-identical to the pre-deletion run. 46 calls, 229 steps, 44622 bytes.
- **Scope.** `git diff --name-only $(git merge-base codex/search-free-mathlib-2026-08-31
  task/T1-trace-capture) task/T1-trace-capture` lists 84 files, **every one** under
  `ExplicitLean/SimpTrace/`, `ExplicitLean/SimpTrace.lean`, `test/SimpTrace/`,
  `Experiment/check_simp_trace.py` or `tracking/tasks/T1-trace-capture/`. `ExplicitLean.lean`,
  `lakefile.toml` and `tracking/SIMP-TRACE-SPEC.md` are **not** in the list.
- **No tracked scratch.** `git ls-files | grep -E 'out/|scratch'` empty; working tree clean.
- **RESULT.md honesty.** Exactly one "Checks" paragraph. Build time, `OK: 59`, the measurement
  table and the five module figures all reproduce. Two claims do not: the classified-line count
  (defect 6) and "the check added no false positives" (defect 2).

---

**Totals: 4 critical, 2 major, 2 minor; 0 T2-side gaps.**

Defects 1, 2, 3 and 5 share one shape and it is the shape the round-6 work was supposed to
retire: **the recorder names something it did not capture, and the new check does not cover the
place where it happens.** The check validates `rw` steps whose origin resolved — it is silent on
unresolved origins (defect 1), silent on side closes (defect 3), wrong about one real lemma
(defect 2), and blind to a wrapper walk that reaches the wrong local (defect 5). RESULT.md calls
it "the correctness backbone"; on this corpus it passes every step it cannot see and rejects one
it should accept.

Defect 4 is the round's hardest finding: **4 of 43 real `Logic/Basic` call sites that stock simp
proves neither trace nor classify** — they crash. No goal-state divergence from stock was found
across 25 differential goals, and all five T2 integration shapes replay clean.
