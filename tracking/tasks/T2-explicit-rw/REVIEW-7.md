# T2-explicit-rw — adversarial review, round 7

Fresh eyes. Every command re-run in the task worktree; `RESULT.md` read but not
trusted, all counts recomputed. Lean compiles run serially (lake build lock).
Scratch under `/private/tmp/t2r7`. No product file edited; working tree clean
after every perturbation (`git status --porcelain` empty each time).

## Round 6 defects: 6/6 re-checked, all fixed

| # | Round-6 title | Status |
| - | ------------- | ------ |
| 1 | *(critical)* `eq` slot admits a FALSE theorem with `sorryAx`, exit 0 | **fixed** — `/private/tmp/t2r7/r6/CRITICAL.lean` now gives `error: explicit_rw: step 1: Unknown identifier 'unknownIdent'` and **exit 1**. (`#print axioms false_thm` still names `sorryAx`, which is the correct downstream consequence of a failed proof, not an admission: the error is emitted and the exit is non-zero.) |
| 2 | discriminating sort fixture absent; 0 `#guard_msgs` | **fixed** — `test/ExplicitRw/Strict.lean:65-85` pins the refusal of `change (Type)` at a `Prop` position with `#guard_msgs`; `Strict.lean` has **8** `#guard_msgs`, `Negative.lean` 21. Reproduced live (`r6/d2_sort.lean`, exit 1) |
| 3 | `ℝ`/`ℂ` atoms unresolvable (prelude-module hygiene) | **fixed** — `r6/d3_real.lean` (imports Mathlib): `change ((a : ℝ))`, `change ((a : ℂ))`, `change ((2 : ℝ) + 0)` and `add_zero (2:ℝ)` all elaborate; `k4`/`k7` axiom-clean, exit 0 |
| 4 | `ℝ`/`ℂ` only in statements, never in a step | **fixed** — `Grammar.lean:182-197`: `numeric_real`, `numeric_ascription`, `numeric_complex` now put the token **inside** the step |
| 5 | `$x` gives "internal error" / misattributed keyword message | **fixed in the step slot** — `r6/d5_anti.lean` → `explicit_rw: antiquotations are not admitted in a trace step.` **Not fixed in the new recursive slots — see defect 1** |
| 6 | `change` error promises an unprinted underlying error | **fixed** — `r6/d6_change.lean` prints exactly `step 1: Unknown identifier 'nope'`, no dangling promise |

**`congr` addendum (task 1): all three replay.** `congr_cast`,
`congr_nested_cast` and the `Function/Basic:390` shape (`congr_function_basic`)
are committed at `test/ExplicitRw/Definitional.lean:245-262` and
`Definitional.lean` passes silently.

---

# Defects

## 1. The round-6 antiquotation fix was not applied to the new recursive side-proof slots (MINOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:1319` (side-proof dispatch) and
`:1211` (step-kind fallthrough). The fix exists only at `:634` and `:1085`.

Round 6's defect 5 was "`internal error` is the wrong category for user input".
It was fixed for the term and step slots, but the side-proof grammar added in the
same round re-introduces it in four of the six slots I swept.

**Input** (`/private/tmp/t2r7/side/anti_side.lean`):
```lean
example (c : Prop) [Decidable c] (x y u : Nat) (hxu : x = u) :
    (if c then x else y) = (if c then u else y) := by
  explicit_rw [ite_congr at [0, 1] with [rfl, $x, intro h ; rfl]] then rfl
```
**Observed:**
```
error: explicit_rw: internal error: unknown side proof `ExplicitLean.ExplicitRw.explicitRwSideTac.antiquot`
```
and in the `congr` nested-step slot, `internal error: unexpected step kind `«$»``.

**Expected:** the same plain message the step slot now gives —
`antiquotations are not admitted in a trace step.`

**Not a safety defect:** every slot rejects it (exit 1, nothing admitted); this is
a diagnostic-category defect, identical in kind to the one round 6 raised.
**Command:** `lake env lean /private/tmp/t2r7/side/anti_side.lean`

## 2. The `congr` soundness refusal prints two identical terms (MINOR)

**File:** `Tactic.lean:1142-1143`.

The `isDefEq pfTy expected` guard at `:1141` is **sound and load-bearing** — it is
what stops an unsound `congr` (see the attack log below). But when the step
changes an argument the congruence theorem treats as `.fixed`/`.cast`, the two
sides differ only in *implicit* arguments, so the error prints them identically.

**Input** (`/private/tmp/t2r7/congr/c15.lean`): with `hAB : A = B`, `hAC : A = C`,
`explicit_rw [congr 0 [hAC at []] at [0,1]]` on `cast hAB x = cast hAB x`.
**Observed:**
```
error: explicit_rw: step 1: `congr 0`: the congruence theorem proves
  cast hAB x = cast hAB x
but this step needs
  cast hAB x = cast hAB x
```
Under `set_option pp.explicit true` the terms are visibly different
(`@cast A B hAB x` vs `@cast C B hAB x`, `/private/tmp/t2r7/congr/c15b.lean`), so
the refusal is correct and only the message is unusable.
**Expected:** render this message with `pp.explicit`/`pp.all` set, as the
mismatch is by construction in the implicit arguments.
**Command:** `lake env lean /private/tmp/t2r7/congr/c15.lean`

## 3. RESULT.md: the escape-sweep figures have no committed artefact (MINOR, honesty)

**File:** `tracking/tasks/T2-explicit-rw/RESULT.md:44-48`.

"324 probes … 210/210 escapes parse-rejected … 114/114 benign terms parse" and
the discarded 24-case classifier run are **not backed by any committed artefact**:
`git ls-files | grep -iE 'sweep|escape|probe'` returns only pre-existing,
unrelated `Experiment/*FoldProbe.lean` files. The task asks that every numeric
claim be backed by a committed artefact; these four numbers cannot be checked by
the next reviewer, and the *discarded* run is exactly the case where an artefact
matters most. On the substance the claim holds — my own independent 270-probe
sweep (below) found 0 escapes — so this is a reproducibility, not a truth, defect.
**Expected:** commit the generator and the results JSON, or drop the counts.

## 4. RESULT.md: stale fixture count (TRIVIAL)

**File:** `RESULT.md:83` says `test/ExplicitRw/` holds "(6 fixtures + …)"; there
are **7** (`Strict.lean` was added in round 6). `RESULT.md:88-89` correctly says 7.
**Command:** `ls test/ExplicitRw/*.lean | wc -l` → 7.

---

## Task 2 — `elabStrict`, read and attacked

`Tactic.lean:764-792`. **Confirmed:** it runs the elaboration inside
`Term.withoutErrToSorry` (`:767`), forces synthetic metavariables without
postponing (`:771`), instantiates twice (`:772`, `:773`), rejects `e.hasSorry ||
e.hasSyntheticSorry` (`:778`), rejects `hasExprMVar` and `hasLevelMVar` unless
`allowMVars` (`:784-789`), and rejects when the message log gained errors
(`:780-782`). Every rejection is step-indexed via `stepError`.

**Routing confirmed complete.** `grep` for `elabTerm|elabType|elabTermEnsuringType|
Term.elab|mkFreshExprMVar|evalTactic|runTactic` over `Tactic.lean`/`Basic.lean`
finds exactly **four** elaboration sites, all `elabStrict`: the lemma term
(`:819`, the only `allowMVars := true`), `change` (`:1161`), `eq` (`:1182`) and
the side-proof `exact` (`:1298`). The remaining `elabTerm` hits are comments
(`:660`, `:662`); the remaining `evalTactic` hits are the *closed enumerations*
(`rfl`/`decide` at `:1194-1195`, side tactics at `:1281`, `:1309`), which take no
user term. The `allowMVars` caller closes its own mvars
(`closeLemmaMVars`, `checkNoLevelMVars:851`, `synthesizeInstanceMVars:873`).

Attacks, all in `/private/tmp/t2r7/strict/`:

| Attack | File | Result |
| ------ | ---- | ------ |
| term logging a **warning**, not an error (deprecation) | `a_warn4.lean` | **passes**, as it should: warning printed, `t_warn4` **axiom-free**, exit 0 |
| term that postpones (`?_`, `?m`) | `b_hole.lean` | parse-rejected: `unexpected token '?'; expected explicitRwTerm` |
| auto-bound implicit (`α` unbound) | `ab3.lean` | `step 1: Unknown identifier 'α'` — **not** auto-bound |
| `@` application, too many args | `ab4.lean` | `step 1: Function expected at Nat.add_zero n` |
| `@` application, no args (legitimate) | `ab5b.lean` | succeeds, `t_ab6` axiom-free — unification fixes it |
| `Type*` as an argument | `typestar.lean` | clean step-indexed type mismatch |
| `change (_)` — unassigned mvar | `d_underscore.lean` | `still contains an unassigned metavariable after elaboration: ?m.9` |
| **`errsBefore` bypass**: log an error earlier in the file so the message-log guard is skipped | `errsbefore.lean` | **no escape.** `withoutErrToSorry` makes the failure *throw*, so the log check is only a backstop; the false theorem is still refused, exit 1 |

I could not defeat it. The `errsBefore` short-circuit at `:780` is the one branch
I consider fragile by construction — it disables the log check for the rest of a
file once any error is logged — but it is unreachable as a soundness hole while
`withoutErrToSorry` is in force, and the `hasSorry` check at `:778` catches the
residue independently.

## Task 3 — `congr` via `mkCongrSimp?`, attacked

**No soundness defect.** The guard that matters is `isDefEq pfTy expected`
(`:1141`): the built proof's type is checked against the claimed equation before
`Replacement.eq` is returned, so an unsound rebuild cannot reach the kernel.

| Attack | File | Result |
| ------ | ---- | ------ |
| head with no cast-dependent args (plain `f a`) | `congr/c1.lean` | works; `c_plain` axiom-free |
| argument index out of range (`congr 5`) | `congr/c1.lean` | `congr 5: the application at this position has only 1 argument(s).` |
| nested steps leave the argument unchanged (no-op) | `congr/c2.lean` | accepted, `mkEqRefl` path; `c_noop` axiom-free |
| **nested step makes the argument type-incorrect for dependents** | `congr/c6.lean` | **refused**, step-indexed: "the congruence theorem proves `myVec 2 k = myVec 2 k` but this step needs `myVec 2 k = myVec 3 k`". No kernel error, no ill-typed goal |
| same, on a real `cast` (`.fixed`/`.cast` arg genuinely changed) | `congr/c15.lean` | **refused** (message unreadable — defect 2) |
| `congr` under a binder | `congr/c3b.lean` | works; `c_binder2` (`Quot.sound` only) |
| head is a local function | `congr/c4.lean` | works; `c_localfn` axiom-free |
| head is a lambda (beta needed first) | `congr/c5.lean` | works, exit 0 |
| instance-implicit args between explicit ones (`a + 1`, arg 4 of `HAdd.hAdd`) | `congr/c7.lean` | works; `c_inst` axiom-free |
| nested `congr` inside `congr`, inner a no-op | `congr/c10.lean` | outer claim unmet → honest `rfl` failure, exit 1 |

`#print axioms` on every fixture: see task 6 — **111 theorems, 0 `sorryAx`**.

## Task 4 — recursive side proofs, attacked

`with [intro h; explicit_rw [...] then rfl]` replays for both `ite_congr` and
`dite_congr` (`test/ExplicitRw/Lemmas.lean:243-251`, both axiom-free).

| Attack | File | Result |
| ------ | ---- | ------ |
| `intro` of wrong arity (3 names, 1 binder) | `side/s1.lean` | `Tactic 'introN' failed: There are no additional binders …`, step-indexed |
| `intro` name shadowing an existing hypothesis | `side/s4.lean` | clean type mismatch: `hxu has type c but is expected to have type x = ?u` — the shadowed name resolves to the *introduced* one, which is correct scoping |
| **side proof leaving goals open** | `side/s2.lean` | **refused**: `the 'with' entry 2 left 1 goal(s) open on x = ?u` |
| `then` closer inside a nested side proof | `side/s6.lean` | works; `s_nestclose` axiom-free |
| nested `explicit_rw` at the side goal | `side/s6.lean`, `Lemmas.lean:255` | works |
| `omega` inside a nested side proof | `side/s5.lean` | fails **honestly** (`?u` undetermined by `ite_congr` at that point) — a property of the lemma, not a defect; `omega` is reachable and reports a real counterexample |

**Escape sweep on the new recursive slots: 270 probes, 0 escapes.**
44 escape constructs (`by simp`, `by simp_all`, `by simp only []`, `by dsimp`,
`by norm_num`, `by push_cast`, `by norm_cast`, `by field_simp`, `by simpa`,
`by simp_rw`, `by rfl`, `by trivial`, `by omega`, `by decide`, `by { simp }`,
`by first | simp | rfl`, `by repeat simp`, `by all_goals simp`, `fun x => by simp`,
`(by simp)`, `(by simp : True)`, bare `simp`/`simp_all`/`dsimp`/`norm_num`/
`push_cast`/`assumption`/`trivial`/`sorry`/`admit`, `by exact (by simp)`,
`id (by simp)`, `by apply And.intro <;> simp`, `show True by simp`, `(· + 1)`,
`by tauto`, `by aesop`, `by ring`, `by linarith`, `by exact?`, `by apply?`, `?m`,
`$x`) x 6 slots (`with` entry, `with` entry after `intro … ;`, `then` closer,
nested `explicit_rw`'s own `then`, chained `then`, `congr` nested-step list).

**264 parse-rejected, 6 tactic-rejected, 0 ADMITTED.** All 6 non-parse rejections
are `$x` (defect 1). **No `by` reached parse in any slot** — the critical
criterion is met. Generator `/private/tmp/t2r7/sweep/gen.py`, runner `run.py`,
results `res.json`.

## Task 5 — grammar after the `ℝ`/`ℂ` notation-node rebuild

- `(2 : ℝ)` **inside a step** in a Mathlib-importing file: works
  (`r6/d3_real.lean`, theorem `k7`, `change ((2 : ℝ) + 0)` then `add_zero (2:ℝ)`).
- `ℝ` in a `prelude`-style file (no Mathlib): **clear error, no crash** —
  `step 1: elaboration function for 'termℝ' has not been implemented`, exit 1
  (`r6/d3_prelude.lean`, and the same in the `eq` slot, `d3_prelude2.lean`). The
  trailing `failed to pretty print term` line is noise but harmless.

## Task 6 — standard checks

- **Scratch build**: `ExplicitRw*` artefacts removed, `lake build
  ExplicitLean.ExplicitRw`: **PASS, no warnings, 4.8 s**.
- **All 7 fixtures individually**: `lake env lean test/ExplicitRw/<each>.lean`
  → **all silent, exit 0** (Basic, Binders, Definitional, Grammar, Lemmas,
  Negative, Strict).
- **`check_explicit_rw.py`**: **PASS (7 fixtures, 13 rejected-syntax), 42.2 s**,
  including `axiom audit: 111 theorems, no sorryAx (75 axiom-free)`.
  RESULT.md's "111 theorems, no `sorryAx`" is **exactly reproduced**.
- **Axiom-audit gate verified to fail** (task 6's injection): appending
  `theorem injected_sorry_probe : (1:Nat) = 2 := by sorry` to `Basic.lean` →
  `check_explicit_rw: FAIL: sorryAx audit`, **exit 1**. A subtler injection with
  no `sorry` warning (`axiom sneaky_ax` + a theorem using it) is **also caught**,
  exit 1 — so the audit catches new axioms, not just the `sorry` warning. Both
  reverted; tree clean.
- **`check_no_simp_family.py`**: **PASS (3 files), 0.04 s**. Verified
  discriminating: `Lean.Meta.CongrTheorems` is **accepted** (it is imported at
  `Tactic.lean:12` and the check passes), and injecting
  `public meta import Lean.Meta.Tactic.Simp` → **FAIL**, `1 violation(s)`,
  exit 1. Reverted; tree clean.
- **`expected.json` perturbation**: `then_simp.lean` fragment set to
  `THIS FRAGMENT CANNOT MATCH` → `FAIL (wrong reason)` /
  `check_explicit_rw: FAIL (1 of 20 fixture(s))`, exit 1. Restored; tree clean.
- **Scope**: `git diff --name-only $(git merge-base HEAD
  codex/search-free-mathlib-2026-08-31) HEAD` (merge-base `6eaed50`) touches
  **only owned files**: the two scripts, `ExplicitRw{.lean,/Basic,/Tactic}`,
  `test/ExplicitRw/**`, `tracking/tasks/T2-explicit-rw/**`. `ExplicitLean.lean`
  and `lakefile.toml` untouched.
- **RESULT.md honesty**: the axiom figure (111/0), the check runtimes, the
  fixture pass list, the `congr` fixtures and the `ite_congr`/`dite_congr` side
  proofs are all reproduced exactly. Two claims are not artefact-backed
  (defect 3) and one count is stale (defect 4). **110 lines, over
  COORDINATION.md's 60-line budget** — as in rounds 1-6; a coordinator waiver is
  assumed but has still never been recorded.

---

## Integration

Read-only in `/Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture`
at tip `e488c9f`. Five committed traces from `test/SimpTrace/expected/`,
hand-translated and replayed in the T2 worktree
(`/private/tmp/t2r7/integ/`). **All five replay; 0 T2-side mismatches.**

| # | T1 trace | Feature required | T2 replay | Result |
| - | -------- | ---------------- | --------- | ------ |
| 1 | `local_named_prop_true.json` | `local` + `prop:"true"` | `explicit_rw [eq_true h at [0,1], and_self at []] then exact trivial` | **PASS** (`i1_prop.lean`) |
| 2 | `dreduce_ite.json` | `change` with `source:"dreduceIte"` | `explicit_rw [change (3) at [0,1]] then exact fun x => rfl` | **PASS** (`i5c.lean`) |
| 3 | `user_congr_ite.json` | user congr as `rw`, `source:"congr"`, side traces with `intros` | `explicit_rw [ite_congr at [0,1] with [exact hpq, intro hq ; exact hb hq, intro hq ; rfl]] then rfl` | **PASS** (`i4_usercongr.lean`) |
| 4 | `congr_cast.json` | `congr` kind, `arg:3`, nested steps | `explicit_rw [congr 3 [hfa at []] at [0,1]] then rfl` | **PASS** (`i2_congr.lean`) |
| 5 | `args_term.json` | `args: ["a","b"]` on an `rw` step | `explicit_rw [fixtureTagT_lem a b at []] then exact trivial` | **PASS** (`i3_args.lean`) |

The spec's `prop`, `local`, `intros`, `side`, `args`, `congr`/`arg` and
`change`/`source` all have a working T2 form, and the positions T1 records are
consumed verbatim — trace 2's `pos: [0,1]` lands on the `ite` under a `forallE`
binder type exactly as recorded (confirmed against the raw term with
`pp.all`).

**Two mismatches, both on the T1 side, neither blocking T2:**

1. **T1 emits no `to` field on `change` steps, which the spec requires** (MAJOR,
   T1). `SIMP-TRACE-SPEC.md` defines the kind as
   `{"kind":"change", "pos":…, "to":"<pp.all term>", …}`. Across
   `test/SimpTrace/expected/*.json` **6 `change` steps carry no `to` and 0 carry
   it** (`dreduce_ite.json`, `let_body_zeta_off.json` x3,
   `let_operand_zeta_off.json` x2). T2's `change t at [pos]` *requires* that
   term, so I had to recover it by inspecting the goal — a generator cannot.
   This is the one thing that would stop an automated T1→T2 pipeline today.
   **Responsible side: T1.**
2. **T1 locations omit `pre`/`post`** (MINOR, T1). The spec (amended after T1
   round 6) puts `pre`/`post` on every location; **59 of 61 locations** across
   the expected traces have neither. Side traces *do* carry them correctly
   (`user_congr_ite.json`). Replay does not depend on these — the spec calls
   them validation fields — so this blocks nothing, but it contradicts the
   amendment the spec records. **Responsible side: T1.**

No mismatch is attributable to T2: every feature the traces exercise replayed on
the first or second attempt, and the two second attempts (traces 2 and 5 in my
working order) were my own position/target errors, not tactic defects.

---

## Summary

| # | Severity | Short title |
| - | -------- | ----------- |
| 1 | minor | round-6's antiquotation fix not applied to the new recursive side-proof slots (`:1319`, `:1211`) |
| 2 | minor | `congr` soundness refusal prints two identical terms (implicit-only mismatch) |
| 3 | minor | RESULT.md's 324/210/114 sweep figures have no committed artefact |
| 4 | trivial | RESULT.md:83 says 6 fixtures; there are 7 |

**0 critical, 0 major, 3 minor, 1 trivial.**

All six round-6 defects — including the critical one that admitted a false
theorem — are genuinely fixed, and each fix is now pinned by a fixture rather
than asserted. The three consecutive rounds of "claimed-covered behaviour with no
fixture exercising it" that round 6 flagged as a *pattern* is broken this round:
`Strict.lean` pins one rejection per elaboration site, the sort refusal is pinned
with `#guard_msgs`, `ℝ`/`ℂ` appear inside steps, and the axiom audit moved from a
RESULT.md claim into the runner, where I verified it fails on both a `sorry` and
a new-axiom injection.

The two consolidations are the real improvements: **one** `elabStrict` that I
could not defeat in eight attacks, and the `isDefEq` check in `congr` that
refuses every unsound rebuild I could construct — including a dependent argument
made type-incorrect for its dependents — without ever reaching the kernel or
producing an ill-typed goal. 270 escape probes over the new recursive grammar
admitted nothing.

**No merge blocker on the T2 side.** Defects 1-4 are diagnostic and bookkeeping.
The merge gate's real finding is on the **T1** side: `change` steps carry no `to`
field, so `dreduce`/`change` traces cannot be mechanically translated today. I
would gate the *joint* merge on that, and let T2 merge on its own.
