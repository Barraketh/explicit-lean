# T2-explicit-rw — adversarial review, round 6

Fresh eyes. Every command re-run in the task worktree; `RESULT.md` read but not
trusted, all counts recomputed. Lean compiles run serially. Scratch under
`/private/tmp/t2r6`.

## Round 5 defects: 5/5 re-checked

| # | Round-5 title | Status |
| - | ------------- | ------ |
| 1 | `Type`/`Type*`/`Sort*` collapse to `Sort _` | **fixed** — `change (Type)` at a `Prop` position is now refused (`/private/tmp/t2r6/r5/d1a.lean`), `change (Sort 0)` and `change (Sort*)` still accepted there (`d1b`, `d1d`), `change (Type)` accepted at a `Type` position (`d1e`) |
| 2 | sort fixtures tested no sort | **partly fixed** — `Grammar.lean:139-160` now has 6 real sort fixtures, but the *discriminating* negative case RESULT.md claims is still absent — see **defect 2** |
| 3 | `iota` reduced many steps | **fixed** — `reduceRecMatcher?` does exactly one contraction; verified it leaves a redex (`/private/tmp/t2r6/iota/h.lean`), that dropping the second `iota` does not reach the goal (`iota/e.lean`), and that a variable scrutinee errors (`iota/g.lean`) |
| 4 | `ℕ ℤ ℚ ℝ ℂ` unparseable | **half fixed** — `ℕ ℤ ℚ` work; **`ℝ` and `ℂ` still fail**, now at elaboration instead of parsing — see **defect 3** |
| 5 | `nofun` close form unimplemented | **fixed** — `then nofun` and `with [... nofun]` both present and working (`/private/tmp/t2r6/r5/nofun2.lean` silent) |

**Instance-resolution addendum (T1 round-4 `add_zero` replay): fixed.** All four
addendum fixtures replay silently (`/private/tmp/t2r6/inst/i0.lean`): `add_zero`
at `ℕ`, `add_zero` under a binder via `beta`, `mul_one` on a `Monoid` variable,
`mul_comm` at `ℝ`.

---

# Defects

## 1. A trace can prove a FALSE theorem: the `eq` slot swallows elaboration failure and ships `sorryAx` with **no error** (CRITICAL)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:1024-1027`.

This is precisely the hole round 5 found at the `change` site, left unfixed at
the `eq` site. `change` was given a `hasSorry` guard (`:1009`); `eq` calls
`Term.elabType` with neither `Term.withoutErrToSorry` nor a `sorry` check. When
the equation fails to elaborate, `elabType` logs a *recoverable* error, returns a
`sorry`-typed expression, and the surrounding `by` block is then silently
abandoned: no error is emitted, the theorem is admitted, and `lake env lean`
**exits 0**.

**Input** (`/private/tmp/t2r6/CRITICAL.lean`, no Mathlib, no linter options):

```lean
import ExplicitLean.ExplicitRw
theorem false_thm : (1 : Nat) = 2 := by
  explicit_rw [eq (unknownIdent = (2:Nat)) by rfl at [0, 1]]
#print axioms false_thm
```

**Observed:**
```
warning: declaration uses `sorry`
'false_thm' depends on axioms: [sorryAx]
EXIT CODE: 0
```
**Expected:** a step-indexed error naming the unresolved identifier, as every
other slot gives (see the audit table below), and a non-zero exit.

**Command:** `lake env lean /private/tmp/t2r6/CRITICAL.lean`

Any tactic after the `explicit_rw` is never executed — the subsequent
`trace_state` prints nothing and a following `exact` never runs
(`/private/tmp/t2r6/r5/y2.lean`), so the trace author sees a silently
"successful" replay. This directly violates the governing rule's "No
`sorry`/`admit`, no new axioms" and "Unresolved calls stay visibly unresolved".

### Audit of every elaboration site (task 2)

A type-mismatched or unresolvable term at each of the six sites
(`/private/tmp/t2r6/audit/sites*.lean`, each with `#print axioms`):

| Site | Source | Guard present | Type-mismatched term |
| ---- | ------ | ------------- | -------------------- |
| lemma term | `:695-708` | `Term.withoutErrToSorry` | step-indexed error |
| explicit args on lemma | same path | same | step-indexed error |
| `change` target | `:1000-1013` | `hasSorry` check | step-indexed error |
| `with [exact …]` proof | `:760-764` | via `evalTactic`/`Tactic.run` | step-indexed error |
| `exact` closer | `:1116-1121` | via `elabTermEnsuringType` + logged error | error (not step-indexed, acceptable — no step) |
| **`eq` equation** | **`:1024-1027`** | **none** | **SILENT — accepted with `sorryAx`** |

Unassigned metavariables are handled: `checkNoLevelMVars` (`:733`) and
`closeLemmaMVars` (`Basic.lean:284`) cover the lemma path. Neither runs on the
`eq` path, which needs only the missing sorry/`withoutErrToSorry` guard.

**Fix:** wrap the `eq` elaboration in `Term.withoutErrToSorry`, or add the same
`hasSorry` check `change` already has, and re-check `eqType` for expression and
level metavariables.

## 2. RESULT.md claims a discriminating sort fixture that does not exist (MAJOR)

**File:** `tracking/tasks/T2-explicit-rw/RESULT.md:16-18`; `test/ExplicitRw/Grammar.lean:139-160`.

RESULT.md states: "The new fixtures include the **discriminating** case —
`change Type` at a `Prop` position must be *refused* — because with `Sort _`
every accepting case passes either way." That fixture is not committed. All six
sort fixtures in `Grammar.lean` are *accepting* cases; `Grammar.lean` contains
**zero** `#guard_msgs` (`grep -c guard_msgs test/ExplicitRw/Grammar.lean` → 0),
and `Negative.lean` has no sort case among its 21.

Every committed sort fixture still passes if the `Sort _` bug returns, because
`Sort _` unifies with `Type`, which is what all six assert. The bug is fixed in
the code (defect 1 of round 5 re-verified above) but **remains untested**, which
is the same failure mode round 5 recorded as its defect 2.

**Expected:** the refusal case, pinned with `#guard_msgs`, e.g. the round-5
reproducer `example : (fun (_α : Prop) => True) True := by explicit_rw [change
(Type) at [0, 0]] then exact trivial` asserting the error.
**Command:** `grep -c guard_msgs test/ExplicitRw/Grammar.lean`

## 3. `ℝ` and `ℂ` still unusable — the atoms map to names not in scope (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:445-446`.

Round-5 defect 4 was fixed for `ℕ ℤ ℚ` only. `Tactic.lean` is a `prelude`
module importing only `Lean.*`, so the hygienic quotations `` `(Real) `` and
`` `(Complex) `` resolve in *that* module's scope, where those constants do not
exist. `ℕ ℤ ℚ` work by accident: `Nat`, `Int` and `Rat` are Lean core.

**Input / observed** (`/private/tmp/t2r6/benign_key2.lean`, with `import Mathlib`):

```lean
theorem k4 (a b : Real) (h : a = b) : a = b := by
  explicit_rw [change ((a : ℝ)) at [0,1], h at [0,1]] ; rfl
```
```
error: explicit_rw: step 1: the `change` term of this step does not elaborate at
the type of the subterm
  ℝ
```
The same term with `Real` spelled as an identifier succeeds
(`/private/tmp/t2r6/r5/s2.lean`, silent), which isolates the cause to the atom
mapping, not to the position or the type.

Confirmed directly: `toTermCore` on `(x : ℝ)` yields `(x✝ : Real✝)` — the
inaccessible macro scope on `Real` is the hygiene marker
(`/private/tmp/t2r6/r5/t1.lean`). All five atoms compared side by side in
`/private/tmp/t2r6/r5/t3.lean`: `ℕ ℤ ℚ` silent, `ℝ ℂ` both error.

**Expected:** `(2 : ℝ)` elaborates, since it is the ordinary pretty-printed
spelling. **Fix:** emit the name unhygienically (e.g. `mkIdent ``Real`` with
`Syntax.mkStrLit`-style raw identifiers, or resolve through
`realizeGlobalConst` at elaboration time rather than quoting), so the name binds
at the *call site*, not in the prelude module.

**Command:** `lake env lean /private/tmp/t2r6/benign_key2.lean`

## 4. The `numeric_ascription` fixture does not test what its docstring claims (MAJOR, same root as defect 2)

**File:** `test/ExplicitRw/Grammar.lean:186-190`.

Its docstring reads "The ascription spelling `(2 : ℝ)` inside a lemma term", but
the step is `h at [0, 1, 0, 1]` — `(2 : ℝ)` appears only in the theorem
*statement*, never inside an `explicit_rw` step. `numeric_real` (`:181`) is the
same: `ℝ` is in the binder, not in a step. So no fixture exercises `ℝ` or `ℂ`
through the grammar, which is why defect 3 passes the suite.

`grep -n "ℝ\|ℂ" test/ExplicitRw/*.lean` shows every occurrence is in a statement
or a comment. `numeric_nat` and `numeric_int` (`:171`, `:176`) *do* put `ℕ`/`ℤ`
inside a `change`, which is why those two spellings are genuinely covered.

**Expected:** `change ((a : ℝ) + 0)` inside the step, matching the `ℕ`/`ℤ`
fixtures. That one-line change turns defect 3 into a test failure.
**Command:** `grep -n "ℝ\|ℂ" test/ExplicitRw/Grammar.lean`

## 5. Antiquotation `$x` reaches the elaborator and produces an internal error (MINOR)

**File:** `Tactic.lean:427` (`toTermCore`'s fallthrough) and `:963` (the
`explicitRwRed` keyword dispatch).

`$x` is admitted by the parser as `explicitRwTerm.pseudo.antiquot` — a node the
grammar's author did not enumerate — and is caught only by the internal-error
fallthrough:

```
explicit_rw: internal error: unhandled whitelisted node `explicitRwTerm.pseudo.antiquot`
```
and, in the lemma slot, by a *misattributed* message:
```
explicit_rw: internal error: unknown reduction keyword ``
```
which names the wrong step kind entirely (the step is a rewrite, not a
reduction). **Not a safety defect** — every slot rejects it, and the proof is not
admitted — but "internal error" is the wrong category for user input, and the
second message would send a trace author to the wrong place.
**Expected:** a parse-time rejection, or a plain step-indexed "antiquotations are
not admitted".
**Command:** `lake env lean /private/tmp/t2r6/esc.lean` (with `$x` in each slot)

## 6. The `change` error promises an underlying error that is never printed (MINOR)

**File:** `Tactic.lean:1010-1012`.

The message ends "(Lean reports the underlying error separately.)" but no second
diagnostic is emitted in any case I produced — `change (nope)`
(`/private/tmp/t2r6/r5/y3.lean`), `change ((a : ℝ))` (defect 3), `change (Type)`
at a `Prop` position (`d1a.lean`) all print exactly one message. The recoverable
error `elabTermEnsuringType` logged is discarded when `stepError` throws. A
trace author is told to look for information that does not exist; with `ℝ` this
actively misleads, since the real cause is a name that failed to resolve.
**Expected:** either surface the logged error or drop the sentence.

---

## Task 4 — grammar escape sweep, re-run against the widened grammar

**395 escape probes = 79 distinct constructs x 5 slots** (`exact` closer, lemma
term, `change` target, `eq` equation, `with [exact …]`), run serially.
Generator `/private/tmp/t2r6/sweep/gen3.py`, runner `run3.py`, results
`res_escape.json`.

**0 escapes. 355 rejected at parse time, 40 at elaboration, none admitted.**
The 40 non-parse rejections are 8 terms x 5 slots: `∑ i ∈ s, f i`, `∑ i, f i`,
`‖x‖`, `⌊x⌋`, `f ⁻¹' s`, `s ×ˢ t` (all genuine lexer rejections — "expected
token" / "missing end of character literal" — the classifier merely did not
match their wording), plus `$x` (defect 5) and `admit` (rejected as an unknown
identifier in every slot; in the `eq` slot it hits defect 1, which is where I
first saw that hole).

Re-tested and all still rejected in all five slots: `by simp`, `by simp_all`,
`by simp only []`, `by dsimp`, `by norm_num`, `by push_cast`, `by exact trivial`,
`by rfl`, `by trivial`, `by omega`, `by decide`, `by { simp }`,
`by first | simp | rfl`, `by repeat simp`, `by all_goals simp`, `fun x => by simp`,
`match`, `let`, `do`, `show … from`, `‹›`, `⟨⟩`, `(· + 1)`, `?m`,
`(config := …)`, `▸`, `nomatch`, `[1,2]`, `s!""`, `sorry`, `open … in`,
`@[simp]`, pattern lambdas, `fun | …`, strict-implicit and instance binders,
binder predicates, `Σ`, `{x // p x}`, `1.5e3`, `'a'`, `` `(1) ``, `have`,
`haveI`, `suffices`, `unsafe`, `if let`, and the parenthesised/operator-wrapped
`by simp` variants round 5 introduced.

The **benign** half of the sweep (375 probes) was still running at write-up time;
I spot-checked the terms that matter — the five numeric atoms in the `change`
slot, which is the slot that actually elaborates a term at a real type — and
found defect 3. The earlier round-5 count of "76 benign spellings parse" cannot
be confirmed or refuted from my partial run, but it is **wrong in substance** for
`ℝ`/`ℂ`: they parse and then fail to elaborate, which RESULT.md's "the grammar
now covers pretty-printer output (`ℕ ℤ ℚ ℝ ℂ` included)" does not describe.

## Task 3 — instance resolution, attacked

The unify-then-synthesize order (`runRwStep:806-814`, `synthesizeInstanceMVars`)
holds up under every attack I built. **No defect.**

- **Instance fixed only by unification with the RHS (`←` direction):**
  `← add_zero` on goal `n = n + 0` replays silently
  (`/private/tmp/t2r6/inst/i1.lean`).
- **Non-canonical but defeq instance:** `@instHAdd Nat myAdd` with
  `myAdd := ⟨Nat.add⟩` — `add_zero` succeeds, as it must (`inst/j2.lean`).
- **Non-canonical and NOT defeq:** `badAdd := ⟨fun a b => a * b⟩`. The rewrite
  correctly follows the *subterm's* instance, producing `n * 0` rather than
  silently rewriting along the canonical one (`inst/k1.lean`, goal
  `⊢ n * 0 = 0`), and the false goal `badAdd-add 3 0 = 3` is **refused** at the
  closer (`inst/k2.lean`). This was my main soundness probe; it is clean.
- **Two instance args, one an `outParam`:** `mul_one` at `ℕ` via `HMul`/`Mul`
  replays silently (`inst/i3.lean`).
- **`Decidable` in an `ite` rewritten by `ite_cond_eq_true`:** the step resolves
  the `Decidable` instance correctly; my two `with` proofs were themselves
  ill-typed and were rejected with an accurate type mismatch naming
  `(1 = 1) = True` (`inst/j1.lean`) — correct behaviour, my test's fault.
- **Level determined by the instance:** `mul_one` on `{α : Type*} [Monoid α]`
  replays silently (`inst/i4.lean`).

## Task 5 — `iota` single-step

**Correct.** `reduceRecMatcher?` performs exactly one contraction.

- Recursor: one `iota` leaves `((fun motive zero succ => zero) …)`, a beta-redex,
  rather than a normal form (`/private/tmp/t2r6/iota/h.lean`). The fixture's
  following `beta` is therefore load-bearing.
- Nested matchers need two steps: dropping the second leaves
  `match 1 with | 0 => 10 | n.succ => 20`, not `20` (`iota/e.lean`), so
  `iota_two_steps` (`Definitional.lean:227`) is a genuine discriminator.
- Non-reducible position errors: variable scrutinee → "the application does not
  reduce; its major premise is not a constructor" (`iota/g.lean`); non-matcher
  head → "the subterm is not a matcher or recursor application; its head is
  `@HAdd.hAdd`" (`iota/d.lean`).

## Task 6 — standard checks

- **Scratch build**: `ExplicitRw*` artefacts removed, `lake build
  ExplicitLean.ExplicitRw`: PASS, no warnings, **5.1 s**.
- **`check_explicit_rw.py`**: PASS (**6** fixtures + **13** rejected-syntax),
  **40.7 s**.
- **`check_no_simp_family.py`**: PASS (3 files), **0.04 s**.
- **`expected.json` perturbation**: `then_simp.lean` fragment set to
  `THIS FRAGMENT CANNOT MATCH` → `FAIL (wrong reason)` /
  `check_explicit_rw: FAIL (1 of 19 fixture(s))`. Restored; `git status` clean.
- **`#print axioms` on all fixtures** (`/private/tmp/t2r6/ax/`): **104**
  theorems, **0 `sorryAx`**, 0 errors. 69 axiom-free; 14 `Quot.sound` only,
  16 `propext` only, 2 `propext`+`Quot.sound`, 3 with `Classical.choice`
  (the `ℝ` ones). The harness would catch a `sorry` warning in a fixture — it
  requires empty output — but **no fixture exercises the `eq` elaboration-failure
  path**, which is why defect 1 survives a green suite.
- **Scope**: `git diff --name-only 6eaed503 HEAD` touches only owned files —
  the two scripts, `ExplicitRw{.lean,/Basic,/Tactic}`, `test/ExplicitRw/**`,
  `tracking/tasks/T2-explicit-rw/**`. `ExplicitLean.lean` and `lakefile.toml`
  untouched. Working tree clean.

## RESULT.md honesty

Mostly accurate; **three claims are not true as written**, and one is the
critical defect's cover.

- **"`#print axioms` on the 100 theorems … **no `sorryAx`** — 68 axiom-free"** —
  the *fixtures* are indeed clean, but my count is **104 / 69**, not 100 / 68.
  Minor drift, but it is presented as a re-run figure.
- **"The new fixtures include the **discriminating** case"** — false; defect 2.
- **"Rounds 4-5 widened the grammar to what the pretty printer emits (`ℕ ℤ ℚ ℝ ℂ`
  included)"** (`Limitations`) and the round-5 entry "`ℕ ℤ ℚ ℝ ℂ` … Added as
  atoms, **verified in all five slots**" — false for `ℝ` and `ℂ`; defect 3. The
  "verified in all five slots" claim cannot have been run against `ℝ`, since it
  fails immediately.
- The round-5 entry for defects 1+2 is otherwise an honest and specific
  self-report: it correctly identifies that fixing the index alone was
  insufficient and that `elabTermEnsuringType` hands back `sorryAx`. That
  diagnosis is right — and it is exactly why leaving the identical hole at the
  `eq` site (defect 1) is hard to excuse: the mechanism was understood and
  written down, then not applied to the neighbouring call.
- The conditional guarantee at `RESULT.md:6-8` and `Tactic.lean:88-96` remains
  **true and correctly scoped**, and round 6's 395 escape probes found nothing
  that weakens it. Defect 1 is not a grammar escape: it needs no forbidden
  tactic, only a term that fails to elaborate.
- **100 lines, over COORDINATION.md's 60-line budget** (as in rounds 1-5; a
  coordinator waiver is assumed but has never been recorded).

---

## Summary

| # | Severity | Short title |
| - | -------- | ----------- |
| 1 | **critical** | `eq` slot swallows elaboration failure: a FALSE theorem is admitted with `sorryAx`, no error, exit 0 |
| 2 | major | the discriminating sort fixture RESULT.md claims does not exist; `Grammar.lean` has 0 `#guard_msgs` |
| 3 | major | `ℝ`/`ℂ` atoms map to `Real`/`Complex`, not in the prelude module's scope — hygiene makes them unresolvable |
| 4 | major | `numeric_ascription`/`numeric_real` fixtures put `ℝ` only in the statement, never in a step — why defect 3 passes |
| 5 | minor | `$x` antiquotation reaches the elaborator; "internal error", and a misattributed "unknown reduction keyword" |
| 6 | minor | the `change` error promises an underlying error that is never printed |

**1 critical, 3 major, 2 minor.**

Defect 1 is a merge blocker. It admits `sorry` into a replayed proof with no
diagnostic, which the governing rule forbids outright ("No `sorry`/`admit`, no
new axioms … Unresolved calls stay visibly unresolved"), and it does so at exit
code 0, so no CI gate built on the current harness would see it. The fix is the
guard that already exists twelve lines above it.

Defects 3 and 4 are one bug and its missing test, as are defects 1's `eq` site
and the fixture gap behind it, and as were round 5's defects 1 and 2. That is
the third consecutive round in which a claimed-covered behaviour had no fixture
exercising it; the pattern, not the individual bug, is what I would raise to the
coordinator. Everything the fixtures *do* exercise is clean: 0 `sorryAx` across
104 theorems, 0 escapes across 395 probes, and instance resolution survives a
deliberate non-defeq-instance soundness attack.
