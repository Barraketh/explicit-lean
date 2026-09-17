# T2-explicit-rw — adversarial review, round 5

Fresh eyes. Every command re-run in the task worktree; `RESULT.md` read but not
trusted, all counts recomputed. Scratch under `/private/tmp/t2r5`.

## Round 4 defects: 4/4 re-checked

| # | Round-4 title | Status |
| - | ------------- | ------ |
| 1 | T1's `eq` `lhs` `if _ then _ else _` unparseable | **fixed** — `/private/tmp/t2r5/r4/d1.lean` compiles silently, `guard_target` holds |
| 2 | `.field` on a parenthesised term rejected (`(hp q).elim`) | **fixed** — `/private/tmp/t2r5/r4/d2.lean` silent; the misleading "invalid 'by' tactic" message is gone |
| 3 | `Type`/`Prop`/`Type*`/`Sort*` not admitted | **parses now, but elaborates wrongly — see defect 1** |
| 4 | spec drift: `iota`, `prop`, `omega` unimplemented | **fixed** — `iota` step implemented, `with [...]` clause added, `eq_true`/`eq_false` fixtures at `Lemmas.lean:187,192` |

## Task 2 — escape surface, re-attacked against the widened grammar

650 probes = 130 terms x 5 slots (`exact` closer, lemma term, `change` target,
`eq` equation, **`with [exact …]`** — a slot round 4 did not exist).
Generator `/private/tmp/t2r5/gen.py`, runner `/private/tmp/t2r5/run2.py`,
results `/private/tmp/t2r5/results.tsv`.

**385 escape probes (77 distinct terms), 385 rejected at parse time, 0 escapes.**
Every earlier probe re-run (`by`, `fun x => by`, `match`, `let`, `do`, `show …
from`, `‹›`, `⟨⟩`, `$`, `<|`, `·`, `?m`, named args, `(config := …)`, `▸`,
`open … in`, `nomatch`, `nofun`, `[1,2]`, `s!""`, `@[simp]`, `sorry`), plus the
ones the widening newly enables, all parse errors in all five slots:
`if h : c then (by simp) else _`, `∀ x, by simp`, `∃ x, by simp`, `{x | by simp}`,
`(by simp) + 1`, `↑(by simp)`, `(by simp)⁻¹`, `(by simp) ^ 2`, `-(by simp)`,
`¬(by simp)`, `((by simp), 1)`, `(1, (by simp))`, `((by simp) : Nat)`,
`(x : (by simp))`, `((by simp).1)`, `id (by simp)`.

Specifically asked about, all **rejected** (correct): `fun ⟨a, b⟩ => a` pattern
lambda, `fun | 0 => 1 | _ => 2`, `∀ ⦃x⦄, p x` strict-implicit, `∀ {x}` /
`∀ [x]`, binder predicates `∀ x ∈ s, p x` and `∃ x ∈ s, p x`, `Σ x, β x`,
`∑ i in s, f i` and `∑ i, f i`, `‖x‖`, `⌊x⌋`, `|x|`, `f ⁻¹' s`, `s ×ˢ t`,
`{x : Nat // x > 0}`, `1.5e3` scientific, `'a'` char, `` `(1) `` quotation,
`have`/`haveI`/`suffices`/`unsafe`/`if let`. Allowed and correct:
`fun x => x.1`, `fun (x : α) => x`, `x ∣ y`, `x ^ 2`, `2⁻¹`, `-1`, `(2 : Nat)`.

Big operators (`∑`) are **not** whitelisted. That is the right call: `∑ i in s,`
is a binder notation whose body would need the binder machinery, and the spec's
`lhs`/`rhs` are debug strings a generator may re-render. RESULT.md already
records it as a dialect exclusion. No action.

**`with [...]` is a genuinely closed set** and `omega` is the real `omega`.
Verified by hijack, not by inspection: `macro "omega" : tactic => `(tactic| fail
…)` in the user's file makes a plain `by omega` fail (control:
`/private/tmp/t2r5/with/omega_ctl.lean` errors "hijacked omega ran"), yet
`with [omega]` still succeeds (`/private/tmp/t2r5/with/omega_shadow2.lean`
silent). Same result for `then rfl`, `then decide` and `eq … by decide` under
hijacked `rfl`/`decide`. The quotations are elaborated inside
`ExplicitRw.Tactic` and are hygienic, so user redefinition is possible but
**cannot** reach the closed set. No defect.

---

# Defects

## 1. `Type`, `Type*` and `Sort*` elaborate to `Sort _`, not to the sort written (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:434` and `:436`.

Both lines read `stx[0].getAtomVal`, but the productions are alternations
(`("Type" <|> "Sort")`, `("Type*" <|> "Sort*")`), which wrap the atom one node
deeper. Every other alternation in the file correctly uses `stx[0][0]`
(`:710`, `:870`, `:1014`). So `getAtomVal` returns `""`, `isType` is always
`false`, and the `Type` branch is dead: bare `Type` becomes `` `(Sort _) ``,
and `Type*`/`Sort*` both become `` `(Sort _) `` as well.

`Sort _` is an *unconstrained universe metavariable*, so it unifies with
anything — including `Prop` (`Sort 0`), which `Type` must never equal.

**Input / observed:**

```lean
-- the binder type at [0,0] is `Prop`; `change Type` must be refused
example : (fun (_α : Prop) => True) True := by
  explicit_rw [change (Type) at [0, 0]] then exact trivial
```
observed: **compiles silently** (accepted).
expected: refused, as the control `change (Type 1)` correctly is
(`/private/tmp/t2r5/r4/ct3.lean` errors), while `change (Sort 0)` is correctly
accepted (`/private/tmp/t2r5/r4/ct4.lean` silent).

Directly visible in an `eq` slot: `eq (Type = Type) by rfl` reports its own term
back as `` `eq (Sort _ = Sort _)` `` and `eq (Type* = Nat)` reports
``Expected Prop``.
**Commands:** `lake env lean /private/tmp/t2r5/r4/ct2.lean` (silent, wrong);
`/private/tmp/t2r5/r4/ct3.lean`, `/private/tmp/t2r5/r4/sort2.lean`,
`/private/tmp/t2r5/r4/sortstar.lean`.

**Not a soundness hole** — the kernel still checks the proof term, and
`#print axioms` on a theorem built this way is clean
(`/private/tmp/t2r5/sort_soundness.lean`). It is a **fidelity** defect: replay
silently accepts a recorded `change`/`eq` term at a position whose sort differs
from the one written, which is exactly what `change` exists to pin down. Fix is
one character in each of the two lines: `stx[0]` → `stx[0][0]`.

## 2. The two fixtures that claim to cover sorts cover no sort (MAJOR, same root)

**File:** `test/ExplicitRw/Grammar.lean:129-138`.

This is why defect 1 survived round 4. `theorem sort_spellings (α β : Type)`
contains no sort spelling in any `explicit_rw` step — it rewrites `α × Nat` with
a hypothesis. `theorem sort_ascriptions`, whose docstring reads "`Type`, `Prop`,
`Type*` and `Sort*` parse in an ascription", actually writes
`change ((a : Nat) + 0)`. Neither theorem would fail if the whole sort branch
were deleted.

**Expected:** a fixture that pins what each sort spelling *elaborates to*, e.g.
asserting `change (Type)` is **refused** at a `Prop` position and accepted at a
`Type` one. Without that the grammar's sort productions are untested.
**Command:** `grep -n "sort_spellings" -A 10 test/ExplicitRw/Grammar.lean`

## 3. `iota` reduces more than one step (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:892-902` — the handler calls
`whnfCore sub`, which iterates to weak-head normal form rather than performing a
single iota contraction.

`tracking/SIMP-TRACE-SPEC.md` is explicit: "`iota` = matcher/recursor
application to a constructor, **reduced one step**".

**Input / observed:**

```lean
theorem iota_steps :
    Nat.rec (motive := fun _ => Nat) 0
      (fun _ ih => Nat.rec (motive := fun _ => Nat) 5 (fun _ _ => 6) ih) 1 = 5 := by
  explicit_rw [iota at [0, 1]]
  trace_state   -- ⊢ 5 = 5
```
observed: `⊢ 5 = 5` — the outer *and* the inner recursor were both reduced.
expected after one step: `Nat.rec 5 (fun _ _ => 6) (Nat.rec 0 … 0) = 5`, i.e. a
term that still contains a redex.
**Command:** `lake env lean /private/tmp/t2r5/iota_multi.lean`

Consequence: a trace that records N successive `iota` steps replays only if the
first one did not already consume the later ones; step N+1 then fails with
"not a matcher or recursor application" at a position the recorder considered
valid. The guards themselves are right — non-constructor scrutinee and
non-matcher head are both refused with good messages
(`/private/tmp/t2r5/iota_var.lean`, `/private/tmp/t2r5/iota_nonmatch.lean`) —
only the step count is wrong. Either bound the reduction to one contraction, or
raise to the coordinator to relax the spec's "one step" to "to weak-head normal
form".

## 4. Mathlib's numeric type notations `ℕ ℤ ℚ ℝ ℂ` are unparseable (MAJOR)

**File:** `Tactic.lean:139-150` (atoms) — the whitelist admits `ident`, but
`ℕ`/`ℤ`/`ℚ`/`ℝ`/`ℂ` are declared in Mathlib as *notation tokens*, not
identifiers, so the lexer stops before the category ever sees them.

**Input / observed:**

```
explicit_rw [eq (ℝ = ℝ) by rfl at [...]]
  error: unexpected token 'ℝ'; expected explicitRwTerm
```
Same for `ℕ ℤ ℚ ℂ`. Greek identifiers (`α`) are fine — they lex as `ident` — and
`Nat`/`Real` work, so only the notation spellings are affected.
**Expected:** parses, because this is exactly how Lean pretty-prints those types:
`(2 : ℝ)` is the ordinary output form, and it is refused in all five slots.
**Command:** `lake env lean /private/tmp/t2r5/uni.lean` (and `uni3.lean`)

This is the same class as round-4 defects 1-3 and the last substantial one: of
265 benign probes, exactly 10 were parse-rejected, and all 10 are this
(`(2 : ℝ)` and `(2 : ℝ)⁻¹` x 5 slots). RESULT.md claims round 4 widened the
grammar to "what Lean's pretty printer emits, so ordinary output passes through";
that is not yet true for the most common types in Mathlib. Either add these
tokens as atoms, or narrow the claim in RESULT.md.

## 5. Spec drift again: the `nofun` close form is unrepresentable (MINOR, coordinator item)

`tracking/SIMP-TRACE-SPEC.md:18-22` was amended (after round 4) to add
`"nofun"` to `close.by`, for `reduceCtorEq`-style side conditions. The closer
enumeration does not offer it and the grammar does not admit the term:

```
explicit_rw [...] then exact nofun
  error: unexpected token 'nofun'; expected explicitRwTerm
```

`grep -n nofun ExplicitLean/ExplicitRw/Tactic.lean` → no match.
**Command:** `lake env lean /private/tmp/t2r5/nofun.lean`

As in round 4, the spec moved under the task; this is a **coordinator decision**,
not an implementer defect. It must not be merged as spec-complete.

---

## Task 3 — semantics of the new kinds

- **`iota` refusals: correct.** Non-constructor scrutinee → "the application does
  not reduce; its major premise is not a constructor". Non-matcher head → "the
  subterm is not a matcher or recursor application; its head is `@HAdd.hAdd`".
  Step count is wrong (defect 3).
- **Positions after `iota`: correct.** A following step addresses the reduced
  term (`/private/tmp/t2r5/iota_pos.lean`, two `guard_target`s, silent).
- **`with [...]` supplies hypotheses in order: correct and positional.** With a
  two-hypothesis lemma, `with [exact h1, exact h2]` succeeds and the swapped
  `with [exact h2, exact h1]` fails with a type mismatch naming `a = 1`
  (`/private/tmp/t2r5/with/order.lean`, `order2.lean`).
- **Count mismatch errors both ways.** Too many → "supplies 2 proof(s) but lemma
  … has 1 undetermined hypothesis(es)". Too few (`with []` or no clause) →
  "still has an unassigned argument of type 5 ≤ n … never searches for it".
- **`eq_true`/`eq_false` fixtures are real** (`Lemmas.lean:187,192`): each pins
  the rewritten goal with `guard_target =ₛ`, so the `prop` flag's rendering is
  genuinely covered.

## Task 4 — standard checks (all pass)

- **Scratch build**: `ExplicitRw*` artefacts removed, `lake build
  ExplicitLean.ExplicitRw`: PASS, no warnings, **4.8 s**.
- **`check_explicit_rw.py`**: PASS (**6** fixtures + **13** rejected-syntax),
  **44.5 s**.
- **`check_no_simp_family.py`**: PASS (3 files), **0.04 s**. Negative control
  run: injecting `open Lean.Meta.Simp in` + `simpTarget` into `Basic.lean` is
  caught as 2 violations, so the lint is not vacuous. Tree restored.
- **`expected.json` perturbation**: `exact_elab_metam.lean` fragment set to
  `THIS FRAGMENT CANNOT MATCH` → `FAIL (wrong reason)` /
  `check_explicit_rw: FAIL (1 of 19 fixture(s))`. Restored; `git status` clean.
- **`#print axioms` on all 89 theorems** of the five positive fixtures
  (`/private/tmp/t2r5/ax/`): **no `sorryAx`**, no errors. 59 axiom-free,
  30 with axioms (15 `propext` only, 14 `Quot.sound` only, 1 both) — matches
  RESULT.md exactly. **No fixture uses `Classical.choice`**, so the question of
  whether a conv equivalent would need it does not arise for any of them.
- **Scope**: `git diff --name-only 6eaed503 HEAD` touches only owned files —
  the two scripts, `ExplicitRw{.lean,/Basic,/Tactic}`, `test/ExplicitRw/**`,
  `tracking/tasks/T2-explicit-rw/**`. `ExplicitLean.lean` and `lakefile.toml`
  untouched. Working tree clean.

## Task 5 — RESULT.md honesty

**Largely accurate; one claim overstated.**

- "Two earlier sweep runs were discarded … one ran against a mid-edit build, the
  other graded *any* error as rejection, hiding that benign terms were failing to
  elaborate rather than to parse" — this is an honest and unusually specific
  self-report, and the described failure mode is real: my own runner needed the
  same PARSE-vs-ELAB discrimination, and I verified mine on known cases (an
  escape gives PARSE, a benign-but-mismatched lemma gives ELAB). **No sweep
  artefacts are committed** (correctly — they are scratch); the durable artefact
  is `test/ExplicitRw/Grammar.lean`'s 19 theorems, and those *do* correspond to
  the widened grammar. But see **defect 2**: two of those 19 do not test what
  they say they test, so the committed regression surface is thinner than the
  third run was.
- "all 76 benign spellings now parse" — **overstated**. `(2 : ℝ)` does not
  (defect 4). My 53 distinct benign terms include two that fail; whether the
  implementer's 54-term list contained a `ℝ` spelling I cannot tell, but the
  RESULT.md sentence "the grammar now covers pretty-printer output" is not yet
  true for `ℕ ℤ ℚ ℝ ℂ`.
- Counts re-verified and **correct**: 89 theorems / 59 axiom-free / 14 / 15 / 1;
  6 fixtures + 13 rejected-syntax; build and check runtimes within noise of the
  stated figures. 90 lines, over COORDINATION.md's 60-line budget (rounds 1-4
  recorded there; a coordinator waiver is assumed, as in round 4).
- The conditional guarantee at `RESULT.md:6-8` and `Tactic.lean:88-96` remains
  **true and correctly scoped**; the `@[term_elab]` residual hole is still stated
  rather than papered over, and round 5's 385 escape probes found nothing that
  weakens it.

---

## Summary

| # | Severity | Short title |
| - | -------- | ----------- |
| 1 | major | `Type`/`Type*`/`Sort*` elaborate to `Sort _`; `stx[0]` should be `stx[0][0]` |
| 2 | major | `sort_spellings`/`sort_ascriptions` fixtures test no sort — why defect 1 survived |
| 3 | major | `iota` uses `whnfCore` and reduces many steps; spec says exactly one |
| 4 | major | `ℕ ℤ ℚ ℝ ℂ` unparseable — the commonest pp spelling for types |
| 5 | minor | spec drift: `nofun` close form unimplemented (coordinator item) |

0 critical, 4 major, 1 minor. **No safety defect this round.** The whitelist held
against all 385 escape probes across 77 constructs and five slots, including the
`with` slot the widening newly introduced; `with`/`then`/`eq … by` are genuinely
closed and hygienic against user redefinition of `omega`, `rfl` and `decide`
(proved by hijack with a working control, not by reading the source). All
required checks pass from scratch, scope is clean, no `sorryAx` and no
`Classical.choice` in any of the 89 fixture theorems.

Defect 1 is a one-character-per-line fix but it silently defeats the point of
`change` at sort positions, and defect 2 explains why no test caught it — those
two should be fixed together. Defects 3 and 4 are fidelity gaps between what the
recorder emits and what replay accepts, of the same kind round 4 addressed.
