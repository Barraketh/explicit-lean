# T2-explicit-rw — adversarial review, round 3

Verified independently in the task worktree, re-running every command rather
than reading the diff or trusting `RESULT.md`.

## Round 2 defects: all 7 re-checked, 6 fixed, 1 fixed-with-a-caveat

Each re-run with REVIEW-2's own reproducing command
(`/private/tmp/t2r3/{lettwo,let1,cap,macro,zeta}.lean`):

| # | Round-2 title | Status |
| - | ------------- | ------ |
| 1 | `let`-body step performs an unrecorded zeta | **fixed** — `two_steps` now applies both steps and keeps the `let`: goal is `(let y := 7; b + (y + d)) = b + (7 + d)`. See caveat in defect 2 below. |
| 2 | `let`-body rewrite captures occurrences of the bound value | **fixed** — `capture` now yields `(let y := a; y + (b + a)) = a + (b + a)`; the standalone `a` is no longer captured. |
| 3 | macro expanding to `by simp` bypasses the guard | **fixed** — `macro "SM" : term => \`(by simp)` is now refused; proof term is `sorry`, not simp's. But see defect 1: a *term elaborator* still bypasses it. |
| 4 | no `zeta` step kind | **fixed** — `zeta at [...]` is a real kind; on a non-`let` it errors ``` `zeta` at this position: the subterm is not a `let`. ``` |
| 5 | `intro_ctx` unimplemented | **fixed as recorded** — fails by name with an honest "does not implement" message. |
| 6 | `assumption` closer searches | **fixed** — dropped from the enumeration; pinned by `RejectedSyntax/then_assumption.lean`. |
| 7 | `proj` T1/T2 cross-check | no change needed, confirmed. |

## REVIEW-1's critical item re-confirmed fixed

`/private/tmp/t2r3/smuggle.lean` — `then simp`, `then simp_all`,
`then (dsimp; simp)` and `eq (2 + 3 = 5) by (simp)` all fail in the **parser**
(`unexpected identifier; expected 'decide', 'exact' or 'rfl'` /
`expected 'decide' or 'rfl'`), exit 1. No simp-family tactic reaches elaboration
through the surface syntax.

## Checks re-run from scratch (all pass)

- Deleted every `ExplicitRw` olean/ilean/trace/ir, then
  `lake build ExplicitLean.ExplicitRw`: PASS, no warnings, **3.1 s**.
- `python3 -B Experiment/check_explicit_rw.py`: PASS (5 fixtures + 6
  rejected-syntax), **22.5 s**.
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), **0.04 s**.
- Runner negative control: setting `then_simp.lean`'s fragment in
  `expected.json` to `THIS FRAGMENT CANNOT MATCH` makes the runner report
  `FAIL (wrong reason)` / `rejected for the wrong reason`. `expected.json`
  restored; `git status` clean.
- `#print axioms` on **all 59** fixture theorems (namespace-qualified, appended
  to copies under `/private/tmp/t2r3/ax/`): **no `sorryAx`** — 39 axiom-free,
  8 `Quot.sound`, 11 `propext`, 1 both.
- Scope: `git diff --name-only d685ec7^ HEAD` (T2's own 15 commits) touches
  **only owned files** — the two check scripts, `ExplicitRw/{Basic,Tactic}.lean`,
  `test/ExplicitRw/**`, `tracking/tasks/T2-explicit-rw/**`. `ExplicitLean.lean`
  and `lakefile.toml` untouched by T2. Working tree clean.

## Task 3 — closing set: every spec close form is renderable

Fixtures written to `/private/tmp/t2r3/{closes,dec2}.lean`; all elaborate and
all are `sorryAx`-free.

| spec `close` | rendering | result |
| ------------ | --------- | ------ |
| `{"by":"rfl"}` | `then rfl` | axiom-free |
| `{"by":"decide"}` | `then decide` | axiom-free (`c_decide2`) |
| `{"by":"true_intro"}` | `then exact True.intro` | axiom-free |
| `{"by":"assumption:hb"}` | `then exact hb` | axiom-free |
| `{"by":"absurd:hp"}` | `explicit_rw [...] at hp` + `exact hp.elim` on the next line | axiom-free |

**No close form is unexpressible.** Dropping bare `assumption` costs nothing.
One caveat, already recorded as REVIEW-2 defect 6 and still true: `absurd:<hyp>`
cannot go through `then` because `then` is refused when the trace targets a
hypothesis (`Tactic.lean:610-612`). That asymmetry *is* now documented at
`Tactic.lean:65-66`, so it is closed. Note `decide` inherits Lean's own
"expected type must not contain free variables" restriction, so a generator must
emit `decide` only for closed goals — worth a line in `RESULT.md`, not a defect.

## Task 4 — `let` handling: `withLetDecl`/`mkLetFVars` holds

All in `/private/tmp/t2r3/{lettwo2,let3,zeta2,deplet,deplet2}.lean`:

- let value mentioning an **outer bound variable** (`let y := x + 1` under `∀ x`):
  correct, `let` preserved.
- **nested lets** (`let y := 1; let z := 2; a + y + z`): correct, both preserved.
- **let inside a lambda under a `∀`**: correct, `(fun z => let y := z; g y + y)`.
- **`zeta` then a rewrite at a position that only exists after zeta**
  (`zeta at [0,1]`, then two rewrites at `[0,1,0,1]` and `[0,1,1]`): succeeds,
  `zeta_then` is **axiom-free**.
- **dependent positions refused, not mis-rewritten**: let *value* → "rewrites the
  value of a `let`"; let *type* → "rewrites the type of a `let`"; a body whose
  type depends on the let variable (`(f k).val` with `f : ∀ k, Fin (k+1)`) →
  the dependent-function message. All step-indexed. No ill-typed term produced.
- `#print axioms` on every fixture above: no `sorryAx`.

## Task 5 — universes: correct

`/private/tmp/t2r3/{univ2,univ4}.lean`.

- A `Sort*` lemma at a position **under a `∀` binder** works at `Sort u`
  (`under_binder`) and at `Sort 0` (`under_binder_prop`); both `Quot.sound` only,
  no `sorryAx`.
- A lemma with **two universe params where only one is determined** by the
  subterm (`two_univ {α : Sort u} {β : Sort v}`, rewritten backwards so `β`/`v`
  stay open) gives a **clear step-indexed error**, not a default:
  ``explicit_rw: step 1: lemma `two_univ (α := Nat) (a := a)` still has an
  unassigned argument of type ?m.3 after matching at the given position.``
  `checkNoLevelMVars` (`Tactic.lean:303-312`) is the second net.

---

# Defects

## 1. A term elaborator running simp in `MetaM`/`TacticM` defeats both guard layers (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:199-216` (`checkNoPendingTactic`)
and `Tactic.lean:224-250` (`checkNoTacticBlock`), called from the `exact` closer
at `Tactic.lean:570,576`.

`RESULT.md:6-8` claims: "no trace in this syntax can introduce it … every term it
elaborates is refused if it elaborates a tactic block, however that block got
there", and `Tactic.lean:77-81` repeats it, naming "via a custom term elaborator"
explicitly. **That claim is false.** Both layers key on *syntax*: the walk needs a
`byTactic` node in the written-or-macro-expanded tree, and the semantic check
needs a pending synthetic metavariable whose `decl.stx` is a `by` block. A term
`elab` that builds the proof itself — opening a fresh mvar and calling simp on it
in `MetaM`, or calling `Lean.Elab.Tactic.run … (evalTactic …)` — registers **no**
synthetic metavariable and contributes **no** `by` syntax, so nothing is left for
either layer to see.

Two independent variants, both succeeding:

**A — `Lean.Meta.simpGoal` directly in `MetaM`** (`/private/tmp/t2r3/elab3.lean`):

```lean
elab "SM2" : term <= ty => do
  let ty ← instantiateMVars ty
  let g ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar ty
  let ctx ← Lean.Meta.Simp.mkContext (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← Lean.Meta.simpGoal g.mvarId! ctx
  if r.isNone then return (← instantiateMVars g) else throwError "no"

theorem attackA (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then exact SM2
```

**B — `Tactic.run` + `evalTactic simp`** (`/private/tmp/t2r3/elab4.lean`), which
is exactly the `Term.runTactic`-shaped attack the task asked for:

```lean
elab "SMT" : term <= ty => do
  let ty ← instantiateMVars ty
  let g ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar ty
  _ ← Lean.Elab.Tactic.run g.mvarId! (Lean.Elab.Tactic.evalTactic (← `(tactic| simp)))
  return (← instantiateMVars g)

theorem attackT (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then exact SMT
```

**Expected:** refused, as `then exact (by simp)` and the `macro` version are.
**Observed:** both compile with no error, and the proof term is simp's own:

```
theorem attackT : ∀ (a b : Nat), a = b → a + 0 = b :=
fun a b h => Eq.mpr (id (congrArg (fun x => x + 0 = b) h)) (of_eq_true (eq_self b))
```

`of_eq_true (eq_self b)` is produced only by simp. `#print axioms attackA` is
`[propext]` — no `sorryAx`, i.e. the smuggled proof is genuinely accepted.

**Reproduce:**

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t2r3/elab3.lean   # attack A: prints simp's proof term
lake env lean /private/tmp/t2r3/elab4.lean   # attack B: same
```

**This is not confined to a Lean-importing test file.** The same attack compiles
from an ordinary `import Mathlib.Logic.Basic` file with no extra imports
(`/private/tmp/t2r3/noimport.lean`, verified): a generated Mathlib file already
has the simp machinery on its import path, so the only thing standing between a
generated file and this bypass is that the generator does not emit `elab`.

**Severity rationale:** major, not critical. It is not reachable by any *trace*
the T1 recorder can emit — it requires the generated file to also contain a
hand-written term elaborator, which the translator does not produce. It is a
false claim in the module docs and `RESULT.md` more than a live hole. But the
whole point of the closed enumeration was that the product tactic's guarantee
should not rest on "the generator happens not to do that", so the claim must
either be defended or withdrawn. See the recommendation section.

## 2. `mkLetFVars` drops a `let` whose body does not mention the bound variable (MINOR)

**File:** `ExplicitLean/ExplicitRw/Basic.lean:236` (`mkLetFVars #[x] r.newExpr`).

The round-2 fix is correct for every case where the body mentions `y`. When it
does not, `mkLetFVars` elides the now-unused binder, so the `let` disappears
without a recorded `zeta` — the *residue* of round-2 defect 1, in a narrower case.

**Failing scenario / reproduce:**

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t2r3/let1b.lean
```

`cap2 (a : Nat) (h : a = 7) : (let y : Nat := 7; a + 1) = 8`, step
`h at [0, 1, 2, 0, 1]`: **expected** `(let y := 7; 7 + 1) = 8`; **observed**
`7 + 1 = 8`. (`cap3`, whose body uses `y`, correctly keeps the `let`.)

A recorder that emitted a second step at a path through the `let` would then hit
a stale position, exactly as in round 2. The window is narrow — simp itself
would usually zeta such a `let` — but the invariant the round-2 fix established
("the `let` is destroyed only by an explicit `zeta` step",
`Basic.lean:232-233`) does not actually hold as stated.

**Fix direction:** use `mkLetFVars (usedLetOnly := false) #[x] r.newExpr`, which
keeps the binder regardless. Add a fixture with a `let` whose body ignores the
bound variable and a `guard_target` requiring the `let` to survive.

## 3. `RESULT.md` overstates the guard and miscounts the fixtures (MINOR)

**File:** `tracking/tasks/T2-explicit-rw/RESULT.md:6-8, 20-24, 55-56`.

- **Lines 6-8** ("no trace in this syntax can introduce it … however that block
  got there") and **`Tactic.lean:77-81`** (same claim, naming "via a custom term
  elaborator") are **falsified by defect 1**. Round 2's own fix note (`RESULT.md:20-24`,
  "an `elab`-based smuggler was found and refused") is true only of an `elab`
  that calls `elabTerm` on a `by` block; an `elab` that never produces `by`
  syntax at all is not refused.
- **Line 55**: "`#print axioms` on all **58** fixture theorems … 38 axiom-free,
  8 `Quot.sound`, 11 `propext`, 1 both". The actual count is **59** theorems and
  **39** axiom-free (`Definitional.lean` 21, `Lemmas.lean` 18, `Binders.lean` 10,
  `Basic.lean` 9, `Negative.lean` 1). The `sorryAx`-free claim is correct.
- **`test/ExplicitRw/Negative.lean:225-229`** heads its section "A macro **or term
  elaborator** expanding to `by` is refused" but contains only a `macro` case.
  No fixture exercises a term elaborator at all, which is why defect 1 survived
  a round.
- **No positive `then exact` fixture exists** — `grep "then exact" test/` returns
  only the three negative cases. The closer that the spec's `true_intro`,
  `assumption:<name>` and `absurd:<hyp>` all route through is untested in the
  positive direction. My task-3 fixtures (above) show it works; it should be
  pinned.

**Reproduce:** `grep -rn "then exact" test/ExplicitRw/`;
`python3 -c "import re,pathlib; print(sum(len(re.findall(r'^(?:private\s+)?(?:theorem|lemma)\s+',f.read_text(),re.M)) for f in pathlib.Path('test/ExplicitRw').glob('*.lean')))"`

---

# Recommendation on exact-term guard

**Recommended: restrict the `exact` closer to an applicative grammar, and drop
the false universality claim.** Concretely, replace the free `term` in
`explicitRwCloser` (`Tactic.lean:141-142`) with a closed grammar admitting only:
an identifier (possibly dotted / `@`-prefixed), application of such to
arguments drawn from the same grammar, `_`, numeric/string literals, `.elim` and
other projection suffixes on an identifier, and parentheses. Nothing else — no
`by`, no `fun`, no `let`, no `match`, no `show ... from`, no `⟨⟩`, no `▸`, no
type ascription. The three spec forms all fit: `exact True.intro`,
`exact <name>`, `exact <hyp>.elim`.

Reasons to prefer it over the alternative:

1. **It is a whitelist, not a blacklist.** Defect 1 exists because both current
   layers enumerate a shape (`by` syntax) and something outside the enumeration
   slipped through. An applicative grammar is enforced by the *parser*, before
   any elaborator runs, so there is no elaboration-time escape to find — the
   same reason the round-1 `tacticSeq` fix worked so cleanly.
2. **It costs nothing.** The closer set is exactly three renderings, all of which
   are applications of named things. I verified all three elaborate axiom-free
   (task 3 table). No fixture and no spec form is lost.
3. **The proof-term constant lint is strictly weaker and I recommend against it
   as the primary defence.** I tested it: `of_eq_true`, `eq_self` do appear in
   simp's output, but the check is (a) a blacklist again, defeated by any simp
   call whose output happens to close via an ordinary lemma, and (b) prone to
   false positives — `of_eq_true` is an ordinary `Lean.Init` lemma a hand-written
   proof may legitimately use. Verified `simp only [Nat.add_zero]` produces the
   same `of_eq_true (eq_self b)` term, so the lint catches this case, but it is
   easy to imagine simp closing a goal with a term indistinguishable from a
   hand-written one. It is worth adding as **defence in depth**, not as the fence.
4. **One residual hole the grammar does *not* close, which the coordinator should
   know:** a grammar admitting bare identifiers still admits an identifier bound
   to a custom term elaborator via `@[term_elab]`. I confirmed a bare-atom
   elaborator passes today (`/private/tmp/t2r3/grammar.lean`). Closing that
   would require refusing any identifier that resolves to a term elaborator, or
   refusing `elab`/`macro`/`notation`/`term_elab` declarations in generated files
   outright. **I recommend the latter as a generator-side rule** (T4/T5 scope, not
   T2's): a translated Mathlib file has no business declaring a term elaborator,
   and a one-line lint over generated output enforcing that is far cheaper and
   more complete than anything `explicit_rw` can do from inside.

**Minimum acceptable action if the coordinator does not want the grammar change
now:** amend `Tactic.lean:77-81` and `RESULT.md:6-8` to state what is actually
true — that the guard catches every `by` block, written or macro-expanded, and
that a hand-written term elaborator calling the simplifier in `MetaM` is *not*
caught, so the guarantee is conditional on generated files containing no
`elab`/`macro_rules` declarations. An honest conditional claim plus a
generator-side lint is acceptable; the current unconditional claim is not.

---

## Summary

| # | Severity | Short title |
| - | -------- | ----------- |
| 1 | major | term elaborator running simp in `MetaM`/`TacticM` defeats both guard layers |
| 2 | minor | `mkLetFVars` drops a `let` whose body ignores the bound variable |
| 3 | minor | `RESULT.md` overstates the guard, miscounts fixtures, untested `then exact` |

0 critical, 1 major, 2 minor. Round-2 defects: 7/7 addressed (defect 3 only
partially — see defect 1). REVIEW-1's critical item stays fixed. All required
checks pass from scratch; scope is clean; no `sorryAx` in 59 fixture theorems;
no unsound or ill-typed replay found in any attack.
