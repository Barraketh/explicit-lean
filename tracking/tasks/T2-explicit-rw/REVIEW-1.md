# T2-explicit-rw — adversarial review, round 1

Verified independently in the task worktree. Scope is clean (all 11 changed
files are owned). `lake build ExplicitLean.ExplicitRw` passes with no warnings;
all 5 fixtures pass; both check scripts pass and both were re-confirmed to
*fail* when fed a broken `guard_target` and a mismatched `#guard_msgs`.
`#print axioms` on all 41 fixture theorems: no `sorryAx`; only `propext` and
`Quot.sound`, and in every case identical to the `conv` cross-check theorem
beside it. No `sorry`/`admit`/`unsafe`/`implemented_by`/`native_decide` in
product code. No product import reaches simp machinery. Soundness attacks
(dependent application argument, dependent `∀` domain, non-Prop `∀` body,
projection structure argument, non-defeq `change`) were all refused with a
step-indexed error; I could not construct an unsound or ill-typed replay.

The defects below are real, reproduced, and not style preferences.

---

## 1. `then <tac>` accepts the entire simp family — product-rule hole (CRITICAL)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:91` (`explicitRwClose` is
`" then " Lean.Parser.Tactic.tacticSeq`), executed unchecked at
`Tactic.lean:343` (`evalTactic closeStx[0][1]`). Same hole at
`Tactic.lean:84` / `Tactic.lean:264`: `eq <term> by <tacticSeq>` runs an
arbitrary `tacticSeq` through `Tactic.run ... (evalTactic byStx)`.

`explicit_rw` is product code — it is what a translated Mathlib file runs. The
governing rule in `AGENTS.md` forbids `simp`, `simp_all`, `dsimp`, … in
generated code. Because `then` and `eq ... by` embed an unrestricted
`tacticSeq`, a generated trace can carry the whole simp family *inside* the
product tactic, and `Experiment/check_no_simp_family.py` cannot see it: the
lint scans `ExplicitLean/ExplicitRw*` only, never the generated call sites.
The spec also names the allowed closers as `rfl|decide`, not "any tactic".

**Observed (all elaborate with no error):**

```lean
theorem smuggle (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then simp

theorem smuggle2 (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then simp_all

theorem smuggle5 (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then (dsimp; simp)

theorem smuggle3 : (2 + 3) + 1 = 6 := by
  explicit_rw [eq (2 + 3 = 5) by (simp) at [0, 1, 0, 1]]
  rfl
```

**Expected:** each is rejected at elaboration with an error naming the
forbidden tactic. **Observed:** all succeed. (Only the deprecated
`simp_arith` errors, and only because Lean itself deprecated it — not because
`explicit_rw` refused it.)

**Reproduce:**

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
mkdir -p /private/tmp/t2 && cat > /private/tmp/t2/smuggle.lean <<'EOF'
import ExplicitLean.ExplicitRw
theorem smuggle (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then simp
theorem smuggle2 (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then simp_all
theorem smuggle3 : (2 + 3) + 1 = 6 := by
  explicit_rw [eq (2 + 3 = 5) by (simp) at [0, 1, 0, 1]]
  rfl
EOF
lake env lean /private/tmp/t2/smuggle.lean   # exits 0 — should not
```

**Proposed restriction.** Do not accept a free `tacticSeq` in product syntax.
Replace both with a closed enumeration matching the spec:

- `explicitRwClose := " then " ("rfl" <|> "decide" <|> "trivial" <|> "assumption" <|> ("exact " term))`
- `explicitRwEq := "eq " term " by " ("rfl" <|> "decide") explicitRwPos`

(the spec's `close` field is exactly `rfl|trivial|assumption:<name>|eq_self|decide`,
and its `eq` kind is exactly `by: "rfl"|"decide"`). If a free `tacticSeq` is
kept for ergonomics, it must be walked at elaboration and rejected when any
node's kind is in the simp family, and `check_no_simp_family.py` must also scan
generated/translated call sites — but the closed enumeration is the honest fix
and is what the spec already specifies.

---

## 2. `proj` step is dead for the projection-function form it claims to accept (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:199–214` (`projReduce`),
specifically line 210: `let r ← withReducible (whnfCore sub)`.

`projReduce` accepts two shapes (line 200–206): a raw `Expr.proj`, **or** an
application whose head is a projection function (`getProjectionFnInfo?`). For
the second — which is what the elaborator actually produces for `(P.mk 3 4).fst`
in a structure with more than one field — reduction needs a delta step to
unfold the projection function `P.fst`. `whnfCore` performs no delta, and
`withReducible` further restricts it, so `r == sub` always holds and the step
always reports "the projection does not reduce; its argument is not a
constructor application" — which is *false*, the argument *is* a constructor
application. There is no positive `proj` fixture, so this is untested.

**Failing scenario:**

```lean
structure P where
  fst : Nat
  snd : Nat

theorem proj_step : (P.mk 3 4).fst = 3 := by
  explicit_rw [proj at [0, 1]]
  guard_target =ₛ 3 = 3
  rfl
```

**Expected:** the goal becomes `3 = 3`. **Observed:**
`explicit_rw: step 1: `proj` at this position: the projection does not reduce;
its argument is not a constructor application.`

Diagnosis confirming the cause (`whnfCore` is a no-op here at both
transparencies):

```
subterm: { fst := 3, snd := 4 }.fst
raw:     Atk10.P.fst (Atk10.P.mk ...)
whnfCore default:          { fst := 3, snd := 4 }.fst
withReducible whnfCore:    { fst := 3, snd := 4 }.fst
```

**Reproduce:**

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
cat > /private/tmp/t2/proj.lean <<'EOF'
import ExplicitLean.ExplicitRw
structure P where
  fst : Nat
  snd : Nat
theorem proj_step : (P.mk 3 4).fst = 3 := by
  explicit_rw [proj at [0, 1]]
  guard_target =ₛ 3 = 3
  rfl
EOF
lake env lean /private/tmp/t2/proj.lean
```

**Fix direction:** for the projection-function shape, delta-unfold the
projection function first (`unfoldDefinition?` at default transparency, as
`unfoldConst` at `Tactic.lean:177–181` already does) and then `whnfCore`;
keep the "not a projection" guard at line 207 so `proj` still cannot stand in
for an arbitrary `whnf`. Add a positive `proj` fixture covering both the
`Expr.proj` and the projection-function shapes — the current fixture set has
none, and `RESULT.md` nonetheless asserts "Fixtures cover every case the task
listed".

---

## 3. `let`-body positions (child 2) are refused although they need no cast (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Basic.lean:210–218`, the `.letE` / `i = 2`
branch: any `r.proof? = some _` is rejected with "rewrites the body of a `let`;
only definitional steps are supported there."

The spec (`SIMP-TRACE-SPEC.md`) requires `letE` navigation with `0` = type,
`1` = value, `2` = body, and a propositional rewrite in a `let` **body** is an
ordinary non-dependent congruence — it needs no cast at all. Ordinary Lean does
it, axiom-free:

```lean
theorem letE_conv (a b : Nat) (h : a = b) : (let y : Nat := 7; a + y) = b + 7 := by
  conv => lhs; rw [h]
-- 'letE_conv' does not depend on any axioms
```

So this is not the spec's "dependent positions needing casts stay unresolved"
escape that `RESULT.md` invokes; it is an unimplemented position kind. Note the
`0` (type) and `1` (value) branches at `Basic.lean:194–209` *are* genuinely
dependent and refusing them is correct — only child `2` is wrongly refused.

**Failing scenario:**

```lean
theorem letE_body (a b : Nat) (h : a = b) : (let y : Nat := 7; a + y) = b + 7 := by
  explicit_rw [h at [0, 1, 2, 0, 1]]
```

**Expected:** goal becomes `(let y : Nat := 7; b + y) = b + 7`.
**Observed:** `explicit_rw: step 1: position [0, 1, 2] rewrites the body of a
`let`; only definitional steps are supported there.`

**Reproduce:**

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
cat > /private/tmp/t2/letbody.lean <<'EOF'
import ExplicitLean.ExplicitRw
theorem letE_body (a b : Nat) (h : a = b) : (let y : Nat := 7; a + y) = b + 7 := by
  explicit_rw [h at [0, 1, 2, 0, 1]]
  sorry
EOF
lake env lean /private/tmp/t2/letbody.lean
```

**Fix direction:** mirror the `.lam` child-1 branch (`Basic.lean:146–155`) —
`withLetDecl`, then `mkLetFVars` the proof as well — or, if a `let`-body
congruence is judged out of scope, say so explicitly in `RESULT.md` as an
unimplemented spec position rather than filing it under the dependent-cast
exemption.

---

## 4. `change` error messages print raw syntax internals, not the term (MINOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:241`:
`runDefeqStep idx e pos s!"`change {target}`" fun sub => do`

`target` is a `Term`. The `s!` interpolation selects `ToString Syntax`, which
dumps the parse tree, instead of the `m!` pretty-printer used everywhere else
in these files. The error names the step index correctly, so this is quality,
not correctness — but the message is unreadable for the one step kind that is
the documented "last-resort escape hatch", and no negative fixture pins a
`change` message, so nothing caught it.

**Failing scenario:**

```lean
theorem change_bad (a : Nat) : a + 0 = a := by
  explicit_rw [change (a + 1) at [0, 1]]
```

**Expected:** ``explicit_rw: step 1: `change (a + 1)` at position [0, 1]
produced a term that is not definitionally equal to the original. ...``
**Observed:**

```
explicit_rw: step 1: `change (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_+_» `a "+" (num "1")) ")")` at position [0, 1] produced a term that is not definitionally equal to the original.
Before
  a + 0
After
  a + 1
```

**Reproduce:**

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
cat > /private/tmp/t2/change.lean <<'EOF'
import ExplicitLean.ExplicitRw
theorem change_bad (a : Nat) : a + 0 = a := by
  explicit_rw [change (a + 1) at [0, 1]]
  sorry
EOF
lake env lean /private/tmp/t2/change.lean
```

**Fix direction:** change `runDefeqStep`'s `what` parameter from `String` to
`MessageData` and pass `m!"`change {target}`"`. Add a negative fixture pinning
a `change` message so it stays pinned. (`unfold` at `Tactic.lean:223` uses the
same `s!` but interpolates a `Name`, which has a correct `ToString`, so it is
unaffected.)

---

## 5. Dependent-application refusal leaks a raw `AppBuilder` message (MINOR)

**File:** `ExplicitLean/ExplicitRw/Basic.lean:70–80` (`congrApp`) — the
`.app` / `i = 1` path at `Basic.lean:111–115` calls `mkCongrArg`, which throws
its own internal error when the function is dependent. `runSteps`'
catch-and-prefix at `Tactic.lean:290–298` adds the step index, so the failure
is *not* silent and the goal is not corrupted (verified: no ill-typed term is
produced). But the reason is phrased in `AppBuilder` terms rather than in the
tactic's own vocabulary, unlike every sibling refusal
(`Basic.lean:130–133`, `143–145`, `168–177`, `188–190`, `200–218`), which all
explain the dependent-position rule to the trace author.

**Failing scenario:**

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
def P (n : Nat) (v : Vec Nat n) : Prop := True

example (n m : Nat) (h : n = m) (v : Vec Nat n) : P n v := by
  explicit_rw [h at [0, 1]]
```

**Expected:** a message in the style of the other dependent refusals, e.g.
"position [0, 1] rewrites an argument of a dependent function; rebuilding that
needs a cast, which `explicit_rw` does not build."
**Observed:**

```
explicit_rw: step 1: AppBuilder for `congrArg`, non-dependent function expected
  P
has type
  (n : Nat) → Vec Nat n → Prop
```

**Reproduce:**

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
cat > /private/tmp/t2/dep.lean <<'EOF'
import ExplicitLean.ExplicitRw
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
def P (n : Nat) (v : Vec Nat n) : Prop := True
example (n m : Nat) (h : n = m) (v : Vec Nat n) : P n v := by
  explicit_rw [h at [0, 1]]
  sorry
EOF
lake env lean /private/tmp/t2/dep.lean
```

**Fix direction:** in `congrApp`, check `(← inferType f)` for a dependent
binder before calling `mkCongrArg`/`mkCongr` and raise the tactic's own
dependent-position error. Add a negative fixture.

---

## 6. `check_no_simp_family.py` does not inspect import lines (MINOR)

**File:** `Experiment/check_no_simp_family.py:32–59`. The three patterns match
identifier *uses*; an import line contributes no matching token, so
`public meta import Lean.Meta.Tactic.Simp` alone passes the lint.

Verified: adding that single import to `ExplicitLean/ExplicitRw/Basic.lean`
(changing nothing else) leaves the lint at
`check_no_simp_family: PASS (3 file(s) scanned ...)`.

This is minor on its own — importing without using is harmless, and every
*use* I attempted was caught. I tried and failed to evade the lint with
`open Lean.Meta.Simp in`, `open Lean Meta Lean.Meta.Simp in` + bare names
(caught on the `open` line), `abbrev S := Lean.Meta.Simp.Result`,
`_root_.Lean.Meta.Simp.main`, `Simp.Config`, `Simp.Result`, `mkSimpContext`,
`simpGoal`, `simpOnly`, `«simp»`, `simp only`, `dsimp`, `norm_num`. The lint
is otherwise sound and scans all three product files. But the check's own
docstring (lines 5–9) claims it catches code that "call[s], import[s] for use,
or expand[s] to `Lean.Meta.Simp`" — the import clause is not enforced.

Note this defect is *separate from* defect 1: defect 1 escapes the lint
because the simp text lives at the generated call site, outside
`ExplicitLean/ExplicitRw*` entirely, which no tightening of this script fixes.

**Reproduce:**

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
cp ExplicitLean/ExplicitRw/Basic.lean /private/tmp/t2/Basic.bak
sed -i '' 's|^public meta import Lean.Meta.Transform$|public meta import Lean.Meta.Transform\npublic meta import Lean.Meta.Tactic.Simp|' ExplicitLean/ExplicitRw/Basic.lean
python3 -B Experiment/check_no_simp_family.py   # PASS — should FAIL
cp /private/tmp/t2/Basic.bak ExplicitLean/ExplicitRw/Basic.lean
```

**Fix direction:** add a pattern over `^\s*(public\s+)?(meta\s+)?import\s+\S*Simp\S*`
applied before comment stripping.

---

## 7. `RESULT.md` overstates fixture coverage (MINOR)

**File:** `tracking/tasks/T2-explicit-rw/RESULT.md:44` — "Fixtures cover every
case the task listed."

Runtimes and pass claims in the table reproduce (build 1.6 s clean; fixtures
1.9–2.5 s each; `check_explicit_rw.py` 12.2 s / 5 fixtures;
`check_no_simp_family.py` 3 files) and the "verified to fail" claim on both
scripts reproduces. But the coverage claim does not:

- **No positive `proj` fixture** — and `proj` is in fact broken (defect 2).
  `test/ExplicitRw/Definitional.lean` covers `unfold`, `beta`, `eta`,
  `change`, `eq ... by rfl`, `eq ... by decide`, but not `proj`.
- **No `mdata` fixture**, though the task list and the spec both name `mdata`
  positions explicitly. (`Basic.lean:117–123` implements it; it is simply
  untested — I could not readily construct a goal retaining `mdata`, which is
  itself worth a note.)
- **No `letE` fixture** in any direction, though the spec names `letE` 0/1/2
  (see defect 3).
- **No universe-polymorphic-lemma fixture.** `Lemmas.lean:72` uses
  `{α : Type}`, which is universe-*mono*morphic; the task list asks for a
  universe-polymorphic lemma.
- **No fixture for a stale position** (the task list asks for "a step whose
  position is stale relative to the previous step's result must fail with the
  documented error"). The behaviour is in fact correct — I verified a stale
  step fails with a step-indexed mismatch — but it is unpinned.

`RESULT.md`'s "Known limitations" should also move the `let`-body case out of
the dependent-cast exemption (defect 3), and should disclose the `then` /
`eq ... by` tacticSeq hole (defect 1) rather than describing the closing form
as "exactly sugar for writing the tactic on the next line" — for product code
under the governing rule, that sugar is precisely the problem.

---

## Summary

| # | Severity | Short title |
| - | -------- | ----------- |
| 1 | critical | `then` / `eq ... by` admit the whole simp family into product code |
| 2 | major    | `proj` step never reduces a projection-function application |
| 3 | major    | `let`-body positions refused although cast-free and spec-required |
| 4 | minor    | `change` errors dump raw `Syntax` instead of the term |
| 5 | minor    | dependent-application refusal leaks an `AppBuilder` message |
| 6 | minor    | lint does not inspect `import` lines |
| 7 | minor    | `RESULT.md` overstates fixture coverage |

1 critical, 2 major, 4 minor.
