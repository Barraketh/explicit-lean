# T2-explicit-rw — adversarial review, round 2

Verified independently in the task worktree, re-running every command rather
than reading the diff.

## Round 1 defects: all 7 confirmed fixed

Each re-run with REVIEW-1's own reproducing command:

| # | Round-1 title | Status |
| - | ------------- | ------ |
| 1 | `then` / `eq ... by` admit the simp family | **fixed** — `then simp`, `then simp_all`, `then (dsimp; simp)`, `eq ... by (simp)` now all fail in the *parser* (`unexpected identifier; expected 'assumption', 'decide', 'exact' or 'rfl'`) |
| 2 | `proj` never reduces a projection-function application | **fixed** — both the raw `Expr.proj` and the projection-function shape reduce; `proj` on `a + b` is still refused, so it cannot stand in for arbitrary `whnf` |
| 3 | `let`-body positions refused | **fixed as stated, but the implementation is defective** — see defects 1 and 2 below |
| 4 | `change` errors dump raw `Syntax` | **fixed** — message now reads ``` `change (a + 1)` ``` |
| 5 | dependent-app refusal leaks `AppBuilder` message | **fixed** — tactic's own dependent-position message |
| 6 | lint does not inspect `import` lines | **fixed** — re-adding `public meta import Lean.Meta.Tactic.Simp` makes the lint FAIL with exit 1 |
| 7 | `RESULT.md` overstates fixture coverage | **fixed** — 50 fixture theorems now, including `proj` both shapes, `mdata`, `letE` body, universe-polymorphic lemma |

## Checks re-run (all pass)

- `lake build ExplicitLean.ExplicitRw` from scratch (oleans deleted first): PASS,
  no warnings, 3.4 s.
- `python3 -B Experiment/check_explicit_rw.py`: PASS (5 fixtures + 5
  rejected-syntax), 21.6 s.
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), 0.05 s.
- Runner negative controls, all three confirmed to FAIL correctly: perturbing
  `expected.json` to an unmatchable fragment → "rejected for the wrong reason";
  making `then_simp.lean` compile → "compiled, but must be rejected"; adding an
  unlisted `.lean` to `RejectedSyntax/` → "not listed in expected.json".
- `#print axioms` on all **50** fixture theorems (namespace-qualified): **no
  `sorryAx`**; 33 axiom-free, 8 `Quot.sound`, 9 `propext`. Matches RESULT.md.
- Scope: `git diff --stat` over the merge-base shows 19 files, **all owned**.
  Working tree clean.

## Closed-closer attack (task 2): holds against direct syntax, one bypass

The syntax walk (`Tactic.lean:152-175`) recurses over *all* `getArgs`, so it is
shape-agnostic and catches `Term.byTactic` / `tacticSeq` under `paren`, `app`,
`show`, `fun`, `let`, anonymous constructor `⟨_⟩`, `▸`, and in the lemma term,
`eq` equation and `change` term slots. All ten of these were **rejected**:
`then exact (by simp)`, `then exact (show _ by simp)`, `then exact (id (by simp))`,
`then exact (fun _ => (by simp : _)) ()`, `then exact (let p := (by simp : _); p)`,
`then exact ⟨by simp⟩`, `then exact _ ▸ (by simp : _) ▸ rfl`, `foo a (by simp) at []`,
`eq (2 + 3 = (by simp : Nat)) by rfl`, `change ((by exact a) + 0)`.
`rfl` / `decide` / `assumption` dispatch to the real tactics, and the
non-reserved `&"rfl"` keywords do not shadow ordinary term uses of `rfl`,
`decide`, `exact`, `eq`, `beta`, `eta`, `proj` elsewhere in a file.

But see defect 3: the walk runs on *pre-expansion* syntax, so a macro bypasses it.

---

# Defects

## 1. A `let`-body step silently performs an unrecorded zeta, invalidating every later position (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Basic.lean:226–237` (the `.letE` / `i = 2`
branch), specifically lines 232–236.

`Expr.abstract` abstracts **free variables only** — it does not abstract an
arbitrary expression. So when the `let`-bound value is a closed term (a literal,
a constant application — the overwhelmingly common case in Mathlib),
`r.newExpr.abstract #[val]` is the identity, `newBody.hasLooseBVars` is `false`,
and the branch always takes the `else` arm `r.newExpr`, which is the
already-zeta-substituted body. The `let` is destroyed, and **no `zeta` step was
recorded for it**.

Confirmed the abstraction is a no-op for a closed value:

```
abstract: Nat.add 7 1  looseBVars=false
after instantiate1 (bvar 0): Nat.add 7 1  looseBVars=false
equal to original? true
```

The spec says "each step's `pos` refers to the term as produced by the previous
step". A recorder that saw `let y := 7; a + (y + c)` emits two body rewrites at
paths through the `let`. After step 1 the `let` is gone, so step 2's path is
stale and the replay dies:

**Failing scenario / reproduce:**

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
mkdir -p /private/tmp/t2r2 && cat > /private/tmp/t2r2/lettwo.lean <<'EOF'
import ExplicitLean.ExplicitRw
theorem two_steps (a b c d : Nat) (h1 : a = b) (h2 : c = d) :
    (let y : Nat := 7; a + (y + c)) = b + (7 + d) := by
  explicit_rw [h1 at [0, 1, 2, 0, 1], h2 at [0, 1, 2, 1, 1]]
  sorry
EOF
lake env lean /private/tmp/t2r2/lettwo.lean
```

**Expected:** both steps apply; the `let` is preserved because neither step is a
`zeta` step. **Observed:**

```
explicit_rw: step 2: position [0, 1, 2, 1, 1] does not exist: the subterm at
prefix [0, 1] is an application (children 0 = function, 1 = argument), so it has
no child 2.
Subterm:
  b + (7 + c)
```

Also directly visible in one step — `guard_target =ₛ (let y : Nat := 7; 7 + 1) = 8`
fails against the actual goal `7 + 1 = 8`:

```
cat > /private/tmp/t2r2/let1.lean <<'EOF'
import ExplicitLean.ExplicitRw
theorem cap (a : Nat) (h : a = 7) : (let y : Nat := 7; a + 1) = 8 := by
  explicit_rw [h at [0, 1, 2, 0, 1]]
  guard_target =ₛ (let y : Nat := 7; 7 + 1) = 8
  sorry
EOF
lake env lean /private/tmp/t2r2/let1.lean
```

Note the fixture `Definitional.lean`'s `let_body` passes only because it is a
single step whose `guard_target` was written against the zeta-reduced goal, so
it pins the wrong behaviour rather than catching it.

**Not unsound** — the result stays definitionally equal, and `#print axioms` is
clean. It is a replay-fidelity defect: the tactic performs a reduction the trace
did not ask for.

**Fix direction:** open the `let` with `withLetDecl` and rebuild with
`mkLetFVars` (mirroring the `.lam` child-1 branch at `Basic.lean:162–171`), so
the bound variable is abstracted *by identity* rather than by value. Add a
two-step `let`-body fixture, and a `guard_target` that requires the `let` to
survive.

## 2. `let`-body rewriting captures occurrences of the bound *value* that are not the bound variable (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Basic.lean:232` —
`let newBody := (r.newExpr.abstract #[val]).instantiate1 (.bvar 0)`.

The complement of defect 1: when the `let`-bound value *is* a free variable,
`abstract` does fire — and it abstracts **every** occurrence of that fvar in the
rewritten body, including occurrences that were never the `let` variable. The
rebuilt `let` therefore binds terms it must not bind.

**Failing scenario / reproduce:**

```
cat > /private/tmp/t2r2/cap.lean <<'EOF'
import ExplicitLean.ExplicitRw
theorem capture (a b c : Nat) (h : c = b) :
    (let y : Nat := a; y + (c + a)) = a + (b + a) := by
  explicit_rw [h at [0, 1, 2, 1, 0, 1]]
  sorry
EOF
lake env lean /private/tmp/t2r2/cap.lean
```

The step rewrites only `c` to `b`, so the body must become `y + (b + a)`.
**Observed goal:**

```
⊢ (let y := a;
    y + (b + y)) =
    a + (b + a)
```

The standalone `a` in `(c + a)` — which the source wrote as `a`, not as `y` —
has been captured into `y`. Again defeq-preserving and not unsound (`#print
axioms capture2` is axiom-free when closed with `rfl`), but the goal no longer
has the structure the trace describes, so subsequent recorded positions do not
match it.

Same fix as defect 1: `withLetDecl` / `mkLetFVars`, never value-based
`abstract`.

## 3. The tactic-block guard runs on pre-expansion syntax, so a macro smuggles `simp` into product code (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:152–175` (`checkNoTacticBlock`),
called at `Tactic.lean:183`, `340`, `349`, `439`.

`checkNoTacticBlock` walks the raw `Syntax` written at the call site. A
user-defined `macro` or `notation` whose *expansion* is `by simp` contributes no
`Term.byTactic` node at that point, so the walk sees nothing and the `by` block
is introduced later, during elaboration. This reopens round-1 defect 1 through a
different door: the forbidden tactic again runs inside the product tactic, and
again lives at the generated call site where `check_no_simp_family.py` cannot
see it.

**Failing scenario / reproduce:**

```
cat > /private/tmp/t2r2/macro.lean <<'EOF'
import ExplicitLean.ExplicitRw
macro "SM" : term => `(by simp)
theorem smuggled (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then exact SM
#print smuggled
EOF
lake env lean /private/tmp/t2r2/macro.lean
```

**Expected:** rejected, as `then exact (by simp)` is. **Observed:** compiles
with no error, and the proof term is simp's own:

```
theorem smuggled : ∀ (a b : Nat), a = b → a + 0 = b :=
fun a b h => Eq.mpr (id (congrArg (fun x => x + 0 = b) h)) (of_eq_true (eq_self b))
```

`of_eq_true (eq_self b)` is produced by `simp`, confirming it ran. The same
bypass works in the `change` slot (`macro "SMN" : term => \`(by exact (0:Nat))`
then `change (a + SMN)` — compiles).

**Fix direction:** check after elaboration rather than before — e.g. elaborate
the term with `Term.withoutTacticIncrementality` and inspect the elaborated
syntax, or (more robustly) re-run the walk on `← Lean.expandMacros stx` as well
as on the raw syntax. Add a `RejectedSyntax` case with a macro expanding to
`by simp`. How much this matters depends on whether generated Mathlib files can
define macros at all; if the answer is "never", say so explicitly in `RESULT.md`
rather than leaving the claim "no trace written in this syntax can introduce
one" (`Tactic.lean:71`) unqualified, because as written that claim is false.

## 4. No `zeta` step kind — the amended spec's kind has no syntax at all (MAJOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:89`
(`syntax explicitRwRed := ("beta" <|> "eta" <|> "proj") explicitRwPos`) and the
dispatch at `Tactic.lean:323–336`.

The spec amendment of 2026-09-16 adds `zeta` to the silent-reduction kinds:
`{"kind":"beta"|"eta"|"proj"|"zeta", ...}`. T2 implements three of the four.
T1 **does** emit it — `T1-trace-capture/ExplicitLean/SimpTrace/Tactic.lean:149-151`:

```
-- `zeta`: `let x := v; b` to `b[v/x]` (amended spec).
return { kind := "zeta", pos := s.pos, ... }
```

reached whenever `raw.before.isLet`, and the reduction itself is at
`SimpTrace/Position.lean:231-232`. So a generator consuming a T1 trace has
**nothing to render a `zeta` step as**. This is a hard interoperability break
between the two halves of the interface.

Worse, the spec says "Unknown `kind` values are a hard error for the replay
tactic", but `zeta at [...]` does not produce an unknown-kind error: it falls
through the `explicitRwStep` alternation into `explicitRwRw` and is elaborated
as a *term* named `zeta`:

```
cat > /private/tmp/t2r2/zeta.lean <<'EOF'
import ExplicitLean.ExplicitRw
example (a : Nat) : (let y : Nat := 7; a + y) = a + 7 := by
  explicit_rw [zeta at [0]]
  rfl
EOF
lake env lean /private/tmp/t2r2/zeta.lean
```

**Observed:** ``explicit_rw: step 1: lemma `zeta` does not prove an equation or
an iff; its type is ?m.15`` — a misleading message for what is really an
unsupported step kind. (A trace author who wrote `zeta` would have no idea the
kind is simply unimplemented.)

**Fix direction:** add `"zeta"` to `explicitRwRed` and implement it as
`fun sub => match sub with | .letE _ _ v b _ => pure (b.instantiate1 v) | _ =>
stepError ...`. It is a one-line reduction and it is also the honest way to make
defects 1/2 behave: the `let` is destroyed only when the trace says `zeta`.
Add a positive `zeta` fixture.

## 5. `intro_ctx` is likewise unimplemented, and RESULT.md discloses it only in passing (MINOR)

**File:** `ExplicitLean/ExplicitRw/Tactic.lean:120–121`.

The spec lists `intro_ctx` as a `STEP` kind. `RESULT.md:52` says "`intro_ctx`
unimplemented" under limitations, which is honest, but combined with defect 4 it
means **two of the spec's eight step kinds have no syntax**. Since T1 does not
yet emit `intro_ctx` (no `intro_ctx` appears in
`T1-trace-capture/ExplicitLean/SimpTrace/Tactic.lean`), this is not currently a
break — unlike `zeta`, which T1 does emit. Recording it here so the coordinator
can decide whether contextual simp is in scope for v1 before merge; if it is
not, the spec should say so rather than listing a kind neither side implements.

## 6. Spec close forms `true_intro` and `absurd:<hyp>` are renderable; `assumption:<name>` is not exactly (MINOR)

Checked against the amended close set
`rfl | true_intro | assumption:<name> | absurd:<hyp> | decide`:

- `rfl`, `decide` — direct closers. Verified working.
- `true_intro` → `then exact True.intro`. Verified working.
- `absurd:<hyp>` → `exact h.elim` / `exact absurd h (fun x => x)` on the next
  line. Verified working, but **not through `then`**: the `absurd` case arises
  after rewriting a *hypothesis* to `False`, and `Tactic.lean:471–473` refuses
  the `then` clause entirely when the trace targets a hypothesis. A generator
  must therefore emit the closer as a separate line for this form. Workable,
  but the asymmetry is undocumented in the module docs at `Tactic.lean:51–59`.
- `assumption:<name>` — the spec names the *specific* hypothesis, but the
  `assumption` closer searches the whole local context for any matching one.
  That is a (bounded) search where the spec recorded an exact name, and it is
  the one closer that can succeed for a different reason than the trace
  recorded. Prefer rendering it as `exact <name>`, which is exact and already
  supported; consider dropping the bare `assumption` closer.

No defect here that blocks a generator; listed so the closed set is on record as
checked against the amendment.

## 7. `proj` / T1 cross-check: no mismatch, but T2 accepts more than T1 emits (INFORMATIONAL)

Task item 4 asked whether the trace capture ever emits `proj` for the
instance-projection case. **It does not.** T1 classifies a definitional step as
`proj` only when `before.isProj` — `SimpTrace/Tactic.lean:81-82`
(`private def isProj (before : Expr) : Bool := before.isProj`) and
`SimpTrace/Position.lean:235` (`if e.isProj then ...`). An `HAdd.hAdd`-through-
`instHAdd` reduction is not an `Expr.proj`, so it falls through to the
`unfoldedConstant?` branch and is emitted as `unfold`, or failing that as
`change`. So T1 emits `proj` strictly for the raw-`Expr.proj` shape.

T2 accepts that shape **and** the projection-function-application shape, while
requiring the projected argument to `whnfCore` to a constructor application
(`Tactic.lean:299–305`). Verified: raw shape reduces (`(Wrap.mk n).val`),
function shape reduces (`(Two.mk 3 4).a`), and `proj at [0,1]` on `a + b` is
refused with "the projection's argument is not a constructor application". So
T2's acceptance is a strict superset of T1's emission, the constructor guard
prevents `proj` from becoming a free `whnf`, and **neither side is wrong**. No
change needed.

---

## Summary

| # | Severity | Short title |
| - | -------- | ----------- |
| 1 | major | `let`-body step performs an unrecorded zeta, invalidating later positions |
| 2 | major | `let`-body rewrite captures occurrences of the bound value |
| 3 | major | macro expanding to `by simp` bypasses the tactic-block guard |
| 4 | major | no `zeta` step kind, although T1 emits it; no unknown-kind error either |
| 5 | minor | `intro_ctx` unimplemented (T1 does not emit it, so not yet a break) |
| 6 | minor | `assumption` closer searches where the spec named a hypothesis |
| 7 | info  | `proj`: T1/T2 cross-check clean, no mismatch |

0 critical, 4 major, 2 minor, 1 informational. Round-1 defects: 7/7 fixed.
All required checks pass; scope is clean; no `sorryAx`; no unsound replay found.
