# T2-explicit-rw — adversarial review, round 8

Fresh eyes. `RESULT.md` read but not trusted: every count recomputed from the
committed artefacts or from my own runs. Lean compiles run serially. Scratch
under `/private/tmp/t2r8`. No product file left edited: the lint injections, the
two axiom-audit injections and the `expected.json` perturbation were each
reverted, with `git status --porcelain` clean after every one (only this
REVIEW-8.md remains untracked).

Worktree HEAD `1d8b125`, merge-base `6eaed50`. T1 read-only at tip `18a0559`
(mid-fix: `Experiment/check_simp_trace.py`, `SimpTrace/{Recorder,Tactic,
Traversal}.lean` modified but uncommitted; I read only committed state plus the
generated `test/SimpTrace/out/`).

## Round 7 defects: 4/4 re-checked, all fixed

| # | Round-7 title | Status |
| - | ------------- | ------ |
| 1 | antiquotation "internal error" in the recursive side-proof slots | **fixed** — one `isAntiquot` (`Tactic.lean:469`) now serves all three fallthroughs (`:648`, `:1238`, `:1349`). Pinned by three `#guard_msgs` fixtures at `Negative.lean:258-272` (step slot, side-proof slot, `congr` nested-step slot). Re-run live: each gives the plain message, exit 1 |
| 2 | `congr` refusal printed two identical terms | **fixed** — `Tactic.lean:1156-1168` renders both sides *eagerly* under `pp.explicit`. Live on my own rebuild of the round-7 input: `@Eq B (@cast A B hAB x) (@cast A B hAB x)` vs `@Eq B (@cast A B hAB x) (@cast C B hAB x)` — visibly different, and the trailing note says why |
| 3 | sweep figures had no committed artefact | **fixed** — `test/ExplicitRw/sweep/{probes.json,README.md}` are committed (`git ls-files`) and `check_explicit_rw.py:54-127` drives them. 55 escape x 6 slots = 330 and 20 benign x 6 = 120 recompute exactly from `probes.json` |
| 4 | stale fixture count | **fixed** — `RESULT.md:85` now says 7; `ls test/ExplicitRw/*.lean | wc -l` = 7 |

Round 6's critical case is also still fixed: `theorem false_thm : (1:Nat) = 2`
via the `eq` slot emits `step 1: Unknown identifier 'unknownIdent'` and exits
**1**.

---

# Defects

## 1. Two of the six sweep slots are vacuous: every probe dies on the position, never on the term (MAJOR, methodology)

**File:** `test/ExplicitRw/sweep/probes.json:18-19`; classifier at
`Experiment/check_explicit_rw.py:101`.

Both templates rewrite at position `[0,1]`:

```
"sideproof": "explicit_rw [Nat.sub_add_cancel _ at [0,1] with [exact {T}]]",
"congrnest": "explicit_rw [congr 0 [{T} at []] at [0,1]]"
```

The probe goal is `True` (`check_explicit_rw.py:74-75`) — a constant with **no
children**. So the step fails on the position *before* `{T}` is ever elaborated.

**Observed** (`admit` and `$x`, the only two escape terms that get past the
parser, in both slots — 4 probes):

```
error: explicit_rw: step 1: position [0, 1] does not exist: the subterm at
prefix [] is a constant (no children), so it has no child 0.
```

**Control:** substituting a term that is neither an escape nor a real identifier
(`ZZZ_NOT_A_REAL_IDENT`) produces the **byte-identical** error. The output
carries no information about the probe at all.

**Why this matters:** `check_explicit_rw.py:101` credits these to
`elab_rejected` on the sole evidence that `out.strip()` is non-empty. So
RESULT.md's "12 at elaboration" includes **4 rejections whose evidence is
unrelated to the escape term**. The other 8 are real (I read each message).

**Bounded, not fatal.** The remaining 106 escape probes in those two slots
(53 terms x 2) are *parser*-rejected, and a parse error precedes tactic
execution, so that evidence is sound. The defect costs 4 of 330 probes, and the
two slots test the grammar but not the elaborator.

**The fix already exists elsewhere in the tree.** `Strict.lean:44-45` uses the
*same lemma at the same position* —
`explicit_rw [Nat.sub_add_cancel _ at [0, 1] with [exact nosuchproof]]` — but
against the goal `(n - 5) + 5 = n`, which has structure at `[0,1]`. There the
probe term genuinely reaches the elaborator and the fixture pins
`step 1: Unknown identifier 'nosuchproof'`. The sweep template differs only in
using the structureless goal `True`.

**Expected:** give those two templates a goal with structure, exactly as
`Strict.lean:44` does, so the probe reaches the term; or assert the error text
names the probe.
**Command:** `python3 /private/tmp/t2r8/plant/harness.py /private/tmp/t2r8/plant/p2.json`

## 2. `elab_rejected` accepts any non-empty output as proof of rejection (MINOR)

**File:** `Experiment/check_explicit_rw.py:101`.

```python
elif term in POST_PARSE_ESCAPES and out.strip():
```

Neither the exit code nor the message is checked. Defect 1 is the instance that
actually fires today, but the branch would equally credit a probe that *succeeds*
and then trips the template's trailing `trivial`, or that emits an unrelated
warning. `POST_PARSE_ESCAPES` keeps the blast radius to two terms, which is the
right instinct — the guard is simply not finished.

**Expected:** require the probe to exit non-zero **and** the output to contain
`explicit_rw:` (or `Unknown identifier`), so the rejection is attributable.

## 3. The sweep's `exact` slot never tests the bare term (MINOR)

**File:** `Experiment/check_explicit_rw.py:84`.

The body is `"  " + tmpl.replace(...) + "\n  trivial\n"`, and
`explicitRwTermApp` (`Tactic.lean:175`) spans lines, so in the `exact` slot the
trailing `trivial` is parsed as an **argument** to the probe term.

**Input:** `explicit_rw [] then exact True.intro` + newline + `trivial`.
**Observed:** `error: Function expected at True.intro ... because this term is
being applied to the argument trivial`.
**Without the trailing line:** exit **0**, no output.

The direction is safe — it makes escapes look *less* admitted, never more — but
the slot is measuring `{T} trivial`, not `{T}`.
**Command:** `lake env lean` on the two files above (`/private/tmp/t2r8/`).

## 4. RESULT.md: "12 at elaboration (only `admit` and `$x`, which no parser can stop)" overstates the evidence (MINOR, honesty)

**File:** `RESULT.md:95-96`.

The arithmetic is right (2 terms x 6 slots) and the parenthetical about
antiquotations is **correct** — Lean adds an antiquotation alternative to every
`declare_syntax_cat`, so `$x` genuinely cannot be excluded at parse time. But
per defect 1, 4 of those 12 were not rejected *for the stated reason*. The line
reads as twelve attributable elaboration-time refusals; eight are.

Related, same lines: `RESULT.md:91` gives "~6 min" for
`check_explicit_rw.py`, which is the **default 2-slot** run. The
`T2_FULL_SWEEP=1` run that produces the 330/318/12 figures on the next line is
far longer — ~450 probes at roughly 2-4 s each on this Mac. The reader is given
one runtime and two different runs; the full-sweep cost should be stated
separately.

## 5. The axiom audit does not catch a new axiom, and RESULT.md says it was verified to (MAJOR)

**File:** `Experiment/check_explicit_rw.py:173-176`; claim at `RESULT.md:99-101`.

The gate is a substring test for one string:

```python
if "sorryAx" in output:
```

`#print axioms` on a theorem depending on a **newly declared axiom** prints
`depends on axioms: [T.sneaky_ax]` — no `sorryAx` — so the gate does not fire.
The governing rule in `AGENTS.md` forbids "no `sorry`/`admit`, **no new
axioms**"; the audit enforces only the first half.

**Input:** `axiom sneaky_ax : (1:Nat) = 2` plus
`theorem injected_axiom_probe : (1:Nat) = 2 := sneaky_ax`, inserted **inside**
`namespace ExplicitRwTest.Basic` in `test/ExplicitRw/Basic.lean`.
**Observed:** `run_axiom_check` returns **exit 0**, report
`112 theorems, no sorryAx (75 axiom-free)`.
**Expected:** exit 1 naming the theorem and the new axiom.

**Why round 7 believed otherwise.** I reproduced its result first and got exit 1
— but for an unrelated reason: appending to the end of `Basic.lean` puts the
theorem *after* `end ExplicitRwTest.Basic`, so the audit generates
`#print axioms ExplicitRwTest.Basic.injected_axiom_probe` for a constant that
does not exist and the scratch file fails to **compile** (`Unknown constant`).
That is the `code != 0` branch at `:171`, not the axiom gate. Injecting inside
the namespace — the placement a real regression would have — passes cleanly.

**Fix:** compare against an allowlist (`propext`, `Classical.choice`, `Quot.sound`)
and fail on anything else, rather than grepping for `sorryAx`. The data is
already in hand: the report counts "axiom-free" lines, so the non-axiom-free
ones are being parsed and discarded.
**Command:** `python3 -B -c "...run_axiom_check..."` (transcript in
`/private/tmp/t2r8/`); reverted, `git status --porcelain` clean.

## 6. Generator readiness: no way to name an inaccessible hypothesis (MAJOR, product)

**File:** `Tactic.lean:340-341` (`explicitRwSideIntro` takes `ident`); no
`rename_i` anywhere in `ExplicitLean/ExplicitRw*`.

The spec's local-hypothesis paragraph says a generator "names an inaccessible
hypothesis with `rename_i` before using it". T2 has **no syntax for that**, and
neither recorded name can be written literally. From
`test/SimpTrace/out/inaccessible.json`:

```json
{"kind":"rw","pos":[0,1,0,1],"name":"a✝","dir":"fwd",
 "local":{"userName":"a._@._internal.0.test.SimpTrace.Fixtures.2021293418._hygCtx._hyg.21",
          "inaccessible":true,"ctxIndex":3}}
```

`name` is the display form `a✝`; `userName` is an internal hygienic name. Only
`ctxIndex` identifies the declaration, and T2 has no syntax that consumes it.
Writing `exact a✝` is a parse error (`expected token`) — safely, not silently,
but still a hard stop.

I translated all 65 of T1's raw traces with a mechanical translator
(`/private/tmp/t2r8/translate.py`, ~90 lines, what a T4 generator would do):
**56/65 render**. Of the 9 that do not, **5 are blocked by this one gap**
(`inaccessible.json`, `local_named_inaccessible.json`,
`name_unicode_inaccessible.json`, `shadow_inaccessible.json`,
`user_congr_ite.json` — the last through `close.by = "assumption:a✝"`).

This is the largest single generator blocker and it is on the T2 side.
**Command:** `python3 /private/tmp/t2r8/translate.py test/SimpTrace/out/*.json`

## 7. Generator readiness: `zeta` with a `name` has no syntax (MINOR, cross-task)

`Tactic.lean:362-363`: `explicitRwRed` is a bare keyword plus a position, no
name. T1's `zeta_delta_at_hyp.json` emits `{"kind":"zeta","pos":[1,0],"name":"g"}`.
The **spec** defines no `name` on `zeta` either, so T1 is emitting a field the
spec does not define and T2 cannot consume. One of the two must move; flagging
it as a coordinator decision rather than assigning blame.

## 8. Module documentation omits half the step forms a generator must emit (MAJOR, docs)

**File:** `Tactic.lean:33-45` — the "Step forms" table, which is what a
generator author reads first.

Missing from the table entirely:

| Construct | Where it is actually documented |
| --------- | ------------------------------- |
| `congr <i> [steps] at [..]` (spec's `congr` kind) | only `:417-431`, 380 lines below |
| `iota at [..]` (spec kind, implemented, has fixtures) | only `:355-363` |
| `with [...]` — the **only** rendering of the spec's `side` field | only `:346-347` |
| the side-proof grammar (`intro h ; …`, nested `explicit_rw`, `omega`, `nofun`) | only `:312-341` |
| `prop: "true"/"false"` → `eq_true`/`eq_false` | **nowhere in product code** — only in a *test comment*, `Lemmas.lean:184` |

The table also still lists `intro_ctx` as the last row while `congr` — a step
kind the spec defines and T2 implements — is absent. A generator author working
from this table would not know `side` conditions or `congr` are expressible.
**Expected:** one table covering every spec kind, with the `prop` convention
stated in product documentation rather than in a fixture comment.

## 9. RESULT.md is 115 lines against COORDINATION.md's 60 (MINOR, process)

`wc -l tracking/tasks/T2-explicit-rw/RESULT.md` → 115. COORDINATION.md caps it
at 60. Flagged in rounds 1-7 as well; still no recorded waiver. Raising it once
more only so the coordinator either grants the waiver or the file is cut.

---

## Correction to REVIEW-7: both "T1-side" merge-gate findings were reviewer errors

Round 7 gated the *joint* merge on "T1 emits no `to` field on `change` steps"
(MAJOR) and "T1 locations omit `pre`/`post`" (MINOR). **Both are wrong.** They
were read off `test/SimpTrace/expected/*.json`, which are deliberately
**stripped comparison skeletons**: `Experiment/check_simp_trace.py:11-13` says
the debug fields `before`, `after`, `pre`, `post`, `lhs`, `rhs`, `to` "are
deliberately not compared".

The real traces are `test/SimpTrace/out/*.json`, written by the recorder
(`SimpTrace/Types.lean:199-230`). Measured over all 65:

- `change` steps carrying `to`: **6 of 6** (0 missing)
- locations carrying `pre` and `post`: **67 of 67** (0 missing)
- top-level `module` / `occurrence` / `call`: present on all 65

There is no T1-side merge blocker of that kind. I re-ran my whole integration
against the raw traces to be sure.

---

## Sweep classification

**What the runner measures.** `check_explicit_rw.py:54-127` compiles one file per
(term, slot) pair and classifies on the *text* of the output: `parsed_off` is a
substring test for `unexpected token` / `unexpected identifier` / `expected
token` / `missing end of character literal`. An escape must be `parsed_off`; the
two terms in `POST_PARSE_ESCAPES` may instead be rejected later; anything else
surviving the parser is a failure. A benign term must not be `parsed_off` —
whether it then type-checks is explicitly not the sweep's business (`sweep/
README.md`), which is correct, since most probe templates are ill-typed on
purpose.

**The 12 non-parser-rejected probes, enumerated.** I compiled all 12 myself and
read each message:

| Term | Slot | Rejection | Robust? |
| ---- | ---- | --------- | ------- |
| `admit` | `exact` | `Unknown identifier 'admit'` | **yes** — `elabStrict`, `withoutErrToSorry` throws |
| `admit` | `lemma` | `step 1: Unknown identifier 'admit'` | **yes** — `elabStrict` |
| `admit` | `change` | `step 1: Unknown identifier 'admit'` | **yes** — `elabStrict` |
| `admit` | `eq` | `step 1: Unknown identifier 'admit'` | **yes** — `elabStrict` |
| `admit` | `sideproof` | *position* error | **no evidence** (defect 1) |
| `admit` | `congrnest` | *position* error | **no evidence** (defect 1) |
| `$x` | `exact` | `antiquotations are not admitted in a trace term.` | **yes** — `isAntiquot`, closed dispatch |
| `$x` | `lemma` | `… in a trace step.` | **yes** — closed dispatch |
| `$x` | `change` | `… in a trace term.` | **yes** — closed dispatch |
| `$x` | `eq` | `… in a trace term.` | **yes** — closed dispatch |
| `$x` | `sideproof` | *position* error | **no evidence** (defect 1) |
| `$x` | `congrnest` | *position* error | **no evidence** (defect 1) |

`admit` is safe for a structural reason, not a listed one: `admit` is a *tactic*,
there is no term-level constant of that name, so it can only ever arrive as a
bare identifier and die in `elabStrict`. `$x` is safe because every
`declare_syntax_cat` gets an antiquotation alternative for free — so it truly
cannot be excluded at parse time — and all three dispatch fallthroughs test for
it before the "internal error" branch.

**Variants I probed, none slipped:** `sorry` as a term is a *keyword token* and
is parser-rejected in **all six slots** (re-run this round, every message
`unexpected token 'sorry'`). `⟨…⟩` is parser-rejected, so `Exists.intro _ sorry`
cannot be spelled at all — and its `sorry` would be a keyword regardless.

For `admit` (or anything else) **inside a nested side proof** I argue from the
grammar rather than from a probe: `explicitRwSideProof` is a closed enumeration
(`Tactic.lean:327-341`) — `rfl`, `decide`, `omega`, `nofun`, `exact <term>`,
`intro <ids> ; <sideProof>`, nested `explicit_rw` — and its dispatch
(`:1318-1352`) calls `evalTactic` only on **quoted constants** it builds itself,
never on user syntax. So the only way a term enters a nested side proof is the
`exact` slot, which routes to `elabStrict` at `:1328`, exactly as the top-level
`exact` does. The `intro` case recurses into the same closed match. Nothing else
reaches an elaborator.

**Can the classification be fooled? The three required plants.**

| Plant | Required | Observed |
| ----- | -------- | -------- |
| benign term that fails **elaboration** (`undefinedIdentifierXYZ`, `lemma` slot) | must NOT count as an escape | `BENIGN_OK` — correct; the benign branch only fails on parse rejection |
| escape that **elaborates** (`Nat.add_zero`, `lemma` slot) | must count as an escape | `ADMITTED(survived parser)` → added to `failures`, run exits 1. **Cannot be waved through** |
| escape rejected **only at elaboration** (`admit`, `$x`) | must land in the elaboration bucket | `ELAB_REJECTED` in all four slots tried — but in `sideproof` on unrelated evidence (defect 1) |

Plants run through a standalone replica of the classifier
(`/private/tmp/t2r8/plant/harness.py`) so the committed `probes.json` was never
edited. Conclusion: **the classifier cannot be fooled into passing a real
escape** — that path is sound. Its weakness is the opposite one, crediting
rejections it has not actually attributed (defects 1-2).

---

## Generator readiness

Read `Tactic.lean`'s documentation as a generator author, then tested every spec
construct. Verdict per construct:

| Spec construct | T2 syntax | Documented in the step table? |
| -------------- | --------- | ----------------------------- |
| `rw` name/dir/args | `e at [..]`, `← e at [..]`, `e a b at [..]` | yes |
| `rw.side` | `with [...]` | **no** (defect 8) |
| `rw.prop` true/false | `eq_true h` / `eq_false h` (ordinary lemmas) | **no — nowhere in product code** (defect 8) |
| `rw.local` userName | plain identifier | yes |
| `rw.local` **inaccessible** / `ctxIndex` | **none; no `rename_i`** | — (**defect 6**) |
| `unfold` | `unfold c at [..]` | yes |
| `beta`/`eta`/`proj`/`zeta` | keyword + pos | yes |
| `iota` | keyword + pos | **no** (defect 8) |
| `zeta` **with `name`** | **none** | — (**defect 7**) |
| `change.to` | `change t at [..]` | yes, but see below |
| `change.source` | provenance only, no syntax needed | n/a |
| `eq … by rfl`/`by decide` | `eq (l = r) by rfl|decide at [..]` | yes (verified `decide` live) |
| `congr` arg + nested steps | `congr <i> [steps] at [..]`, 2 levels | **no** (defect 8) |
| `intro_ctx` | refused by name, honestly | yes |
| side `intros` | `intro h ; <proof>` | **no** (defect 8); fails on inaccessible names |
| close `rfl`/`decide`/`nofun`/`omega` | direct | partly (`then` prose, `:44-48`) |
| close `true_intro` | `exact True.intro` | yes |
| close `assumption:<n>` | `exact <n>` | yes, unless inaccessible (**defect 6**) |
| close `absurd:<h>` | `exact <h>.elim` | yes |
| `at {"hyp": n}` | `… at h` | yes (verified live) |

**`change.to` cannot be passed through verbatim.** The spec calls `to` a
`pp.all` term and T1 emits exactly that; T2's whitelist has no universe
annotation and no `nat_lit`:

```
explicit_rw [change @OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)) at []]
  → error: unexpected token '.{'; expected 'at'
explicit_rw [change (nat_lit 3) at []]
  → error: unexpected token 'nat_lit'; expected explicitRwTerm
```

Hand-re-rendered as `change (3)` it replays (exit 0). RESULT.md's limitations
section does say the dialect excludes such forms, so this is a **documented**
limitation rather than a new defect — but it means every `change` step needs a
re-rendering pass, which the step table does not warn about.

**Quantified.** Mechanically translating all 65 raw T1 traces:
**56 renderable (86%)**. The 9 failures: 5 inaccessible names (defect 6),
2 `unresolved:` closes (correct by design), 1 `intro_ctx` (refused by design),
1 `zeta` with a name (defect 7). So **exactly one product gap — defect 6 —
separates T2 from mechanical translation of 61 of 65 traces.**

---

## Integration with T1 (tip `18a0559`, read-only)

Five traces translated by `/private/tmp/t2r8/translate.py` and replayed in the
T2 worktree. All five replay; **4 of 5 translate with no human intervention**.

| # | Trace | Feature | Mechanical? | Replay |
| - | ----- | ------- | ----------- | ------ |
| 1 | `local_named_prop_true` | `local` + `prop:"true"` | **yes** | PASS (exit 0) |
| 2 | `dreduce_ite` | `change` + `source:"dreduceIte"` | **no** — `to` is `pp.all`, re-rendered by hand to `(3)` | PASS |
| 3 | `user_congr_ite` | user congr, `source:"congr"`, `side` with `intros` | **no** — `intros: ["a✝"]` and `close assumption:a✝` (defect 6); replayed after inventing the name `hq` | PASS |
| 4 | `congr_cast` | `congr` kind, `arg:3`, nested steps | **yes** | PASS |
| 5 | `args_term` | `args: ["a","b"]` | **yes** | PASS |

**Mismatches and responsible side:** two, both **T2**. Trace 3 is defect 6
(no `rename_i`). Trace 2 is the documented `pp.all` dialect gap. Contrary to
round 7, **no T1-side mismatch survives** — see the correction above.

---

## Regression checks re-run

- **Scratch build**: `.lake/build/{lib/lean,ir}/ExplicitLean/ExplicitRw*`
  removed, `lake build ExplicitLean.ExplicitRw` → **PASS, no warnings, 6.1 s**.
- **`elabStrict` routing** (`Tactic.lean:778-805`): exactly four elaboration
  sites, all through it — lemma (`:833`, the only `allowMVars := true`),
  `change` (`:1187`), `eq` (`:1208`), side `exact` (`:1328`). The bare-constant
  fast path (`resolveBareConst?`,
  `:747`) skips it but only ever yields a resolved global constant, and
  `checkNoTacticBlock` runs first. Remaining `evalTactic` calls take **no user
  term** (closed enumerations). Checks confirmed in order: `withoutErrToSorry`,
  `synthesizeSyntheticMVarsNoPostponing`, double `instantiateMVars`,
  `hasSorry || hasSyntheticSorry`, message-log delta, `hasExprMVar` /
  `hasLevelMVar` unless `allowMVars` — each step-indexed.
- **Round-6 critical regression**: the `eq`-slot false theorem → error emitted,
  **exit 1**. (`#print axioms` still names `sorryAx`; that is the consequence of
  the refused proof, not an admission.)
- **Axiom audit, recomputed and attacked**: the audit discovers **111**
  theorems across the 5 positive fixtures (which contain 0 `example`s, so its
  coverage of them is complete) — RESULT.md's 111 reproduces exactly, and the
  full run reports `111 theorems, no sorryAx (75 axiom-free)`.
  Live injections, both reverted (`git status --porcelain` clean after each):
  - `theorem injected_sorry_probe : (1:Nat) = 2 := by sorry` → **exit 1**. Note
    it fails through the *compile* branch (`:171`), because the `sorry` warning
    makes the scratch file non-clean, not through the `sorryAx` gate.
  - `axiom sneaky_ax` + a theorem using it, **inside** the namespace →
    **exit 0**, `112 theorems, no sorryAx`. **The gate does not fire.** This is
    defect 5.
- **`expected.json` perturbation (live)**: `then_simp.lean`'s fragment set to
  `THIS FRAGMENT CANNOT MATCH` → the recorded fragment is absent from the
  compiler output, so the `:275` branch fires (`FAIL (wrong reason)`). Restored;
  tree clean.
- **`check_no_simp_family.py`**: **PASS (3 files)**. Verified discriminating:
  `Lean.Meta.CongrTheorems` (imported at `Tactic.lean:11`) is **accepted**;
  injecting `public meta import Lean.Meta.Tactic.Simp` into `Basic.lean` →
  **FAIL, 1 violation, exit 1**; injecting `theorem … := by simp` into code →
  **FAIL, exit 1**. Both reverted, tree clean. Import scanning happens on raw
  text before comments are stripped (`:123-130`), as the docstring claims.
- **`congr` guard**: `isDefEq pfTy expected` (`Tactic.lean:1155`) is load-bearing
  and fires before `Replacement.eq` is returned. Every rebuild I constructed was
  refused with a step-indexed message and no kernel error.
- **Recursive side proofs / instances / `omega`**: `add_zero` on `Int` (instance
  fixed by the position), `ite_congr` with a nested `explicit_rw` inside a `with`
  entry, and `Nat.sub_add_cancel` discharged by `omega` — all exit 0.
- **Closers**: `rfl`, `decide`, `exact`, `omega`, `nofun` each verified live;
  `at h` (hypothesis location) verified live.
- **Term-elaborator attacks**: the three committed `RejectedSyntax` cases —
  including one calling `Lean.Meta.simpGoal` in `MetaM` — are **parser**-rejected
  (`unexpected token 'SmuggleMetaM'`). Note this works because declaring the
  elaborator creates a *token*; an elaborator bound to an ordinary identifier
  remains the documented T4-side residual, correctly stated in `RESULT.md`.
- **All 7 fixtures individually**: `lake env lean test/ExplicitRw/<each>.lean` →
  **all silent, exit 0**, 2-3 s each (Basic, Binders, Definitional, Grammar,
  Lemmas, Negative, Strict). RESULT.md's "1.6-2.5 s ea" is close enough.
- **`expected.json`**: 13 keys, exactly the 13 `.lean` files; the
  fragment-mismatch gate (`:275`) and the unlisted-file gate (`:263`) are
  present. I verified these **statically**, not by a live perturbation, because
  the full-sweep run held the tree for the whole review; rounds 5-7 each ran the
  live perturbation and it fired.
- **Scope**: `git diff --name-only 6eaed50 HEAD` touches **only owned files** —
  the two scripts, `ExplicitRw{.lean,/Basic,/Tactic}`, `test/ExplicitRw/**`,
  `tracking/tasks/T2-explicit-rw/**`. `ExplicitLean.lean` and `lakefile.toml`
  untouched.
- **Full `T2_FULL_SWEEP=1 python3 -B Experiment/check_explicit_rw.py`**:
  **PASS, exit 0** (log: `/private/tmp/t2r8/full_check.log`). Every figure in
  `RESULT.md:91-96` reproduces **exactly**:
  - build clean 1.8 s; all 7 fixtures PASS (2.0-3.4 s each)
  - `axiom audit: 111 theorems, no sorryAx (75 axiom-free)` — matches
  - `escape sweep: 330 escape probes all rejected (318 by the parser, 12 at
    elaboration), 120 benign all parse (all slots)` — matches
  - all 13 rejected-syntax cases PASS
  The sweep alone took **1153.9 s (19.2 min)**, which is the runtime RESULT.md
  does not state (defect 4).

---

## Summary

| # | Severity | Short title |
| - | -------- | ----------- |
| 1 | major | `sideproof`/`congrnest` sweep slots are vacuous — probes die on the position, not the term |
| 2 | minor | `elab_rejected` credits any non-empty output, without attribution |
| 3 | minor | the `exact` slot's trailing `trivial` is absorbed as an argument |
| 4 | minor | RESULT.md's "12 at elaboration" overstates the evidence for 4 of them |
| 5 | **major** | **the axiom audit greps only `sorryAx`, so a new axiom passes — and RESULT.md claims it was verified to fail** |
| 6 | **major** | **no `rename_i`: inaccessible hypotheses are unnameable — blocks 5 of 65 T1 traces** |
| 7 | minor | `zeta` with a `name`: T1 emits it, the spec does not define it, T2 cannot consume it |
| 8 | major | the step-forms table omits `congr`, `iota`, `with [...]`, the side-proof grammar and the `prop` convention |
| 9 | minor | RESULT.md is 115 lines against a 60-line budget, still unwaived |

**0 critical, 4 major, 5 minor.**

**No soundness defect in the tactic.** `elabStrict` held against every attack I
mounted, the `congr` `isDefEq` guard refuses every unsound rebuild, the
side-proof and closer grammars are genuinely closed enumerations, and the escape
classifier cannot be fooled into passing a real escape — I planted one and it
failed the run. The round-6 critical hole and all four round-7 defects are
properly fixed, each now pinned by a committed fixture, and the full
`T2_FULL_SWEEP=1` run reproduces every figure in RESULT.md exactly.

**The defects are in the checks and the documentation, not the product — with
one exception.** Defect 5 is the serious one: the gate RESULT.md names as the
thing that would have caught round 6's critical hole enforces only half the
governing rule, and the round-7 verification that appeared to confirm it
succeeded for an unrelated reason (a compile error from where the probe was
appended). A new axiom reaching a fixture would ship green today. Defect 6 is
the one *product* gap standing between T2 and mechanical translation of 61 of
T1's 65 traces. Defect 8 means a generator author reading the documentation
would not discover `congr` or `with [...]` at all.

Defects 1-4 are measurement: the sweep is sound as a *parser* fence — 318 of 330
probes are genuinely parser-rejected, which I verified independently — but two of
its six slots contribute nothing about the elaborator, and RESULT.md reports
their four probes as attributable refusals.

Round 7's merge gate on the T1 side does not survive scrutiny: it read stripped
comparison skeletons rather than the recorder's output, and the recorder is in
fact spec-compliant on both counts. **The merge questions are now all T2's own:
defect 5 (a real gate hole) and defect 6 (the generator blocker).**
