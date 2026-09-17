# T3-compliance -- adversarial review round 2

Fresh reviewer; RESULT.md was not trusted. Every claim re-run independently.
Merge-base used: `6eaed5035d8b3caf682d4f3a7db7aee38f72fdb6`.

## Verdict

Round 1's two defects are **genuinely fixed**. Part A (the two replacements),
the splice, the loader wiring and scope are correct; all four Lean files
compile clean. **2 new defects**, both **Low**, both in the same round-1 fix:
`_in_attribute_list` recognises too narrow a set of attribute spellings, so 11
attribute forms that occur in pinned Mathlib are still false positives. No
false negative was found anywhere: nothing that is a real simp-family tactic
escapes the lint.

## Round 1 defects: both confirmed fixed

- **Defect 1 fixed.** `python3 -B Experiment/simp_family_lint.py
  /Users/ptsier/projects/explicit-lean/.lake/packages/mathlib/Mathlib/Order/Concept.lean`
  now reports 13 findings, and line 277 (`attribute [simp] upperPolar_extent
  lowerPolar_intent`) is **not** among them. All 13 are genuine tactic calls
  (`simp_rw` x7, `simp_all`, `simpa` x2, `simp` x3). RESULT.md's correction to
  the round-1 brief -- that this file cannot report zero findings -- is right.
- **Defect 2 fixed.** `check_simp_family_lint.py` is at **38 tests, OK**
  (round 1: 30), and the added cases genuinely pin `attribute [simp]`,
  `attribute [local simp]`, `attribute [scoped simp]`, `attribute [-simp]`,
  `(attr := simp)`, plus two whole-file runs.

## Defects

### 1. Low -- 8 `@[...]` attribute spellings are false positives

`Experiment/simp_family_lint.py:260`. The backward scan accepts only
`" \t\n,-"`, identifier characters and `.`. Any other character inside the
attribute list aborts the scan and the token is reported. Real pinned-Mathlib
attribute lists contain `(`, `)`, `=`, `>`, `<-` and `"`, so the token after
them is flagged. Each line below must be clean and is flagged (1 finding each):

```
@[simp <-, push_cast] theorem t : a = a := rfl          -- stops at '<-'
@[push <-, simp] theorem t : a = a := rfl               -- stops at '<-'
@[grind =>, simp] lemma t : a = a := rfl                -- stops at '>'
@[simp, grind =, norm_cast] theorem t : a = a := rfl    -- stops at '='
@[aesop (rule_sets := [finiteness]) safe apply, simp] theorem t : a = a := rfl
@[deprecated "use X" (since := "2026-02-21"), norm_cast] theorem t : a = a := rfl
@[to_dual self (reorder := f g, hf hg), simp] theorem t : a = a := rfl
```

Note `@[simp <-]` alone is clean (the arrow is *after* `simp`); the bug needs a
token to the right of the offending character. Reproduce:

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T3-compliance
printf '@[push \xe2\x86\x90, simp] theorem t : a = a := rfl\n' | python3 -B Experiment/simp_family_lint.py
```

### 2. Low -- 3 `attribute` command spellings are false positives

`Experiment/simp_family_lint.py:291-294`. `_opens_attribute_list` requires the
`attribute` keyword to be preceded only by spaces/tabs back to a newline, so
any prefix modifier defeats it. These are all real Lean commands, must be
clean, and are flagged:

```
local attribute [simp] foo
scoped attribute [simp] foo
scoped[Pointwise] attribute [simp] Set.image_smul     -- occurs in pinned Mathlib
open Foo in attribute [simp] foo
```

Reproduce:

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T3-compliance
printf 'scoped[Pointwise] attribute [simp] Set.image_smul\n' | python3 -B Experiment/simp_family_lint.py
```

The command-position guard itself is right and must be kept: `exact foo
attribute [simp]` is still correctly flagged, and so is a tactic on a later
line after an attribute line.

### Scale of defects 1 and 2, and why Low

A sweep of all **8264** pinned Mathlib files classifying every finding by
whether it sits inside an attribute bracket gives **18** true false positives
in **13** distinct spellings (`scoped[NS] attribute [simp]` x4,
`@[aesop (rule_sets := [...]) safe apply, simp]` x4, `@[simp, grind =,
norm_cast]` x2, `@[simp <-, push_cast]` x2, and one each of `@[push <-, simp]`,
`@[grind =>, simp]` x2, `@[deprecated ... (since := ...), norm_cast]`,
`@[to_dual self (reorder := ...), simp]`). Severity stays **Low** for the same
reason as round 1: the only production call site is
`Experiment/simp_manual_overrides.py:175`, which lints replacement snippets,
where attribute syntax cannot appear. It blocks whole-file gating later, which
is exactly what `_in_attribute_list`'s docstring (`:216`, "the forms that
actually occur in pinned Mathlib") promises to support.

### 3. Low -- none of the 11 spellings above is tested

`Experiment/check_simp_family_lint.py:157-207` pins only the unprefixed forms.
`grep -c` over that file: `local attribute` 0, `scoped attribute` 0, `scoped[`
0, `in attribute` 0, `grind` 0, `aesop` 0, `deprecated` 0, `to_dual` 0. This is
the round-1 defect-2 pattern repeating one level out: the fix was pinned only
for the spellings the round-1 reviewer happened to name.

## Attacks that found nothing (evidence)

1. **Attribute recognition, 38 hand-built cases.** Everything the brief asked
   for behaves correctly except defects 1-2: `attribute [simp] foo` at line
   start, after `in` on its own line, indented in a namespace, split across two
   lines (`attribute [\n  simp] foo`), `attribute [local simp, norm_cast] foo
   bar`, `attribute [-simp]`, `attribute [scoped simp]`, `@[simp high]`,
   `@[simp <-]`, `@[simp, aesop safe]`, `@[to_additive (attr := simp)]`,
   `@[simps]` -- all clean.
2. **No false negatives.** All of these are still flagged: `exact foo
   attribute [simp]`, `have := by simp`, `. simp`, `simp <;> rfl`, `(simp)`,
   `simp;`, bare `simp\n`, `fun _ => by simp`, `decreasing_by simp`,
   `termination_by`+`decreasing_by simp`, `simp_all?`, `simp only []`,
   `dsimp!`, `simp_arith`, `simpa?`, `norm_num`, `push_cast`, `dsimp only [f]`,
   `conv => simp`.
3. **`@[simp] lemma ... := by simp` flags the tactic only.** One finding, at
   column 31 -- the `by simp`, not the attribute. Same for `@[simp] theorem
   ... := by simp only [x]` (one finding, column 33).
4. **Identifier adjacency.** `simp'`, `simp''`, `simp.foo`, `simple`,
   `Nat.simp_foo`, `Simp.Config.default` are all clean. Multi-byte: `simpa`
   (Greek alpha) clean, because `_IDENT_BODY` covers Greek. `simpN` (U+2115),
   `simp1` (subscript), `simp<<`, `simp` + Hebrew/CJK/emoji are flagged, since
   those code points fall outside `_IDENT_BODY`'s `A-Za-z0-9_'A-yA-!?` ranges.
   Lean would treat `simpN` as one identifier, so these are technically false
   positives too. I do **not** raise them as a defect: no such identifier
   exists in pinned Mathlib (every `simp`+non-ASCII occurrence there is a
   delimiter such as `simp>`, `simp<-` or a backtick, never an identifier
   continuation), and round 1 explicitly accepted `simp1`/`simp<<` as flagged.
   Widening `_IDENT_BODY` would risk false negatives for no real gain.
5. **Loader path, fresh violating databases.** Built a temp DB per case from
   the real JSON and called `load_database`. **All rejected**: `rfl <;> simp`,
   `exact h <;> dsimp only [f]` (the `<;>`-hidden cases the brief asked for),
   `norm_num`, `intro h\n  norm_num [foo]`, `push_cast\n  ring`,
   `dsimp only [f]`, `conv => simp`, `simpa using h`, `constructor <;> intro h
   <;> simp_all`, `exact h\n  norm_cast`, `field_simp`. Three of them
   (`dsimp only`, `norm_cast`, `<;> dsimp only`) are caught **only** by the new
   lint, not by the pre-existing `BANNED_SEARCH_PATTERN`, so the wiring adds
   real coverage. A clean replacement still loads.
6. **Splice reproducibility, verified by regenerating.** `python3 -B
   test/Compliance/splice.py` rewrites all four files; SHA-256 of each is
   unchanged and `git status --porcelain` is empty, so RESULT.md's
   byte-identical claim holds. The two control files hash to exactly the
   `moduleSourceSha256` recorded in the JSON. `diff control replacement`
   differs **only** in the tactic block for both pairs (Unitization line 268,
   EpiMono line 243); no `sorry`/`admit`.
7. **Lean compiles.** `lake env lean` on all four `test/Compliance/*.lean`:
   rc=0 with **zero** bytes of output each (no errors, no warnings),
   3.8-4.4 s wall and 0.87-0.93 GB peak RSS.
8. **JSON minimality and scope.** `git diff <merge-base>` changes exactly the
   two `replacement` strings and nothing else in the JSON. All **11** changed
   paths are task-owned; `Experiment/manual_overlay.py` is genuinely
   **unmodified**, consistent with RESULT.md's statement that
   `simp_manual_overrides.load_database` is the real chokepoint.
9. **Lint over the shipped database.** 21 entries, **0** findings, no `erw`,
   and all 21 `source` fields still contain a simp-family token.
10. **RESULT.md honesty (58 lines, within the 60 cap): accurate.** The "all
    1385 pinned files containing `attribute [`" figure is exactly right
    (`grep -rl "attribute \[" Mathlib --include='*.lean' | wc -l` = 1385).
    The 38/6-test counts, the 21-entry/0-finding line and the byte-identical
    splice claim all reproduce. The "0 attribute-derived findings" sweep claim
    is the one overstatement: it is true for the unprefixed `attribute [`
    spellings it tested, but 18 attribute-bracket false positives remain
    (defects 1-2), so that line should be narrowed when the fix lands.

## Checks run

| Check | Result |
| --- | --- |
| `python3 -B Experiment/check_simp_family_lint.py` | PASS, 38 tests, 0.02 s |
| `python3 -B Experiment/check_manual_overlay.py` | PASS, 6 tests, 0.01 s |
| `python3 -B Experiment/check_simp_manual_overrides.py` | PASS, rc=0 (Lean) |
| `lake env lean` x4 `test/Compliance/*.lean` | PASS, rc=0, no output |
| `python3 -B test/Compliance/splice.py` + `git status` | PASS, byte-identical |
| Lint over all 21 replacements | 21 entries, 0 findings |
| Loader rejection, 11 violating temp DBs | PASS, all rejected |
| Sweep of 8264 pinned Mathlib files | 18 attribute false positives |

**Pre-existing failure re-confirmed independently.** RESULT.md discloses that
`check_simp_manual_composition.py` fails for a reason T3 does not own. I ran it
in the **untouched main checkout** (`/Users/ptsier/projects/explicit-lean`,
which contains none of T3's changes): rc=1, "manual simp composition failed:
generated renderer continuation indentation leaves no line budget" -- the exact
message RESULT.md reports. Confirmed not a T3 defect.

**All six dependent checks have now completed.** The set was found by `grep
-rln -E "simp_manual_overrides|manual_overlay|simp_family_lint"
Experiment/check_*.py`. Five pass; the sixth is the disclosed pre-existing
failure above:

| Dependent check | Result |
| --- | --- |
| `check_simp_family_lint.py` | PASS, 38 tests |
| `check_manual_overlay.py` | PASS, 6 tests |
| `check_simp_manual_overrides.py` | PASS, rc=0, "manual simp overrides: passed" |
| `check_campaign_supervisor_v10.py` | PASS, 22 tests, 0.74 s |
| `check_campaign_worker.py` | PASS, 33 tests, 0.76 s |
| `check_simp_manual_composition.py` | FAIL, rc=1 -- pre-existing, see above |

`check_simp_manual_overrides.py` is the one that actually exercises
`load_database` against the shipped JSON and re-elaborates the patched modules,
so the loader wiring is confirmed end to end on the real database.
