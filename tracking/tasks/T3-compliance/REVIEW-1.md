# T3-compliance -- adversarial review round 1

Reviewer re-ran every check independently; RESULT.md claims were not trusted.
Merge-base used: `6eaed5035d8b3caf682d4f3a7db7aee38f72fdb6`.

## Verdict

2 defects, both **Low**. No High or Medium defect found. Part A (the two
replacements) and the loader wiring are correct and the claims in RESULT.md
that I could test are accurate.

## Defects

### 1. Low -- `attribute [simp] foo` is a false positive

`Experiment/simp_family_lint.py:210` (`_in_attribute_list`) only recognises the
`@[...]` form. The standalone `attribute [simp] ...` command and the
`(attr := simp)` form are attribute *declarations*, not tactic calls, but are
flagged. Per the governing rule (`AGENTS.md`, "Forbidden in generated or
override code" covers tactics/term elaborators) and the reasoning RESULT.md
itself gives for `@[simp]`, generated Mathlib files must keep their original
attributes, so these are false positives of the same class the author already
decided to exclude.

Failing scenario (real pinned Mathlib source, not synthetic):

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T3-compliance
python3 -B Experiment/simp_family_lint.py \
  /Users/ptsier/projects/explicit-lean/.lake/packages/mathlib/Mathlib/Order/Concept.lean
```

reports `line 277, column 12: simp ('attribute [simp] upperPolar_extent
lowerPolar_intent')`. Minimal inputs that reproduce:

- `attribute [simp] Foo.bar`            -> flagged (should be clean)
- `attribute [local simp] foo`          -> flagged (should be clean)
- `attribute [-simp] foo`               -> flagged; `-simp` *removes* the
  attribute, so this is doubly wrong
- `@[to_additive (attr := simp)] theorem t : a = a := rfl` -> flagged

`attribute [...simp...]` occurs in 449 pinned Mathlib files
(`grep -rl "attribute \[.*simp" .lake/packages/mathlib/Mathlib | wc -l`), so
this blocks using the lint as a whole-file gate later.

Severity is Low, not Medium, only because the lint is currently invoked on
replacement snippets alone (`Experiment/simp_manual_overrides.py:175` is the
sole production call site; verified by
`grep -rn simp_family_lint Experiment/ test/`), where the `attribute` command
cannot appear. It becomes a blocker the moment the lint is pointed at rendered
files. No false negative was found (see below), so this is the only accuracy
gap.

### 2. Low -- the gap in defect 1 is untested

`Experiment/check_simp_family_lint.py:153`
(`test_simp_attribute_is_not_a_tactic_call`) pins only the `@[simp]` and
`@[simp, norm_cast]` spellings. Nothing covers `attribute [simp]`,
`attribute [local simp]`, `attribute [-simp]` or `(attr := simp)`, which is why
defect 1 survived a 30-test suite that otherwise passes. Add these cases with
the fix so the behaviour is pinned either way.

## Attacks that found nothing (evidence)

1. **JSON minimality.** `git diff <merge-base> task/T3-compliance --
   Experiment/simp_manual_overrides.json` changes exactly two `replacement`
   strings and nothing else. `source`, `module`, `moduleSourceSha256`,
   `occurrence`, `startByte`, `endByte` and all 19 other entries are
   byte-identical. No `erw`, no simp-family tactic in either new replacement.
2. **Scope.** All 10 changed paths are owned by the task. `manual_overlay.py`
   is genuinely unmodified; the loader (`simp_manual_overrides.load_database`)
   is the real chokepoint and `manual_overlay.py:278` delegates to it, so the
   single call site does cover both, as RESULT.md states.
3. **Splice fidelity.** Re-ran `python3 -B test/Compliance/splice.py`: the four
   committed files regenerate **byte-identically** (`git status` clean), which
   proves the recorded `startByte`/`endByte` and sha were used exactly.
   `diff <control> <replacement>` differs only in the tactic block for both
   pairs, so the spliced copy proves the same theorem statement as the control.
   Indentation is preserved and the replacement stays inside the original
   tactic block: the Unitization continuation lines align under `by` inside the
   `·` bullet, and `unfold tau` sits at the same 2-space level in EpiMono.
4. **Lean compiles.** `lake env lean` on all four `test/Compliance/*.lean`:
   rc=0 with **zero** bytes of output (no errors, no warnings), ~3.5-4.6e9
   cycles and peak RSS ~133 MB each. No `sorry`/`admit` anywhere.
5. **Loader rejection.** Constructed temp databases with a violating first
   entry; `load_database` raised `RuntimeError` for every one of `dsimp only
   [f]`, `simp`, `conv => simp`, `push_cast`, `norm_num`, `exact (by simpa
   using h)`. `dsimp only [f]` and `push_cast` are caught by the new lint
   specifically -- the pre-existing `BANNED_SEARCH_PATTERN` misses them -- so
   the wiring adds real coverage. No reader bypasses it: the other readers
   (`boundary_materialize_shard.py`, `simp_engine_boundary_corpus.py`,
   `verify_simp_boundary_manifest.py`) go through `load_database` or only hash
   and schema-check the file.
6. **Lint false negatives: none.** All 37 positives caught, including
   `simp only [..]`, `simpa using h`, `simp_all`, `simp_rw`, `dsimp only`,
   `norm_num`, `field_simp`, `push_cast`, `norm_cast`, `simp?`, `simp!`,
   `simp_arith`, `simp_wf`, `simp at h ⊢`, `<;> simp`, `by simp`, `(simp)`,
   `intro h; simp`, `conv => simp`, `conv_lhs => simp`, `first | simp | rfl`,
   `try simp`, `all_goals simp`, `simp (config := ..)`, `simp +arith`,
   `exact (by simp?)`, `· simp`, `omega <;> dsimp only [f]`, and the unicode
   cases `simp₁` / `simp«`.
7. **Lint false positives: only defect 1.** Correctly clean on
   `nlinarith [sq_nonneg x]`, `decide`, `Simp.Config`, `@[simp]`, `@[simps]`,
   `@[simp, norm_cast]`, `simple`, `simp_lemma`, `rw [Nat.simp_foo]`, string
   literals, line comments, retained `-- Original simp:` lines, nested block
   comments `/- /- simp -/ -/` and doc comments `/-- simp -/`.
8. **Checks.** `check_simp_family_lint.py` 30 tests OK;
   `check_manual_overlay.py` 6 tests OK; `check_simp_manual_overrides.py`
   passed. Lint over the fixed database: 21 entries, **0 findings** (and all 21
   `source` fields still contain simp, as expected).
9. **RESULT.md honesty: verified.** The pre-existing-failure claim is true and
   I checked it more strictly than claimed: `check_simp_manual_composition.py`
   fails with the identical message "generated renderer continuation
   indentation leaves no line budget" in the worktree, in the main checkout
   (now at `1a667cb`), **and** in a detached worktree at the exact merge-base
   `6eaed50`. Not a T3 defect. Every other check result in the table
   reproduced. The `@[simp]` limitation is disclosed honestly, though the
   disclosure does not mention the `attribute [simp]` form of defect 1.
