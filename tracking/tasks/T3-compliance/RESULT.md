# T3-compliance result

Status: complete, rounds 1-2 defects fixed. Branch `task/T3-compliance`.

## Parts A and B (clean in both reviews; shas matched before work)

- `Unitization.lean`, `1734864b48394331`: `dsimp [starAlgHom]` unfolded a
  let-bound local to `(algebraMap R A) 0 + ↑x = ↑x`. Replaced by
  `show (algebraMap R A) 0 + _ = _` / `rw [map_zero]` / `exact zero_add _`; a
  one-step `rw [map_zero, zero_add]` fails (`zero_add` also fires on the RHS).
- `EpiMono.lean`, `3251bc59333b0c31`: replaced by `rw [Equiv.coe_trans,
  Equiv.coe_trans, Function.comp_apply, Function.comp_apply]` / `unfold tau`.

No `erw`, no simp-family tactic; `source`, byte ranges, ids, digests and schema
unchanged. The JSON loader is **`simp_manual_overrides.load_database`**, which
`manual_overlay.py` delegates to, so one call there covers both.

**Round 1 fixes (confirmed fixed by round 2):** `_in_attribute_list` gained the
`attribute [...]` command and `(attr := simp)`; 8 tests added (30 -> 38). Its
sweep line claimed "0 attribute-derived findings" over the 1385 files with
`attribute [` -- **too broad**: true only for unprefixed lines; round 2 found 18.

## Round 2 fixes

All three were real. Attribute context is now **structural** rather than a
backward character scan: the lint matches delimiters backwards to the enclosing
bracket group (`_enclosing_bracket`, over comment- and string-masked text) and
asks whether it is an attribute list, resolving outwards through nested groups.
It never inspects characters *between* delimiters, so arbitrary attribute
arguments work by construction.

- **Defects 1-2 (11 spellings).** Clean on `@[simp <-, push_cast]`,
  `@[push <-, simp]`, `@[grind =>, simp]`, `@[simp, grind =, norm_cast]`,
  `@[aesop (rule_sets := [finiteness]) safe apply, simp]`, `@[deprecated "..."
  (since := "..."), norm_cast]`, `@[to_dual self (reorder := ...), simp]`, and
  `local`/`scoped`/`scoped[NS]`/`open ... in` before `attribute`. The
  command-position guard holds: `exact foo attribute [simp]` is still flagged.
- **Defect 3 (untested).** 8 tests added (38 -> 46): one per spelling above,
  nested groups, split lists, prefixes not shielding a tactic, corpus sweep.

Corpus evidence: over **all 8264** pinned files, **0** of 124,182 findings are
attribute-derived (round 2: 18). A differential run of old vs new lint shows
exactly those **18** became clean and **0** newly flagged, so no false negative.
Running the sweep's oracle against the *old* lint reproduces 18, so the test is
a real regression test, not a tautology.

## Checks (all re-run after the round 2 fix)

| Check | Result |
| --- | --- |
| `lake env lean` on all 4 `test/Compliance/*.lean` | PASS, 4-5s, RSS < 1 GB |
| `check_simp_family_lint.py` (fast suite) | PASS, 46 tests, 0.04 s |
| `check_simp_family_lint.py --sweep` (8264 files) | PASS, 46 tests, 304 s |
| `check_manual_overlay.py`; `check_simp_manual_overrides.py` | PASS, 6; PASS |
| `splice.py` regen; lint over 21 replacements | byte-identical; **0 findings** |

**Known limitation (pre-existing, not T3's):** `check_simp_manual_composition.py`
fails with "generated renderer continuation indentation leaves no line budget",
identical on the untouched main checkout at `6eaed50`, from
`_format_generated_line` in a file T3 does not own.
