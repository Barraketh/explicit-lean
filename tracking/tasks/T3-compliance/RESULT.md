# T3-compliance result

Status: complete, round 1 defects fixed. Branch `task/T3-compliance`.

## Parts A and B (verified clean in round 1; shas matched before any work)

- `Unitization.lean`, `1734864b48394331`: `dsimp [starAlgHom]` unfolded a
  let-bound local to `(algebraMap R A) 0 + ↑x = ↑x`. Replaced by
  `show (algebraMap R A) 0 + _ = _` / `rw [map_zero]` / `exact zero_add _`; a
  one-step `rw [map_zero, zero_add]` fails (`zero_add` also fires on the RHS).
- `EpiMono.lean`, `3251bc59333b0c31`: replaced by `rw [Equiv.coe_trans,
  Equiv.coe_trans, Function.comp_apply, Function.comp_apply]` / `unfold tau`.

No `erw`, no simp-family tactic; `source`, byte ranges, ids, digests and the
schema unchanged. `splice.py` regenerates all four whole-file copies, checking
the sha and byte range. The JSON loader is
**`simp_manual_overrides.load_database`**, not `manual_overlay.py`, which
delegates to it, so the one call added there covers both.

## Round 1 fixes (both real; both fixed and pinned by tests)

- **Defect 1 (attribute false positives).** `_in_attribute_list` recognised
  only `@[...]`. It now also recognises the `attribute [...]` command (required
  to be in command position, so `exact foo attribute [simp]` is still flagged)
  and `(attr := simp)`, and tolerates the `-` of `[-simp]`. Clean on
  `attribute [simp|local simp|scoped simp|-simp] foo`, `(attr := simp)`,
  `@[simp]`, `@[simp, norm_cast]`, `@[local simp]`, `@[simps]`.
- **Defect 2 (untested).** `check_simp_family_lint.py` grew 8 tests (30 -> 38):
  one per attribute form above, plus the two whole-file runs.

Extra verification: swept **all 1385** pinned Mathlib files containing
`attribute [` -- **0** attribute-derived findings; a differential run of old vs
new lint over 300 random files shows only attribute-line findings disappeared
and no new ones appeared, so no false negative.

**One correction to the brief:** the run over `Mathlib/Order/Concept.lean`
**cannot** report zero findings -- it has 13 genuine simp tactic calls; the
reviewer cited it only as the reproduction for the `attribute [simp]` on line
277. The test asserts the right property instead: line 277 is not reported and
no finding comes from any attribute line. The hand-written test asserts
exactly one finding, as asked.

## Checks (all re-run in the worktree after the fix)

| Check | Result |
| --- | --- |
| `lake env lean` on all 4 `test/Compliance/*.lean` | PASS, 4-5s, RSS < 1 GB |
| Overlay-rendered modules (with `-- Original simp:`) | PASS |
| `check_simp_family_lint.py` / `check_manual_overlay.py` | PASS, 38 / 6 tests |
| `check_simp_manual_overrides.py`; `splice.py` regen | PASS; byte-identical |
| Lint over all 21 replacements | 21 entries, **0 findings** |

## Known limitations (pre-existing, not introduced by T3)

`check_simp_manual_composition.py` fails with "generated renderer continuation
indentation leaves no line budget" -- identical on the untouched main checkout
at `6eaed50`, from `_format_generated_line` in
`check_simp_engine_boundary_source.py`, which T3 does not own.
