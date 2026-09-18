# T40 — fix Function.Defs and Logic.Basic compile failures

Added authenticated ordinary-Lean source overrides for the three non-
`Function.Basic` failures from the fresh T37 report:

- `Mathlib/Logic/Function/Defs.lean`, site 1 (`Injective.beq_eq`): prove the
  Boolean equality equivalence through `Bool.eq_iff_iff`, `beq_iff_eq`, and
  `Injective.eq_iff`.
- `Mathlib/Logic/Basic.lean`, site 4 (`xor_iff_not_iff'`): direct `rw`.
- `Mathlib/Logic/Basic.lean`, site 10 (`Decidable.and_forall_ne`): direct
  constructor proof with an equality case split.

The original source calls remain adjacent comments through the manual-overlay
renderer. The replacements contain no simp-family tactic, search tactic,
`sorry`, or serialized term payload. The manual override and lint checkers now
expect the expanded 26-entry database.

Checks:

- Both patched source overlays compile with `lake env lean`.
- `python3 -B Experiment/pipeline/check_pipeline.py` — PASS (307 checks; the
  existing Nontrivial.Defs render-failed measurement remains reported by the
  harness).
- `python3 -B Experiment/check_simp_family_lint.py` — PASS (46 tests, 2
  opt-in sweep tests skipped).
- Manual database load and source-range validation — PASS (26 entries).

Replay gain: 3 previously failing sites now compile, across 2 modules; both
patched modules compile as complete source overlays.
