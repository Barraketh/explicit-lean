# T3-compliance result

Status: complete. Branch `task/T3-compliance`. Both pinned files matched their
recorded `moduleSourceSha256` before any work.

## Part A: the two `dsimp` overrides

- `Mathlib/Algebra/Algebra/Subalgebra/Unitization.lean`, `1734864b48394331`:
  `dsimp [starAlgHom]` unfolded the let-bound local, turning
  `((StarAlgebra.adjoin R ↑s).subtype.comp starAlgHom) ↑x = ↑x` into
  `(algebraMap R A) 0 + ↑x = ↑x`. New replacement:
  `show (algebraMap R A) 0 + _ = _` / `rw [map_zero]` / `exact zero_add _` --
  the `show` gets there definitionally; `rw [map_zero, zero_add]` in one step
  fails because `zero_add` also fires on the RHS.
- `Mathlib/Algebra/Category/Grp/EpiMono.lean`, `3251bc59333b0c31`: replaced by
  `rw [Equiv.coe_trans, Equiv.coe_trans, Function.comp_apply,
  Function.comp_apply]` / `unfold tau`, which reaches exactly the goal the
  original `dsimp only [...]` produced (verified with `trace_state` both ways).

No `erw` and no simp-family tactic. `source`, byte ranges, occurrence ids,
digests and the JSON schema are unchanged; no other entry was touched.
`test/Compliance/splice.py` regenerates all four whole-file Lean copies from
the pinned sources, re-checking the sha and byte range each time.

## Part B: the lint

- `Experiment/simp_family_lint.py` exports `findings`, `has_simp_family`,
  `assert_clean`, `format_findings`, and a CLI (`--quiet`; exit 1 on a
  finding). It masks nested block comments, line comments (including retained
  `-- Original simp:` lines) and string/char/raw/interpolated literals, then
  tokenises, growing each candidate to a full dotted identifier (so `simple`,
  `Simp.Result` and `simp_lemma_name` miss) and skipping `@[...]` lists.
- Loader wiring: the function that reads the JSON is
  **`simp_manual_overrides.load_database`**, not `manual_overlay.py`, which
  delegates to it on every path -- so the one call added there covers both and
  `manual_overlay.py` is unmodified. The pre-existing `BANNED_SEARCH_PATTERN`
  omits `dsimp`/`push_cast`/`norm_cast`; it was left in place and the lint runs
  alongside it.

## Checks (all run in the worktree)

| Check | Result |
| --- | --- |
| `lake env lean` on all 4 `test/Compliance/*.lean` (2 controls, 2 spliced) | PASS, 4-5s each, peak RSS < 1 GB |
| Overlay-rendered modules (with `-- Original simp:` blocks) compiled | PASS |
| `python3 -B Experiment/check_simp_family_lint.py` | PASS, 30 tests |
| `python3 -B Experiment/check_manual_overlay.py` | PASS, 6 tests |
| `python3 -B Experiment/check_simp_manual_overrides.py` | PASS |
| Lint over all 21 replacements | 21 entries, **0 findings** |

## Known limitations / open questions

- `Experiment/check_simp_manual_composition.py` reports "generated renderer
  continuation indentation leaves no line budget". **Pre-existing, not mine**:
  it fails identically on the untouched main checkout at `6eaed50`, from
  `_format_generated_line` in `check_simp_engine_boundary_source.py`, which I
  do not own. Flagged for the coordinator, not fixed here.
- The lint treats `@[simp]` / `@[simps]` as declaration attributes, not
  findings, matching the rule's scope (executable code). Barring overrides from
  *adding* simp attributes would be a separate rule.
