# T3-compliance result

Status: complete. Branch `task/T3-compliance`.

## Part A: the two `dsimp` overrides

Both pinned files matched their recorded `moduleSourceSha256` before any work.

- `Mathlib/Algebra/Algebra/Subalgebra/Unitization.lean`, `1734864b48394331`.
  Goal is `((StarAlgebra.adjoin R ↑s).subtype.comp starAlgHom) ↑x = ↑x`;
  `dsimp [starAlgHom]` unfolded the let-bound local to
  `(algebraMap R A) 0 + ↑x = ↑x`. New replacement:
  `show (algebraMap R A) 0 + _ = _` / `rw [map_zero]` / `exact zero_add _`.
  The `show` reaches that goal definitionally, so no simp engine is involved.
  A single `rw [map_zero, zero_add]` fails (the `zero_add` rewrite also fires
  on the RHS), hence the closing `exact`.
- `Mathlib/Algebra/Category/Grp/EpiMono.lean`, `3251bc59333b0c31`. New
  replacement: `rw [Equiv.coe_trans, Equiv.coe_trans, Function.comp_apply,
  Function.comp_apply]` / `unfold tau`. Reaches exactly the goal the original
  `dsimp only [...]` produced, verified with `trace_state` on both sides.

No `erw` and no simp-family tactic. `source`, byte ranges, occurrence ids,
digests and the JSON schema are unchanged; no other entry was touched.

`test/Compliance/splice.py` regenerates all four Lean copies from the pinned
sources, re-checking the sha and byte range each time, so the compile check is
repeatable. Copies are whole-file and keep the `module` header and
`public import` lines.

## Part B: the lint

- `Experiment/simp_family_lint.py`: `findings`, `has_simp_family`,
  `assert_clean`, `format_findings`, and a CLI (`--quiet`; exit 1 on a
  finding). It masks nested block comments, line comments (including the
  retained `-- Original simp:` lines) and string/char/raw/interpolated
  literals, then tokenises, growing each candidate to a full dotted identifier
  and skipping `@[...]` attribute lists.
- Loader wiring: the function that reads the JSON is
  **`simp_manual_overrides.load_database`**, not `manual_overlay.py`.
  `manual_overlay` delegates to it on every path, so the one call added there
  covers both; `manual_overlay.py` is unmodified. The pre-existing
  `BANNED_SEARCH_PATTERN` omits `dsimp`, `push_cast` and `norm_cast`; it was
  left in place and the lint runs alongside it.

## Checks (all run in the worktree)

| Check | Result |
| --- | --- |
| `lake env lean` on both `*_control.lean` | PASS, 4s / 5s, peak RSS < 1 GB |
| `lake env lean` on both `*_replacement.lean` | PASS, 4s / 5s |
| Overlay-rendered modules (with `-- Original simp:` blocks) compiled | PASS |
| `python3 -B Experiment/check_simp_family_lint.py` | PASS, 30 tests |
| `python3 -B Experiment/check_manual_overlay.py` | PASS, 6 tests |
| `python3 -B Experiment/check_simp_manual_overrides.py` | PASS |
| Lint over all 21 replacements | 21 entries, **0 findings** |

## Known limitations / open questions

- `Experiment/check_simp_manual_composition.py` reports "generated renderer
  continuation indentation leaves no line budget". **Pre-existing, not mine**:
  it fails identically on the untouched main checkout at `6eaed50`. Source is
  `_format_generated_line` in `check_simp_engine_boundary_source.py`, which I
  do not own. Flagged for the coordinator, not fixed here.
- The lint treats `@[simp]` / `@[simps]` as declaration attributes rather than
  findings, matching the rule's scope (executable code). Barring overrides from
  *adding* simp attributes would be a separate rule.
