# T3-compliance result

Status: complete. Branch `task/T3-compliance`, worktree
`/Users/ptsier/projects/explicit-lean-worktrees/T3-compliance`.

## Part A: the two `dsimp` overrides

Both pinned files matched their recorded `moduleSourceSha256` before any work.

- `Mathlib/Algebra/Algebra/Subalgebra/Unitization.lean`, occurrence
  `1734864b48394331`. Goal at the call site is
  `((StarAlgebra.adjoin R ↑s).subtype.comp starAlgHom) ↑x = ↑x`; `dsimp
  [starAlgHom]` unfolded the let-bound local to `(algebraMap R A) 0 + ↑x = ↑x`.
  New replacement: `show (algebraMap R A) 0 + _ = _` / `rw [map_zero]` /
  `exact zero_add _`. The `show` reaches the same goal definitionally, so no
  simp engine is involved. `rw [map_zero, zero_add]` in one step fails (the
  `zero_add` rewrite also fires on the RHS), which is why the closing step is
  an `exact`.
- `Mathlib/Algebra/Category/Grp/EpiMono.lean`, occurrence `3251bc59333b0c31`.
  New replacement: `rw [Equiv.coe_trans, Equiv.coe_trans, Function.comp_apply,
  Function.comp_apply]` / `unfold tau`. This reaches exactly the goal the
  original `dsimp only [tau, Equiv.coe_trans, Function.comp_apply]` produced,
  verified by `trace_state` on both sides.

Neither replacement uses `erw` or any simp-family tactic. `source`, byte
ranges, occurrence ids, digests and the JSON schema are unchanged; no other
entry was touched.

`test/Compliance/splice.py` regenerates all four Lean copies from the pinned
Mathlib sources, re-checking the recorded sha and the byte range each time, so
the compile check is repeatable. The copies are whole-file and keep the
original `module` header and `public import` lines.

## Part B: the lint

- `Experiment/simp_family_lint.py`: `findings`, `has_simp_family`,
  `assert_clean`, `format_findings`, plus a CLI (`--quiet`; exit 1 on any
  finding). It masks nested block comments, line comments (including the
  retained `-- Original simp:` lines), string/char/raw/interpolated literals,
  then tokenises, growing each candidate to a full dotted identifier and
  skipping `@[...]` attribute lists.
- Loader wiring: the function that actually reads the JSON is
  **`simp_manual_overrides.load_database`**, not `manual_overlay.py`.
  `manual_overlay` delegates to it for every path, so the single call added
  there covers both. The pre-existing `BANNED_SEARCH_PATTERN` omits `dsimp`,
  `push_cast` and `norm_cast`; it was left in place and the lint runs
  alongside it. No other `manual_overlay.py` behaviour changed (the file is in
  fact unmodified).

## Checks (all run in the worktree)

| Check | Result |
| --- | --- |
| `lake env lean` on both `*_control.lean` | PASS, 4s / 5s, peak RSS < 1 GB |
| `lake env lean` on both `*_replacement.lean` | PASS, 4s / 5s |
| Full `manual_overlay` rendering of both modules (with the `-- Original simp:` comment blocks) compiled | PASS |
| `python3 -B Experiment/check_simp_family_lint.py` | PASS, 30 tests |
| `python3 -B Experiment/check_manual_overlay.py` | PASS, 6 tests |
| `python3 -B Experiment/check_simp_manual_overrides.py` | PASS |
| Lint over all 21 replacements | 21 entries, **0 findings** |

## Known limitations / open questions

- `Experiment/check_simp_manual_composition.py` reports "generated renderer
  continuation indentation leaves no line budget". **Pre-existing and not mine**:
  it fails identically on the untouched main checkout at `6eaed50`. It comes
  from `_format_generated_line` in `check_simp_engine_boundary_source.py`,
  which I do not own. Flagging for the coordinator, not fixed here.
- The lint treats `@[simp]` and `@[simps]` as declaration attributes, not
  findings, matching the governing rule's scope (executable code). If override
  entries should ever be barred from *adding* simp attributes, that is a
  separate rule and a separate change.
