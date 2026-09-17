# T23 — deterministic local handles

Implemented in `/Users/ptsier/projects/explicit-lean-worktrees/T23-local-handles`
from `3953012ca54634beb2e8b63fec0f5d84925edd2c`.

## Surface and semantics

- `local_ref N` resolves one declaration by direct `LocalDecl.index` access;
  missing slots, auxiliary declarations, type mismatches, and invalid/out of
  bounds structure projections fail explicitly.  Numeric suffixes are
  1-indexed (`.1`, `.2`, and chains).
- `intro_ref N ; ...` introduces exactly one binder and binds the closed
  `introduced_ref N` term to that binder.  Handles are ordered, scoped to the
  recursive side proof, and reject unknown or duplicate IDs.
- The custom terms are guarded by an option enabled only by `explicit_rw` and
  are not ordinary readable Lean terms outside the tactic.

## Fixtures and checks

`LocalHandles.lean` has 7 positive cases: exact index, projection, nested
side-intro, inaccessible binder, and ordinary compatibility coverage.
`LocalHandlesNegative.lean` has 8 guarded failures: bounds, declaration kind,
invalid/out-of-bounds projections, type mismatch, unknown handle, duplicate
handle, and outside-`explicit_rw` use.

- `python3 -B Experiment/check_no_simp_family.py` — PASS (4 files).
- `python3 -B Experiment/check_explicit_rw.py` — run for the final report.
- `lake build ExplicitLean.ExplicitRw` — PASS (warning-free).

No recorder, pipeline, axioms, or simp-family code was changed.
