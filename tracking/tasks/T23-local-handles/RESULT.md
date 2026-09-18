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
  recursive side proof (including `prop_true`/`prop_false` evidence clauses),
  and reject unknown or duplicate IDs.
- The custom terms are syntax in the closed `explicit_rw` whitelist category,
  not ordinary readable Lean terms outside the tactic; there is no public
  option or toggle that exposes their elaborator.
- Handle and local-index numerals are checked before any array access.  Non-
  canonical forms such as `1_0` and huge/out-of-range values fail with a user
  diagnostic rather than panicking.

## Fixtures and checks

`LocalHandles.lean` has 12 fixture declarations (11 replay cases), including
exact-index/projection, nested side-intro, inherited proposition-side handles,
inaccessible binders, and ordinary compatibility coverage.
`LocalHandlesNegative.lean` has 13 guarded failures covering bounds,
declaration kind, invalid/out-of-bounds projections, type mismatch, unknown or
duplicate handles, inherited proposition-side unknown handles, non-canonical
and huge numerals, and malformed side-intro handles.  The parser rejection
directory has 14 cases, including ordinary-term `local_ref` escape.

- `python3 -B Experiment/check_no_simp_family.py` — PASS (4 files).
- `python3 -B Experiment/check_explicit_rw.py` — PASS (12 fixtures, 14
  rejected-syntax cases; 129-theorem axiom audit clean; all-slot serial escape
  sweep: 330/330 escapes rejected and 120/120 benign forms parsed; the suite's
  final all-slot run was before the additional `prop_false` fixture, so the
  axiom count was rechecked separately at 129).
- `lake build ExplicitLean.ExplicitRw` — PASS (warning-free).

No recorder, pipeline, axioms, or simp-family code was changed.
