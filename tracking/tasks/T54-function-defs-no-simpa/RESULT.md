# T54 — render Function.Defs without copied `simpa`

## Result

The structural multi-invocation renderer now treats the reviewed
`by_cases h : a == b <;> simp [h] <;> simpa [I.eq_iff] using h` continuation as
an ordinary Lean branch close.  It preserves the original continuation as a
comment, emits `congrArg`/explicit `I.eq_iff` conversions after the generic
`explicit_rw` steps, and refuses any other unsupported simp-family suffix
instead of copying it into generated source.  No manual override database
entry was added.

Files changed:

- `Experiment/pipeline/replay_module.py`
- `Experiment/pipeline/check_pipeline.py`

## Checks

- `lake build ExplicitLean.ExplicitRw ExplicitLean.SimpTrace` — PASS.
- `lake env lean /private/tmp/t54-replay-after/Mathlib/Logic/Function/Defs.lean` — PASS (whole generated module).
- `python3 -B Experiment/pipeline/check_pipeline.py` — PASS (320 checks; its expected Nontrivial.Defs render-failed fixture remains reported).
- `python3 -B Experiment/pipeline/replay_module.py --module all ...` — PASS; 91/91 sites replayed, all seven modules whole-module compiled.
- Generated replay assertion over `/private/tmp/t54-replay-91/report.json` — PASS; 91 sites, all replayed, all replacement blocks strict-lint clean.
- `python3 -B Experiment/check_no_simp_family.py` — PASS (4 product files).
- `python3 -B Experiment/check_simp_family_lint.py` — PASS (46 tests, 2 opt-in skips).
- `python3 -m py_compile ...` and `git diff --check` — PASS.

No whole-tree acceptance is claimed.
