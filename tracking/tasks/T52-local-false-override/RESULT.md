# T52 — replay local false proposition and retire extend_apply overlay

Implemented generic source-local provenance for generated proposition wrappers
such as `Bool.of_not_eq_true h`. The recorder now retains the real local fvar;
the renderer emits `prop_false h`, and ExplicitRw handles Bool coercion by
replaying `b = false` with the recorded proposition evidence.

Removed the stale `Function.Basic` `extend_apply` overlay
(`acca7bbba4fc669d`). The follow-up integration/prune removes the four
remaining now-generic non-`eqComm` overlays (`8e17e105590e562a`,
`c28dd19f3d6d3d67`, `42f1163b9fd99b7b`, and `a30cdf5ef0f79ad7`). The
authenticated manual database is now 21 entries across 17 modules; the
`Function.Basic` `eqComm` override (`bcd40e80cbe2ffe1`) remains untouched.

Checks:

- `lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw` — PASS.
- `lake env lean test/ExplicitRw/T52LocalFalse.lean` — PASS.
- Generic Function.Defs replay with the `a30cdf5ef0f79ad7` overlay disabled —
  PASS, 2/2 sites replayed; false branch renders `prop_false h`.
- Generic Function.Basic replay with `extend_apply` overlay absent — PASS,
  25/25 sites replayed, including the former extend_apply site.
- `python3 -B Experiment/pipeline/check_pipeline.py` — PASS (328 checks;
  baseline Nontrivial.Defs render failure remains reported by the harness).
- `python3 -B Experiment/check_simp_family_lint.py` — PASS (46 tests, 2
  opt-in sweep tests skipped).
- `python3 -B Experiment/check_no_simp_family.py` — PASS (4 files scanned).
- `python3 -B Experiment/check_simp_manual_overrides.py` — PASS (21 overlays,
  17 modules; all patched compiles and declaration-oracle checks succeeded).

Known limitation: no whole-tree acceptance is claimed.
