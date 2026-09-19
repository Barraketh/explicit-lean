# T58 result

Status: completed for the two Grind metadata operations; certification passes
with a fresh olean, but final `Mathlib.Logic.Basic` acceptance remains blocked
by the two dormant Meta `simp symmExpr` source bodies.

## Changes

- Added `ExplicitLean/Grind/Metadata.lean`, a narrow pair of command
  elaborators. They register the same `grindExt` E-match entries as stock,
  using explicit theorem/pattern elaboration and preprocessing with the
  normalizer disabled; no `Lean.Meta.Simp` is called.
- Extended the authenticated broader overlay with the exact source identities
  `79237ddd16d5c161` (`xor_def`) and `965368017b80e872` (`Exists.choose_spec`).
  Original operations remain adjacent comments; the theorem declaration is
  preserved.
- The stock/replacement fixtures now emit and compare every `EMatchTheorem`
  field: `levelParams`, `proof`, `origin`, `kind`, `numParams`, `patterns`,
  `symbols`, `cnstrs`, and `minIndexable`. Pretty-printed values are newline
  escaped so the differential cannot silently truncate a multiline pattern.
- `check_pipeline.py` now derives an absolute compiler from
  `lake env lean --print-prefix`, fail-closes unless it reports Lean 4.32.2
  commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`, and runs both fixtures
  with that binary and the explicit temp-first `LEAN_PATH`.
- Reviewed the exact stock forms: `[grind =]` takes the E-match attribute
  branch (which adds an `.ematch` entry) and `grind_pattern` directly adds an
  E-match theorem. Neither writes
  `casesTypes`, `extThms`, `funCC`, or `inj`; therefore `grindExt.ematch` is the
  complete Grind-extension write surface for this differential.
- `replay_module.py` imports the helper only for generated
  `Mathlib.Logic.Basic`.

## Checks

- `python3 -B Experiment/pipeline/check_pipeline.py`: **355 checks passed**;
  the differential passed compiler identity checks and exact stock/replacement
  metadata equality for both operations.
- Fresh current-main replay using `/Users/ptsier/projects/explicit-lean` as
  both T1 and T2:
  `python3 -B Experiment/pipeline/replay_module.py --module
  Mathlib/Logic/Basic.lean --t1 /Users/ptsier/projects/explicit-lean --t2
  /Users/ptsier/projects/explicit-lean --out
  /tmp/T58-main-replay-20260919T-current` — **31/31 replayed**, whole-module
  compile passed.
- Rebuilt the pinned certification compiler with
  `python3 -B Toolchain/SimpDisabled/build.py --json`, then ran the strict
  compiler against the fresh replay source with `Toolchain/SimpDisabled/run.py`.
  It returned **0** and emitted the fresh olean
  `/tmp/T58-cert-current-20260919T/Logic.Basic.cert-final.olean`.
- `python3 -B Experiment/check_simp_family_lint.py`: **46 passed, 2 skipped**;
  the generated target still has exactly the two dormant Meta findings.
- `python3 -m py_compile Experiment/pipeline/check_pipeline.py
  Experiment/pipeline/replay_module.py Experiment/pipeline/broader_overlay.py`:
  passed. `git diff --check`: passed.

## Limitations

The two dormant Meta `simp symmExpr` bodies remain outside T58 and prevent
static cleanliness and final `Mathlib.Logic.Basic` module acceptance claims.
No cloud, deadline, authorization, package, or frozen evidence was changed.
