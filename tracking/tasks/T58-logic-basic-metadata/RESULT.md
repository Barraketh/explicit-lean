# T58 result

Status: completed for the two Grind metadata operations; full module acceptance is
not claimed because the two dormant Meta `simp symmExpr` bodies remain.

## Changes

- Added `ExplicitLean/Grind/Metadata.lean`, a narrow pair of command
  elaborators. They register the same `grindExt` E-match entries as stock,
  using explicit theorem/pattern elaboration and preprocessing with the
  normalizer disabled; no `Lean.Meta.Simp` is called.
- Extended the authenticated broader overlay with the exact source identities
  `79237ddd16d5c161` (`xor_def`) and `965368017b80e872` (`Exists.choose_spec`).
  Original operations remain adjacent comments; the theorem declaration is
  preserved.
- Added `test/GrindMetadata/{Stock,Replacement}.lean` and a fail-closed
  differential check in `check_pipeline.py`. It compares kind, parameter
  count, normalized pattern, symbols, constraints and `minIndexable` for both
  exact operations.
- `replay_module.py` imports the helper only for generated `Mathlib.Logic.Basic`.

## Checks

- Fresh current-main replay with `--t1` and `--t2` both
  `/Users/ptsier/projects/explicit-lean`: 31/31 direct sites, stock whole-module
  compile exit 0, 7.12s.
- `python3 -B Experiment/pipeline/check_pipeline.py ...`: 346 checks, 8.65s.
- Stock seven-target strict cone preflight with baseline lint: passed; fresh
  outputs and translated-root resolution recorded in
  `.lake/T58-cert-cone-20260919T0320/manifest.json`.
- Main `Toolchain/SimpDisabled/run.py` strict translated-root compile: exit 0,
  fresh `.lake/T58-cert-cone-20260919T0320/Logic.Basic.cert-final.olean`.
- `check_simp_family_lint.py`: 46 passed, 2 skipped. Generated target lint
  intentionally reports exactly 2 dormant Meta bodies (lines 57 and 88).
- Touched-declaration no-new-axiom comparison: stock/applied axiom lines match
  for `xor_def` and `Exists.choose_spec` (2/2); `check_explicit_rw.py` also
  passed its 138-theorem axiom audit.
- `git diff --check`, Python compilation, and helper lint passed.

## Limitations

The dormant Meta bodies are outside T58 and prevent static cleanliness/final
Logic.Basic acceptance claims. No cloud, deadline, authorization, package, or
frozen evidence was changed.
