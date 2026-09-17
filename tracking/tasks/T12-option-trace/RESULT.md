# T12 Option trace capture

Status: complete for producer capture; awaiting coordinator review.

## Delivered

- Added `test/SimpTrace/OptionBasicTraced.lean`, generated from the pinned
  `Mathlib/Data/Option/Basic.lean` using the accepted v2 transform ledger.
- Added `test/SimpTrace/OptionBasicTraced.manifest.json` with exactly seven
  sites, in source order: lines 48, 56, 59, 96, 195, 198, and 234. The
  manifest records module path, exact source character ranges, ordinals, and
  call text. The nested `<| by simp only [← map_some, h]` site and the
  `ext`/tail `simp only [Function.comp_apply, getD_some, id_eq]` site are
  preserved as syntax contexts rather than whole-line replacements.
- Added Option to `test/SimpTrace/check_transcription.py` and to the producer
  positive-fixture and report coverage in `Experiment/check_simp_trace.py`.

## Recording and finalization

Compiled traced module: `lake env lean test/SimpTrace/OptionBasicTraced.lean`,
exit 0. Fresh raw records were captured under `/private/tmp/t12-option/raw/`
and finalized under `/private/tmp/t12-option/final/` using the explicit-path
finalizer. Finalization reported 7 records for 7 sites; every record is
`simp-trace-v2`, has the corresponding site ordinal, and has invocation `0/1`.
Each record has one location and no classified/unresolved result. The seven
records contain 32 top-level `rw` steps in total (no nested side traces).

## Checks

| Check | Result |
| --- | --- |
| `lake build ExplicitLean.SimpTrace` | PASS; 7 jobs, 0 errors (existing warnings only) |
| `lake env lean test/SimpTrace/OptionBasicTraced.lean` | PASS; exit 0 |
| `python3 -B test/SimpTrace/test_trace_identity.py` | PASS |
| `python3 -B test/SimpTrace/check_transcription.py` | PASS; 91/91 across seven copies, Option 7/7 |
| `python3 -B Experiment/check_simp_trace.py` | PASS; 72 fixture skeletons and containment checks |
| `python3 -B Experiment/check_simp_trace.py --report` | PASS; 91 sites, 113 records, 624 steps |
| `git diff --check` | PASS |

The report totals include the existing six-module baseline and Option:
Option contributes 7 sites, 7 records, 32 `rw` steps, and 6,550 bytes. The
full report's classified rows remain existing six-module cases; Option adds
none. A measured Option compile took 2.72s real, 1.34s user, 2.02s system,
and 738,410,496 bytes maximum RSS on the local pinned toolchain.

## Scope

Only the Option fixture/manifest, the two existing producer/report check
registrations, and this result summary are owned here. No recorder, replay
tactic, six-module fixture, or source Mathlib file was changed. Generated raw
and finalized JSON remain run artifacts under `/private/tmp`, not committed
source evidence.
