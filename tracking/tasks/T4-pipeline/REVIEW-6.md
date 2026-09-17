# T4-pipeline lifecycle review (round 6)

Reviewed 2026-09-17 at T4 `c51eabb` (`task/T4-pipeline`) using T1
`30fb84903f04902f3dc9a8adb972822d87f2977a` and T2
`8b57c4a008fcef73859eedbcc95f7605a58d5e8c`. Both driven worktrees were clean
before and after the run.

## Verdict

**CRITICAL: merge ineligible.** The lifecycle design is sound in the focused
fixtures, but the real six-module gate cannot produce finalized traces.

## Checks

- `python3 -B Experiment/pipeline/check_pipeline.py`: **PASS, 240 checks**.
  Focused checks cover run-local `stage/raw/final` ownership, deterministic
  trace-path rewriting, `SIMP_TRACE_OUT_ROOT`, the five-argument explicit-path
  finalizer CLI, raw-v1/final-v2 separation, repeated-run isolation, no shared
  `meas_out` writes, and fail-closed missing-final behavior.
- Fresh full six-module harness at `/private/tmp/t4-review6-six.5EUVUS`: all
  six trace compiles ran, but all six finalizer invocations exited 1 with
  `FAIL traced source differs from deterministic transform`. The T4 rewrite
  changes each `=>trace` path to the run-local absolute raw directory, while
  T1 `finalize_traces.py` calls `verify_transform` against the original
  `test/SimpTrace/meas_out/...` transform. No final v2 records were produced.
- Identity: **0/6 modules accepted; 84/84 sites identity-failed**. Replay:
  **0/84** (fail-closed; no render or translated source was attempted). This
  is a lifecycle failure, not evidence about `explicit_rw` correctness.
- The run reported T1/T2 clean after compilation; T1/T2 tips are exactly
  `30fb849` and `8b57c4a`.

## Required fix

Make finalization accept the run-local rewritten trace paths while preserving
the original source/manifest identity and deterministic edit-ledger checks,
then rerun the full six-module gate. Do not weaken identity validation or
reintroduce shared `meas_out`/mtime selection.
