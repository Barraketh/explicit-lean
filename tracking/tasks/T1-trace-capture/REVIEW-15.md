# T1-trace-capture: merge-gate review, round 15

Reviewed `8d7f57d49360eb2980b217cb2afbf493e14496fc`. Verdict: **NO DEFECTS; merge-eligible**.

## Checks

- `lake build ExplicitLean.SimpTrace`: PASS (7 jobs; existing unused-variable/deprecation warnings only).
- `python3 -B test/SimpTrace/test_trace_identity.py`: PASS (identity, comment, ordinal, explicit-path, raw immutability, and outside-root regressions).
- `python3 -B test/SimpTrace/check_transcription.py`: PASS, 84/84 sites; `FunctionBasicTraced` 25/25.
- Fresh six-copy temporary integration: all 84 sites recorded and finalized as 106 v2 records; Lean exited 0 or only with the expected classified unresolved diagnostics. Raw v1 bytes were unchanged through all six finalizations; all v2 output was confined to the separate output directories.
- `python3 -B Experiment/check_simp_trace.py`: PASS, 72 fixtures; `--report`: PASS, 84 sites (the shared ignored measurement directory currently contains 123 records from concurrent runs, while the fresh six-copy run has the expected 106).
- Additional focused checks: differing raw call path rejected; legacy relative-root finalization retained; `git diff --check`: PASS; worktree clean.

The explicit five-path interface binds the deterministic transform and every raw call clause to `--raw-dir`, accepts absolute T4-style run-local paths, and leaves default module-mode relative behavior intact. No implementation change is requested.
