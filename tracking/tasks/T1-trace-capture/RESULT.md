# T1-trace-capture: RESULT (review 10 fix)

## Delivered

- Added a structured validator verdict tree in `ExplicitLean/SimpTrace/Tactic.lean`.
- Every event now receives its own verdict; side and dependent-congruence trees
  recurse independently, and `buildLocation` attaches each classification to
  the exact nested `Step.unresolved` field. Top-level behavior is preserved.
- Extended `Experiment/check_simp_trace.py` to compare an expected
  `unresolved` field and to fail closed if corpus regressions omit nested
  `exists_apply_eq_apply` or `ne_eq` verdicts; the existing generic
  `source: congr` + side shape is also required.

## Checks

Commands run from this worktree on 2026-09-17:

- `lake build ExplicitLean.SimpTrace`: PASS (7 jobs, 4.3 s).
- `python3 -B test/SimpTrace/check_transcription.py`: PASS (82/82).
- `lake env lean test/SimpTrace/Fixtures.lean`: PASS (0).
- `python3 -B Experiment/check_simp_trace.py`: PASS (72 fixtures).
- Six-module trace transcription: PASS for all modules; classified exits are
  expected. `--report` PASS with 84 sites, 110 traces, 633 steps; nested
  regression line PASS. (Generated output includes prior invocation variants.)
- T4 end-to-end harness against current T2: completed; 44/84 replayed, 1
  unresolved, 19 render failures, 18 compile failures, 2 probe inconclusive.
  The harness now recognizes the nested `exists_apply_eq_apply` verdict.

## Remaining blockers

- T4 still needs its multiple-invocation renderer fix (19 cases in this run).
- Existing T1 unresolved families remain: quantified Prop arguments, unreadable
  origins, inaccessible names, and positional/binder cases.
- T2 still reports six compile failures; T1 does not broaden those families.

## Scope

Changed only `ExplicitLean/SimpTrace/Tactic.lean`,
`Experiment/check_simp_trace.py`, and this result file. Ready for fresh review
11.
