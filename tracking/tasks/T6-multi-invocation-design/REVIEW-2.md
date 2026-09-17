# T6 structural multi-invocation rendering — review 2

Reviewed commit `539a3c7a7328956379d55a48233cbb270bb05c18` on 2026-09-17.
The structural renderer is unchanged from reviewed commit `4077d149` except
for the intended status-accounting changes in `STATUS_ORDER` and `summarize`.
The `structurally_refused` bucket is explicit, and the fixture summary test
exercises its column, count, and total reconciliation.

## Verdict

**Structural implementation: PASS. Merge eligibility: HOLD.**

## Evidence

- `python3 -B Experiment/pipeline/check_pipeline.py`: **PASS, 265 checks**.
- `python3 -m py_compile Experiment/pipeline/replay_module.py
  Experiment/pipeline/check_pipeline.py`: **PASS**.
- `git diff --check 4077d149..539a3c7`: **PASS**.
- The six-module report `/private/tmp/t6-six-structural-r2/report.json`,
  re-rendered with the current summarizer, reconciles 84 records as
  **54 replayed / 5 unresolved / 2 render_failed / 4 structurally_refused /
  19 compile_failed**; no records are omitted or double-counted.
- Fresh seven-module report `/private/tmp/t6-seven-review2/report.json` used
  clean T1 `9600009b4690667da52650b2c4a99df2022e54c5` and clean T2
  `8b57c4a008fcef73859eedbcc95f7605a58d5e8c`; all 7/7 identities and 91/91
  records were accepted. Its exact totals are **59 replayed / 5 unresolved /
  6 render_failed / 0 structurally_refused / 21 compile_failed**, summing to
  91; both driven worktrees stayed clean.

## Finding

`RESULT.md` reports the fresh seven-module gate as 2 `render_failed` plus 4
`structurally_refused`, but the fresh report records 6 `render_failed` and 0
`structurally_refused`. The aggregate six render outcomes and total 91 still
reconcile, but the per-status headline is stale/mislabeled. Correct that
documentation before merge. The former Option-worktree-blocked statement is
removed from `RESULT.md`.
