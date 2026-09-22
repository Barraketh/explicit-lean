# T67 bootstrap recovery re-review

Status: **FAIL**

Reviewed `555ea6794d45b06b6f9b1a0db350bb8dfd0cc087` against `463dcf8` in an
isolated worktree. The explicit `run-workers` retry path now repairs the
`/opt/explicit-lean` ownership issue idempotently, verifies the existing
checkout's origin, and validates the already armed TTL timer instead of
rearming it. The dispatch-state gate now requires exact pending job records
and rejects extra state/job fields that could indicate a prior worker launch.

One resume-path blocker remains: `_bootstrap_resume_is_safe` accepts a
`supervisor_report` only when it has `supervisor`, `complete`, `error`, and
`elapsed_seconds` in a particular completed shape. However, `supervise()` saves
`supervisor_report` in its `finally` block before it appends the final error,
elapsed time, and completion flag. After a supervised bootstrap failure, the
checkpoint therefore does not satisfy the resume predicate, so invoking the
supervisor again refuses the intended `bootstrap-started` retry. Update the
accepted checkpoint shape or change report persistence order, and test a
bootstrap failure followed by a resume through `supervise()`.

Checks run against the reviewed tree:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 18 mock checks passed.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 tests passed.
- `python3 -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.

No live Scaleway calls were made during this review.
