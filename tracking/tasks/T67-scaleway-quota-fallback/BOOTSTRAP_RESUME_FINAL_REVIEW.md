# T67 bootstrap-resume final trust-boundary review

Verdict: PASS for the reviewed offline bootstrap-recovery change (`e9b4c11216019d858339511be7f3c85cc17286d5`, integrated in this checkout as `f165a96`). No live provider calls were made.

## Findings

- The legacy live state report `{"supervisor":"started"}` is accepted by `_bootstrap_resume_is_safe` only as an exact one-key object. The gate still requires phase `bootstrap-started`, the fixed top-level state whitelist and required fields, an armed watchdog with a positive integer TTL budget, a string bootstrap timestamp, exactly the two expected jobs with the exact pending-job key set and `phase: pending`, and no worker/dispatch evidence. The regression test constructs this exact legacy report, saves it, and drives `supervise` through a resumed run.
- Final supervisor reporting now happens after cleanup and after `elapsed_seconds`, failure, and `complete` have been finalized. A bootstrap failure with cleanup refusal is tested to persist the full returned report; the legacy report is then tested as a valid recovery checkpoint, followed by a successful resumed run and completed cleanup. Checkpoint write errors force the returned result to `complete: false`.
- The watchdog recovery path verifies the already-armed systemd timer is active and its monotonic expiry falls within the remaining host TTL; it does not arm a second timer. The resume path also retains the authorization deadline, one-host state machine, repository/job identity, and no-dispatch gates. Tests cover dispatch-evidence rejection and missing-watchdog refusal.

## Checks

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 19 full-run mock checks passed.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 tests passed.
- `python3 -B -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.

No live Scaleway/provider calls were made. Review scope was the bootstrap report persistence/resume fix and its effect on the existing one-host, cost, TTL, watchdog, and no-dispatch gates.
