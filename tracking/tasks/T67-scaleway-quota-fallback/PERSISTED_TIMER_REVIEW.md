# T67 persisted TTL timer review

Verdict: PASS for implementation commit `24239b28a65c3e3a890303081910ab9b58a1b972`. Review and checks were offline; no provider calls were made.

The bootstrap-resume path derives the immutable host cutoff as `min(policy deadline, created_at + policy lifetime)` and rejects saved `state.deadline` values that differ. It reads the already provisioned `explicit-lean-simp-pilot-ttl.timer`; it does not invoke `systemd-run` again when the persisted watchdog flag is set. Resume proceeds only if the timer reports `ActiveState=active` and its parsed `NextElapseUSecRealtime` is strictly in the future and no later than that derived cutoff. The timestamp parser accepts only the observed weekday/date/time/UTC form, checks the calendar date and weekday agree, and rejects malformed, missing, duplicate, unknown, or non-UTC fields through fail-closed validation. The existing exact legacy `{"supervisor":"started"}` bootstrap checkpoint remains eligible only under the strict bootstrap-started, armed-watchdog, positive-TTL, exact-pending-jobs, no-dispatch-evidence gate.

The refreshed mock covers exact-cutoff timer acceptance, inactive timer rejection, no timer re-arm on resume, and successful recovery from the legacy report shape. The production comparison also rejects past or later-than-cutoff timestamps. The existing authorization, one-host, $20 cap, immutable policy-hash, and host-TTL gates were not weakened by this commit.

Checks:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 19 full-run mock checks passed.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 tests passed.
- `python3 -B -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.
