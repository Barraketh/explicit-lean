# T67 bootstrap redirect review

Verdict: PASS for `3950274ad02a62aef13d20134a59c5308fd5ac4f`. No live provider calls were made.

The only runtime change adds curl's `--location` option while retaining `--fail`, `--silent`, and `--show-error`, so a redirect is followed but HTTP failures still abort the `set -e` bootstrap. The pinned Elan release URL and SHA-256 constant are unchanged; the fetched archive is still verified with `sha256sum -c -` before extraction or execution. The exact URL/checksum and curl flags are asserted in the bootstrap mock. The commit does not alter launch authorization, immutable policy hash, one-host/$20/TTL limits, worker dispatch, or recovery gates.

Offline checks:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 19 full-run mock checks passed.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 tests passed.
- `python3 -B -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.
