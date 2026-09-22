# T67 SSH and SCP public-IP re-review

Status: **PASS**

Reviewed `e9856f575614f9c614ff69540b60e4c51cc694cc` against `11f88e2` in an
isolated worktree. SSH bootstrap, job-upload SCP, and result-download SCP now
resolve the address through `_one_public_ip` and require both the ID and
address to match the created server's saved state before connecting. Duplicate
singular/plural records for one IP are rejected if their address, family, or
dynamic status disagree. Strict known-host checking remains on each connection.

Regression coverage includes plural-only server responses for SSH, upload, and
download; state-address mismatch; and conflicting duplicate IP records. Checks
run against the reviewed tree:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 17 mock checks passed.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 tests passed.
- `python3 -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.

No live Scaleway calls were made during this review.
