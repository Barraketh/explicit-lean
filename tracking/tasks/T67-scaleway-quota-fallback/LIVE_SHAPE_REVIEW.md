# T67 live SBS volume-shape re-review

Status: **PASS**

Reviewed `f6e0bda719b9d1eb3adbb8f44f37891c315d878e` against `1953b07` in an
isolated worktree. The shared root parser now accepts the observed uppercase
`Volumes` one-entry array as well as the supported lowercase representation.
It requires exactly one identified attachment, validates its configured
volume type and any reported size or IOPS, and checks a boot-volume reference
against that attachment. A response containing both `Volumes` and `volumes`,
multiple attachments, an unknown shape, or a conflicting attachment fails
closed. The attachment’s exact block-volume identity is then verified against
the pinned size, type, and IOPS, with mismatching project or zone rejected when
reported. Cleanup uses the same parser, so it resolves and removes only the
recorded SBS root volume.

Checks run against the reviewed tree:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 16 mock checks passed, including the uppercase array, surviving-volume cleanup, conflicting fields, multiple roots, and mismatched IOPS.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 tests passed.
- `python3 -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.

No live Scaleway calls were made during this review.
