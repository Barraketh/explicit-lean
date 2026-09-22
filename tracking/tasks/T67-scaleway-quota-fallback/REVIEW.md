# T67 Scaleway quota fallback review

Status: **PASS**

Reviewed the T67 changes (`d947d89`, `257735d`, and `5bae1f1`) against base
`499e1ced9df6a7d31f66b9b0d31d033e87196598` in an isolated worktree. The
follow-ups resolve the provider-shape, cleanup, and architecture-value gaps
identified during review.

The fallback now checks the configured commercial type from the server-type
listing, requires available provider architecture `x64` (the x86-64 machine
architecture) with RAM at or above the configured minimum, and verifies the
pinned Ubuntu image's `x86_64` architecture, exact compatibility, and
root-volume image type (`instance_sbs` for SBS). It validates SBS type, exact
decimal-byte size, IOPS, project, and zone through the Block Storage API. The
policy compares decimal GB storage against the `minimum_local_disk_gib` bound
in GiB, so 100 GB does not incorrectly satisfy a 100 GiB minimum.

For the observed POP2 server response, the sole volume at slot `0` is the root
even though the response omits a boot-volume reference and reports `boot=false`.
The controller accepts that shape only for a single slot-0 SBS attachment and
then validates the exact block-volume identity and policy details. This is
consistent with the preserved real server response at
`.lake/private/T61-scaleway-pop2hm/server-create.json`.

SBS preflight rejects tagged or named orphan pilot volumes. Cleanup inventories
the exact block-volume resource, deletes only the recorded root if it remains
after server deletion, and confirms the server, block volume, and flexible IP
are absent before marking cleanup complete. Existing one-host/two-worker,
12-hour host, 10-hour worker, and at-most-$20 guards remain in place. The
checked-in policy remains launch-disabled.

Checks run against the reviewed tree:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 16 mock checks passed.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 tests passed.
- `python3 -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.

No live Scaleway calls were made during this review.
