# T65 independent trust-boundary review

Reviewed `0edb614..0345a40` at `0345a40a8855430b56fe6c66db62af743181666f`.
No live Scaleway calls or mutations were made. `python3 -B
Experiment/check_scaleway_simp_replacements.py` passes all 7 mock checks;
`py_compile` passes. The installed Scaleway CLI reports version 2.61.0. Its
local `--help` confirms the reviewed command forms for server create/delete,
server list/get, volume list, flexible-IP list, marketplace local-image list,
and security-group rule listing. The checks do not establish cloud resource
cleanup or remote Ubuntu build behavior.

Verdict: **FAIL — do not launch the full run until the P1 findings below are
fixed and independently rechecked.**

## Findings

### P1 — restarting after worker completion deletes uncollected results

`Experiment/scaleway_simp_replacements.py:852-857` accepts only `created` and
`workers-running` when starting `supervise`. `poll_workers` persists
`workers-finished` or `workers-failed` at lines 744-748, before
`collect_workers` starts at line 884. If the foreground supervisor exits or
the machine restarts in this interval, the next `supervise` call raises
"requires a created host or already-running workers". Its `finally` block
(lines 928-931) then calls `cleanup`, deleting the server and its result
archives without collecting them. This is a direct restart/data-loss path.

Reproduction: run through a successful `poll_workers()` so state is
`workers-finished`, stop the supervisor before collection, then invoke
`supervise` again. The second invocation rejects the phase and enters cleanup.
The resume path must collect terminal worker states before cleanup; the test
suite should cover both terminal phases.

### P1 — cleanup can declare completion while a billable flexible IP remains

Creation explicitly requests `ip=new` at line 531. Cleanup requests
`with-ip` at line 1010, but only verifies server and volume absence at lines
1013-1022. It never records the server's public IP ID, lists flexible IPs, or
confirms that the owned IP is absent. The already-absent-server branch at
lines 975-984 marks state `deleted` after checking only volumes. Scaleway CLI
2.61 exposes `instance ip list` (verified with local `--help`); its ID and
server attachment should be captured and checked in both deletion paths.
Otherwise an orphaned/reserved IP can continue billing after the controller
reports cleanup complete, so the $20 ceiling is not established.

### P1 — worker inputs are not checked as a complete, disjoint full-campaign partition

`validate_job_root` at lines 244-261 checks each manifest's syntax and hashes,
but does not check that the two manifests are disjoint, cover every pending
module in their pinned databases, or that the two database files have distinct
underlying inodes. The `simp_replacement_jobs.prepare` implementation at
`Experiment/simp_replacement_jobs.py:32-47, 50-74, 88-103` does create an exact
partition and separate SQLite backups, but the controller does not verify
that a policy-approved job root came from that command or retained its
invariants. Two manifests can overlap or omit modules and still pass policy
validation; workers can exit successfully with incomplete campaign coverage.
Hard-linked identical DB files also pass hashes and can be concurrently
mutated by both workers. Preflight needs to validate both manifests against
the queue in their DBs, reject overlap and missing candidates, and reject
shared DB inodes.

### P1 — collection has no compressed or expanded size bound before writing to disk

`collect_workers` downloads each full archive with `scp` at lines 784-790,
then extracts every accepted regular file at lines 793-818. There is no cap on
downloaded archive size, tar member count, per-file size, total expanded size,
or available destination disk space. The 200 GiB remote-disk requirement does
not protect the coordinator's local disk. A large worker artifact or highly
compressible archive can fill local storage before validation, and repeated
attempts may repeat that cost. Check remote and local free space and enforce
archive/member/expanded-size ceilings before extraction; fail while preserving
the remote results and resource state.

### P1 — bootstrap omits worker prerequisites and races two Lake builds

The bootstrap at lines 631-640 installs no `zstd` and runs only
`lake exe cache get`. The repository's existing Linux setup at
`Experiment/simp_engine_vast.py:350-369` installs `zstd`, runs the cache, and
builds `ExplicitLean` targets. The T62 worker's `ensure_prerequisites` at
`Experiment/simp_replacement_worker.py:344-362` runs
`lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw` if the oleans are
absent. T65 starts both workers concurrently at lines 684-708, so a clean
checkout can have both workers invoke Lake's build for the same targets at
once. The bootstrap must install the cache decompressor and build/check those
targets once before launching either worker.

### P2 — created-host identity is not fully verified before dispatch

The create and dispatch checks at lines 553-557 and 612-618 validate server
ID, name, project, zone, commercial type, and one ownership tag. They do not
verify the created server's image/local-image identity, attached security
group, selected SSH key identity, or volume shape against the policy. The
create request contains image and security-group arguments, and cloud-init
embeds a public key, but the controller should verify the resulting server
shape before transferring the database or starting paid work. This also makes
the documented exact-image/SG/key identity gate stronger than the code.

## Cloud-shape observations

The CLI 2.61.0 local help confirms these forms used by T65: server create
accepts `type`, `image`, `root-volume`, `ip`, `security-group-id`,
`cloud-init`, `project-id`, `zone`, and indexed `tags`; delete accepts
`with-volumes=all`, `with-ip`, and `--wait`; server and volume list accept
project/zone filters; `instance ip list` is available; local-image and
security-group `list-rules` commands accept the corresponding IDs and zone.
No authenticated API response was fetched, so mocked JSON shapes are not a
substitute for a live read-only preflight.

## Final re-review of `e028bba`

Re-reviewed the fixes in `e028bba0e2f1bdaa1fd3e9ad32dad362b8d3d276` (the
implementation fix is `6e894410`). Ran:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 12 checks
  passed.
- `python3 -m py_compile Experiment/scaleway_simp_replacements.py
  Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.
- `scw version` — CLI 2.61.0. Local help remains consistent with the server,
  IP, volume, image, and security-group command forms above. Official
  Scaleway schema/CLI documentation describes the server volume inventory and
  boot-volume identity ([Instance API schemas](https://www.scaleway.com/en/developers/api/instance/~schemas),
  [CLI v2 instance output example](https://www.scaleway.com/en/docs/instances/api-cli/creating-managing-instances-with-cliv2/)).

The original findings are resolved in this diff: manifest sets must exactly
partition both read-only pending queues, DBs must have equal baseline bytes but
distinct inodes, collection checks compressed and extracted bounds plus free
space, bootstrap installs `zstd` and builds/verifies the two Lean targets
before launching either worker, and cleanup pins/checks the flexible-IP ID in
both normal and already-absent-server paths. Terminal
`workers-finished`/`workers-failed` states now resume collection. The new
server verification checks the configured image ID, SG ID, key provenance,
volume type/size and IP identity. Mocks exercise these paths, including
retained IP rejection, low disk, archive expansion, and terminal restart.

Final verdict: **FAIL — one P1 remains; do not dispatch from this controller
until it is fixed and re-reviewed.**

### P1 — a supervisor restart in `dispatching` waits out the budget then deletes results

`run_workers` saves `phase="dispatching"` before launching the first worker
and only saves `workers-running` after both remote launch requests finish
([`Experiment/scaleway_simp_replacements.py:806-836](../../../../Experiment/scaleway_simp_replacements.py)).
The supervisor calls this phase resumable at lines 1031-1040 and allows it in
the polling loop at line 1056. However, `poll_workers` rejects every phase
except `workers-running`, `workers-finished`, and `workers-failed` at lines
839-842. If the supervisor exits during dispatch, a restart catches that
polling error repeatedly, runs until the deadline/budget, then sets
`cleanup_allowed=True` and deletes the server at lines 1067-1070. A worker
launched before interruption may have valid completed results in its remote
job directory, which this path never collects. `dispatch-failed` is also
accepted by the loop but rejected by `poll_workers`; that phase may include
one launched worker and the same eventual result deletion.

Reproduction: persist `phase="dispatching"` (or `dispatch-failed`) with
`server_id` and remote job directories, then invoke `supervise`. Its first
`poll_workers` call raises "worker status requires dispatched jobs" because
the saved phase is outside that method's accepted set. Repeated poll errors
reach the timeout branch, which permits cleanup. The suite's restart test
covers terminal phases, but not these intermediate dispatch phases. Resume
must reconcile per-job remote markers/PIDs and collect any completed results;
it must not age out to cleanup while a launched worker may have recoverable
output.

### P2 — root volume verification matches any volume, not the boot volume

`_verify_server_identity` accepts any attached local volume whose size is
within the 559 GB window at lines 524-533. It does not compare the selected
volume ID to the server's `boot_volume_id`, nor require its volume `boot`
field. Scaleway's server schema exposes `boot_volume_id`, and its CLI example
includes `Volumes.*.Boot` (links above). An unexpected server with a different
boot volume plus an additional matching-size local volume would pass this
check and be recorded as if the requested root volume were verified. The
mock's server includes one volume only and does not test a mismatched boot
volume. Validate that the unique boot volume is the configured local root
volume and record that exact ID.

No provider API calls or resource mutations were made during this re-review.

## Final re-review of `7bdd576`

Re-reviewed author change `7bdd576c3e8c5e9f0d91ec842aed93cd67f3726c`
(cherry-picked in this review checkout as `4c5f82f`) and the accumulated
controller changes. Verification:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — all 13 mock
  checks passed, including bounded cleanup after persistent ambiguous dispatch
  and transient recovery that retains an already-live job and launches only
  its untouched peer.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — all 10 preparation
  checks passed.
- `python3 -m py_compile Experiment/scaleway_simp_replacements.py
  Experiment/check_scaleway_simp_replacements.py
  Experiment/simp_replacement_jobs.py
  Experiment/check_simp_replacement_jobs.py` — passed.
- `git diff --check` — passed.
- No live Scaleway calls or mutations were made.

The two findings from the `97ef952` review are resolved. For persistent
ambiguity, the supervisor retries reconciliation within the worker/host budget;
on expiry it checkpoints the unresolved claim and possible result loss, then
cleans up the exact owned resources. The new mock advances the supervisor to
budget expiry and verifies that cleanup occurs. For PID reuse, both launch
reconciliation and subsequent status polling require the saved random launch
token to match `/proc/$pid/environ` and the process command line to identify the
expected worker and job paths; `kill -0` alone is no longer sufficient. A
mismatched or missing process identity remains ambiguous and is never
relaunched. Tests also assert that the generated status and launch scripts
carry the token checks. The procedure and result notes now describe this
behavior and its hard-deadline cleanup tradeoff.

The prior boot-volume identity, server/image/security-group/key/IP checks,
two-shard full/disjoint baseline validation, bounded archive handling,
bootstrap prerequisites/build, dispatch recovery, and exact cleanup checks
remain present; the full mocked and preparation suites pass after this change.

Final verdict: **PASS — no remaining launch-blocking finding identified in
this review.** This is a static/mock review only; the reviewed command/API
shapes and cloud cleanup behavior have not been exercised against live
Scaleway resources.

## Final re-review of `97ef952`

Re-reviewed the launch-claim and boot-volume fixes in
`97ef952c5fb14b797ac0282d942639522acf1bb7`. Verification:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — all 13
  Scaleway mock checks passed.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — all 10 preparation
  checks passed.
- `python3 -m py_compile Experiment/scaleway_simp_replacements.py
  Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.
- No live Scaleway requests or mutations were made.

The prior P1 for terminal worker restarts is resolved. Dispatch recovery now
reconciles the two remote job states and includes tests for six restart points,
including a live worker, a completed worker, a lost SSH launch response, and
the ambiguous response retry. The atomic `mkdir .launch-claim` closes the
status-to-launch race: concurrent controllers cannot both pass the claim, and
an extant or ambiguous claim is never relaunched. The boot-volume check now
requires the pinned 559 GB local volume to match `boot_volume_id` or
`boot: true`; tests reject wrong boot IDs and a matching-size non-boot volume.

Final verdict: **FAIL — one P1 cost-bound recovery gap remains before the
authorized run.**

### P1 — unresolved launch ambiguity ends supervision without deadline cleanup

On launch-status or claim ambiguity, `_reconcile_dispatch` persists
`dispatch-failed` and raises (for example lines 783-799 and 816-820).
`supervise` catches that error and deliberately leaves `cleanup_allowed=False`
for `dispatch-failed` (lines 1219-1229), then returns. No local deadline
monitor continues. The cloud-init watchdog only powers off the server; it
does not delete the attached flexible IP. The controller therefore leaves a
billable IP/resource after an ambiguous outcome, with no automatic provider
cleanup at the 12-hour deadline. This protects possibly recoverable output,
but no longer enforces the configured all-in cost cap in that failure mode.

Reproduction: make the remote claim exist but return an empty/malformed PID or
have `kill -0` fail; `_reconcile_dispatch` records `dispatch-failed` and
raises. `supervise` returns with no cleanup call. After the cloud-init TTL
powers off the instance, the exact public IP remains allocated because cleanup
never calls `instance server delete ... with-ip`. Keep a durable local
supervisor running through the hard deadline and clean up there, or implement
an equivalent bounded cleanup/recovery mechanism that preserves remote data
until the deadline and verifies the IP is deleted.

### P2 — `kill -0` proves only that some process owns the PID

The claim reconciliation script validates that `worker.pid` contains decimal
digits and calls `kill -0` (lines 744-748, 772-775). It does not verify the
process start time or command line against the expected worker launcher. If
the worker shell exits without writing `complete.json`, its PID is later
reused, and the claim remains, an unrelated process can be classified as
`RUNNING`. This does not cause a duplicate launch, but can leave a missing
result unresolved until timeout. Pin process identity (for example with a
start-time token stored atomically with the PID and checked through `/proc`),
or ensure unresolved status enters bounded recovery/cleanup rather than
ending supervision.

The P2 does not supersede the P1: regardless of PID identity checking, an
unresolved claim needs a persistent monitor through the authorized cleanup
deadline. The report's earlier verdicts are historical; this section is the
final verdict for `97ef952`.
