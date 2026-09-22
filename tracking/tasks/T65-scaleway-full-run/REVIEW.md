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
