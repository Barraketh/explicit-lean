# Historical T64 single-worker pilot

This procedure was superseded by
[`tracking/tasks/T65-scaleway-full-run/PROCEDURE.md`](../T65-scaleway-full-run/PROCEDURE.md),
which defines the current two-worker full-run contract and policy schema. Do
not follow this historical single-worker procedure for the current run.

This procedure is for one GP1-L Linux x86_64 host and one module-list job. The
checked-in policy is intentionally disabled. The previous AWS authorization is
closed, and it does not authorize Scaleway spending. A coordinator must publish
the exact source commit and fill the region, project, image, network, job,
runtime, deadline, all-in EUR estimate and cap, itemized compute/IP/storage/
egress costs, pricing source, and cost-check timestamp (no older than 24 hours)
in `pilot-policy.json`, then explicitly
set `launch_authorized` to `true`. There is no multi-host mode.

The controller does not read or print API secrets. It uses the installed
Scaleway CLI with a dedicated profile named in the policy; it rejects `default`
and `explicit-lean-cloud`. SSH uses the named local identity file and strict
host-key checking. Before dispatch, an operator must verify the new server's
host-key fingerprint through the Scaleway console and install that key in the
local `known_hosts` file. SSH must not be run with host-key checking disabled.

The approved job directory contains exactly the inputs used by the job:

```text
modules.txt              # one unique Lean module name per line
mathlib-db.sqlite3       # the worker's writable database copy
```

The policy pins their SHA-256 hashes. The controller checks the source checkout
is clean, `HEAD` is the full approved commit, and that commit appears on the
canonical GitHub origin. It validates the authenticated organization/project,
zone, GP1-L availability, pinned Ubuntu x86_64 image, dedicated SSH key,
SSH-only security-group rule, absence of existing pilot resources, and job
hashes before creation. The server receives a local 559 GB root volume, one
public IPv4, and only the pre-existing security group. The created host clones
the pinned commit over HTTPS, installs pinned elan 4.2.3 by checksum, fetches
the dependencies from the committed Lake manifest, transfers the manifest and
database, and invokes:

```sh
python3 -B Experiment/simp_replacement_worker.py \
  --database .../mathlib-db.sqlite3 \
  --manifest .../modules.txt \
  --artifacts .../artifacts
```

Use these commands from the published clean checkout after the coordinator has
completed and reviewed the policy:

```sh
python3 -B Experiment/scaleway_simp_replacements.py plan
python3 -B Experiment/scaleway_simp_replacements.py preflight --repo "$PWD" --job /absolute/job/path
python3 -B Experiment/scaleway_simp_replacements.py create --repo "$PWD" --job /absolute/job/path --confirm-create
python3 -B Experiment/scaleway_simp_replacements.py status
python3 -B Experiment/scaleway_simp_replacements.py run-worker --repo "$PWD" --job /absolute/job/path
python3 -B Experiment/scaleway_simp_replacements.py collect --output /absolute/result/path
python3 -B Experiment/scaleway_simp_replacements.py cleanup --confirm-delete
```

`plan`, `preflight`, and `status` are read-only. `create` requires the literal
confirmation flag and a fully authorized policy. The worker may run once per
server and is bounded by both worker runtime and remaining host lifetime. A
guest systemd poweroff timer is armed before cloning. That watchdog stops compute
if the local controller disappears; it cannot delete a Scaleway server or its
storage, so the operator must run `cleanup` after collection and verify the
deleted receipt. Cleanup refuses a changed policy or resource identity and
checks the exact server and tagged storage are gone. If cleanup fails, keep the
state file and retry after resolving the reported issue.

Collection extracts only regular files under the artifact directory, requires
the worker completion marker, and checks its commit, worker exit code, input
manifest hash, and returned database hash. It writes SHA-256 values for the
archive, database, log, and artifacts into the local state file. A missing
marker, nonmatching checksum, dirty/unpublished checkout, stale/expired policy,
duplicate resource, wrong account/project/zone/type/image/network, timeout, or
cleanup failure blocks the corresponding transition. Do not retry `create`
after an ambiguous CLI timeout. The controller retains a `create-requested`
state before invoking the provider. Run read-only `status`; then confirmed
`cleanup` can adopt and delete only one exact name/tag/project/zone/type match.
If visibility is delayed or the match is not unique, cleanup refuses to guess;
keep the state and retry status/cleanup after provider listing settles.

Do not launch from this task branch: the checked-in policy is not an
authorization. Live provisioning is outside this implementation task.
