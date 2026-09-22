# T65 two-worker Scaleway run

T65 extends the T64 controller to one GP1-L Linux x86_64 host running exactly
two module workers concurrently. It is still a single host. The checked-in
policy remains disabled and contains no live account, network, key, job, or
cost authorization values.

## Prepare and pin inputs

Create the two independent writable database copies and module manifests from
the source DB:

```sh
python3 -B Experiment/simp_replacement_jobs.py prepare \
  --database /absolute/path/mathlib-db.sqlite3 --jobs 2 \
  --output /absolute/path/job-root
```

The root must contain exactly `job-000/` and `job-001/`, each with
`modules.txt` and `mathlib-db.sqlite3`. Pin both SHA-256 digests for each job
in the policy. The source commit must be the full published commit that owns
the controller, worker, and Lean project.

Before authorization, fill the dedicated profile, organization/project/zone,
GP1-L-compatible Ubuntu Noble x86_64 global image ID, security group, SSH key,
private identity file, dedicated absolute `known_hosts_file`, and SSH source
CIDR. Price the full 12-hour host envelope, public IPv4, root storage, egress,
and other charges. Set the all-in EUR estimate below the configured EUR cap,
set `max_cost_usd` no higher than $20, and pin `eur_usd_rate`, `fx_checked_at`
and `fx_source` to a current trustworthy conversion. `validate_policy` rejects
an estimate above the EUR cap, a EUR cap that converts above the USD cap,
stale pricing, more than 12 hours of host lifetime, or more than 10 hours of
worker runtime. Set
`launch_authorized: true` only after those values are reviewed.

The host key file must be a readable, regular, non-symlink file. It may be
empty during preflight. After creation, verify the server's SSH host-key
fingerprint through the Scaleway console, add that key to the dedicated file,
and start worker dispatch only after the controller finds the server address
in that file. Every SSH/SCP command pins that file and keeps
`StrictHostKeyChecking=yes`.

## Preflight and execution

Run from the exact clean, published checkout:

```sh
python3 -B Experiment/scaleway_simp_replacements.py plan
python3 -B Experiment/scaleway_simp_replacements.py preflight \
  --repo "$PWD" --jobs /absolute/path/job-root
python3 -B Experiment/scaleway_simp_replacements.py create \
  --repo "$PWD" --jobs /absolute/path/job-root --confirm-create
```

Preflight is read-only. It checks the exact source HEAD and publication,
project identity, absence of pilot resources, `GP1-L` availability,
marketplace local-image compatibility (`ubuntu_noble`, `x86_64`,
`instance_local`), exact SSH ingress rule, pinned job hashes, and input layout.
It also opens the pinned databases read-only and requires that both are
distinct regular files with distinct inodes but identical baseline bytes and
pending queues; the two manifests must be disjoint and their union must equal
that complete queue. The parser accepts the top-level array and keyed-object
response shapes used by Scaleway CLI 2.61.0. The cloud-init TTL shutdown is
armed before remote setup.

After verifying/installing the new host key, run the local supervisor in a
foreground terminal or under a process supervisor so it remains alive:

```sh
python3 -B Experiment/scaleway_simp_replacements.py supervise \
  --repo "$PWD" --jobs /absolute/path/job-root \
  --output /absolute/path/collected-results --poll-seconds 60
```

The supervisor accepts an already-created host or resumes polling already
running workers. It pins and uploads both jobs, verifies remote hashes, starts
two independent Lean worker processes with separate DBs, logs and artifact
directories, then polls both completion markers. Before either worker starts,
bootstrap installs `zstd`, warms the Lake cache, and builds and verifies
`ExplicitLean.SimpTrace` and `ExplicitLean.ExplicitRw` once. Creation and
dispatch both validate the resultant server's image, security group, SSH-key
provenance and local root volume, and record the exact attached flexible-IP ID.
Collection validates both archives, module-manifest hashes, source commit,
worker exit codes, updated DB hashes, logs and artifacts before atomically
publishing the local output. A compressed archive is capped at 8 GiB per worker
(16 GiB total), extraction is capped at 100,000 members, 8 GiB per member and
32 GiB total, and local free space is checked before download and during
extraction. Failed staging attempts are removed before retry so retries cannot
accumulate large temporary trees. A transient or invalid collection is retried
while host time remains. A restart from `workers-finished` or `workers-failed`
resumes collection; it does not relaunch workers or delete remote archives.
Uncollected terminal results are preserved on entry rejection or
policy-validation failure. The supervisor deletes the exact tagged host,
attached storage and recorded flexible IP only after validated collection, or
at the hard worker/host deadline after recording that results could not be
recovered. Cleanup verifies absence of the exact IP in Scaleway's IP list in
both normal and already-absent-server paths. The state file records retries,
failures, checksums, cleanup, and the final report.

Useful read-only follow-up:

```sh
python3 -B Experiment/scaleway_simp_replacements.py status
```

If cleanup itself fails, preserve the state and retry `cleanup
--confirm-delete`; it is idempotent once state records confirmed deletion.
Do not retry an ambiguous create: inspect status, then use the exact-match
cleanup recovery path.

The controller, supervisor and tests make no cloud requests unless their CLI
subcommands are run with a populated policy. The mock test suite never contacts
Scaleway and never contains credentials.
