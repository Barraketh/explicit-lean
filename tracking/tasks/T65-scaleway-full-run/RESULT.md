# T65 implementation result

Implemented an opt-in one-host, two-worker Scaleway controller and local
supervisor. Each of two independently pinned module jobs has its own writable
SQLite database, manifest, worker process, log and artifact directory. Remote
input checks, per-job completion markers, result archive extraction, and
collected database/log/artifact hashes fail closed. The controller now uses
Scaleway CLI 2.61 response shapes reported by the coordinator: top-level arrays
for list calls, keyed `servers` for server-type lookup, marketplace local-image
compatibility, and separate security-group rule listing. Dedicated
`known_hosts_file` pinning is mandatory for all SSH/SCP operations.

The foreground `supervise` command polls both workers, retries result
collection using isolated attempt directories until the host/deadline budget
ends, atomically publishes validated results, and then deletes the exact
instance and attached resources. Terminal `workers-finished` and
`workers-failed` phases resume collection after restart and are not relaunched.
Policy/entry rejection does not delete uncollected archives. Collection enforces
compressed archive, member-count, per-member and total-extraction bounds, checks
local disk space, and discards failed staging directories before retry. The
created server's image, security group, key provenance and root volume are
checked before worker launch; the exact flexible-IP ID is saved and absence is
verified during cleanup. Bootstrap installs `zstd` and builds/verifies both
shared Lean targets once before starting either worker. Cleanup preserves
retry/error information in the local state file and is idempotent after
confirmed deletion.

Dispatch now persists an atomic per-job remote claim and unique launch token
before launch. The token is passed in the worker environment; reconciliation
requires exact `/proc` environment and command-line evidence before treating a
PID as the worker, preventing PID reuse from appearing live. It records remote
running/completed jobs and launches only jobs with no evidence of prior launch.
Ambiguous dispatch is retried until evidence resolves or the bounded
worker/host deadline expires; at expiry it records the unresolved state and
cleans up the exact server, volume and IP. The root volume must match the
server's explicit boot-volume ID or have `boot: true`; a similarly sized local
data volume is insufficient.

Verification completed locally:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 13 mock-only
  checks passed, including cost/TTL/job-hash rejection, complete/disjoint
  pending-queue validation and distinct DB inodes, CLI response shapes,
  server and boot-volume identity, concurrent launches, dispatch crash-point
  reconciliation, persistent-ambiguity cleanup and transient recovery without
  duplicate workers, result-size/disk limits, restart-safe
  collection, flexible-IP cleanup, idempotent cleanup, ambiguous-create
  handling, and transient collection retry before cleanup.
- `python3 -m py_compile Experiment/scaleway_simp_replacements.py
  Experiment/check_scaleway_simp_replacements.py` — passed.
- `python3 -B Experiment/scaleway_simp_replacements.py plan` — reported
  `authorized: false`, `mutation_count: 0`.

The policy now hard-limits `max_cost_usd` to $20, requires a current pinned
EUR/USD rate and source, and rejects a configured EUR cap that would exceed
the USD ceiling.

## Policy-selected machine and root-volume shapes

The controller no longer assumes GP1-L or a 559 GB local disk. It reads the
exact commercial type, minimum RAM, minimum root-disk capacity, and root-volume
format from the authorized policy. Preflight requires provider-reported
x64 (x86_64) architecture and RAM at or above the configured minimum; image
compatibility and the created server type must match the exact configured type.
The supported root forms are `local:<size>GB` and `sbs:<size>GB:<iops>`. The
attached root must have the exact configured type and decimal-byte size; the
minimum-local-disk GiB bound is converted to binary bytes before comparison.
SBS details are fetched with positional `block volume get <id> zone=...` when
the server attachment omits size. The block volume must have the matching
`sbs_5k`/`sbs_15k` type, exact `size`, and `specs.perf_iops`; project and zone
are checked when present. The image type must match its root kind
(`instance_local` or `instance_sbs`). The historical lowercase `volumes:
{"0": ...}` shape and observed capital `Volumes: [...]` shape are accepted only
when exactly one root entry exists. SBS attachments may report `sbs_volume` or
the policy-matched class (`sbs_15k`/`sbs_5k`); any reported size or IOPS must
agree. Type architecture and RAM come from the
full `instance server-type list zone=...` response (`arch: x64`); the selected name and
availability must match exactly. The ordinary boot-volume ID/flag is accepted
as root evidence. For the observed Scaleway SBS response shape, the single
attached volume at API slot `0` is accepted as the root when the boot reference
is absent, even when its `boot` field is false; multiple or unknown attached
volumes fail closed. Preflight lists SBS block volumes and rejects existing
pilot-named/tagged orphans. Cleanup lists block volumes before and after server
deletion, removes only the exact verified SBS root ID if it remains, and will
not record the terminal `deleted` phase while that ID or a tagged pilot volume
remains. The server-absent recovery path applies the same exact-ID and
project/zone checks. Cleanup's ambiguous-create adoption also checks the exact
policy type.

The default checked-in, launch-disabled policy remains GP1-L with its original
559 GB local root. Mock-only regression coverage includes the POP2-HM-16C-128G
fallback (128 GiB, provider arch `x64`, x86_64 image, 120 GB SBS root,
15,000 IOPS), capital `Volumes` with `sbs_15k`/`15K` attachment, insufficient RAM,
wrong architecture/image type, decimal-GB versus binary-GiB minimum, volume
type/size/IOPS/project/zone mismatch, invalid boot identity, orphan detection,
and server-present/server-absent cleanup with leftover SBS storage.

Verification for this addition:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 16 mock checks passed.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 tests passed.
- `python3 -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py` — passed.
- `python3 -B Experiment/scaleway_simp_replacements.py plan` — authorized false, mutation count 0.
- `git diff --check` — passed.

No live Scaleway calls were made.

No live Scaleway call, resource creation/deletion, or credential access was
performed. `pilot-policy.json` remains launch-disabled; it must be completed
with a current all-in cost estimate under the user's $20 total cap before any
run. The supervisor must remain running locally until it records validated
collection and confirmed cleanup, or a hard host/deadline failure and cleanup
attempt.
