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

No live Scaleway call, resource creation/deletion, or credential access was
performed. `pilot-policy.json` remains launch-disabled; it must be completed
with a current all-in cost estimate under the user's $20 total cap before any
run. The supervisor must remain running locally until it records validated
collection and confirmed cleanup, or a hard host/deadline failure and cleanup
attempt.
