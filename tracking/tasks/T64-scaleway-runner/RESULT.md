# T64: bounded Scaleway worker controller

Implemented the operator-controlled, single-host Scaleway lifecycle in
`Experiment/scaleway_simp_replacements.py`. It uses the installed `scw` CLI
through an injectable subprocess runner. The controller validates a clean,
published full Git commit and exact job hashes, authenticated Scaleway
organization/project, zone, GP1-L availability and memory, pinned Ubuntu
x86_64 image, dedicated SSH key, source-limited SSH ingress, and existing
pilot-resource absence before the one explicitly confirmed create action.

The worker path clones the pinned source, installs pinned elan 4.2.3 with a
SHA-256 check, fetches the committed Lake dependencies, transfers one
`modules.txt` plus writable database, invokes the agreed worker CLI once, and
limits runtime by worker cap, host TTL and absolute deadline. A persistent
guest systemd timer powers off at the earlier of the authorized deadline or
host TTL. Result collection requires a completion marker and matching source,
manifest, worker exit and database hashes; it records hashes for the archive,
database, log and artifacts. Cleanup targets the saved resource ID only,
deletes the server with attached volumes and IP, then verifies server and
storage removal. `status` is read-only. Creation is locally serialized and the
checked-in policy is disabled by default.

Added `Experiment/check_scaleway_simp_replacements.py`, the planning-only
`tracking/tasks/T64-scaleway-runner/pilot-policy.json`, and the operator
procedure at `tracking/tasks/T64-scaleway-runner/PROCEDURE.md`.

Checks run:

- `python3 -B -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py`
- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 7 mock checks passed
- `python3 -B Experiment/scaleway_simp_replacements.py --help`
- `python3 -B Experiment/scaleway_simp_replacements.py plan` — reports launch disabled and zero mutations
- `python3 -m json.tool tracking/tasks/T64-scaleway-runner/pilot-policy.json`
- `git diff --check`

No live Scaleway API operations or resource mutations were performed. The
controller path was tested with mocked provider/SSH/SCP commands, not a real
Linux host. The job-worker file is owned by T62 and was not available for an
end-to-end worker execution in this task. The policy still needs coordinator
approval and exact org/project/zone/image/network/SSH/job/source pins, fresh
itemized EUR pricing, runtime and deadline before any launch. The operator must
verify the created host key through Scaleway's console and install it in
`known_hosts`; SSH host-key checking remains strict. The guest timer powers off
compute but cannot delete the server or its storage after a controller crash,
so `cleanup --confirm-delete` remains a required lifecycle step.
