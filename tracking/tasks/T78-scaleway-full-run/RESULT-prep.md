# T78 checkpoint and shard preparation

This is a focused preparation-tool result from a fresh worktree at
`3ae9e23cb7e575f9d66284b72289bb1794c35ebe`. It does not provision a server,
launch workers, or modify any campaign database.

`Experiment/t78_checkpoint_prepare.py checkpoint` validates the stopped-worker
inputs against their respective source databases and prepares a new checkpoint
copied from T76. It applies changed queue rows in this order: the four pending
jobs, the two named-zeta jobs, and the two max-retry jobs. It checks database
integrity, the required table schemas, exact source table identity, complete
row keys, per-layer manifest coverage, and that queue and auxiliary-table
mutations stay within each job's module manifest. Each layer is compared to
its own immutable base: pending uses its recorded T65 base, named-zeta uses
T76, and max-retry uses the named-zeta merged base.

Each incoming changed success is rechecked using the current
`TSA.assert_success_commands_have_no_simp` candidate-source and direct-simp
postcondition. A failure tied to one command quarantines that success only; a
non-local parser or source refusal quarantines every incoming success in that
module. Quarantine leaves the checkpoint's previous row untouched. A
deterministic `checkpoint-audit.json` records each accepted success, each
quarantined `(module, ordinal, reason)`, and each current success preserved
against a stale or non-success result. A current success cannot be replaced
when the incoming job's baseline row differs from it.

Pending and max-retry manifests must exactly cover modules selected by their
explicit baseline statuses. Named-zeta requires
`--zeta-expected-manifest`, a canonical module list preserved from the
pre-run selection. The tool does not infer that set from error text. All three
groups must have pairwise-disjoint manifests internally and the exact expected
module union. The original databases are opened read-only and never modified.
The output root must not already exist.

The checkpoint now also requires `--input-receipt` and the separately
preserved `--input-receipt-sha256`; it rejects a receipt digest mismatch
before any database or Lean/TSA access and records both expected and actual
receipt digests. The canonical receipt pins all four baselines, all eight
worker databases, all eight worker manifests, the pre-run named-zeta target
manifest, and the selected max-retry statuses. Every caller-supplied input
path must be absolute, canonical, and non-symlink; every pinned file must be a
regular non-symlink file, and each database must be sidecar-free. The T65
pending base, T76 base, named-zeta base, and max-retry base digests are also
hard-pinned to the recorded campaign artifacts. After preflight, database and
manifest reads/copies use only receipt-resolved paths. The output audit
records the receipt's resolved path and expected/actual SHA-256, plus the
resolved path and SHA-256 of every pinned baseline, worker database, and
manifest. Inputs are rechecked after validation and immediately before
copying the T76 base.

Receipt JSON schema 1 is a fixed object with `schema`, `campaign`,
`maxretry_statuses`, and `inputs`. `inputs` contains `t76_database`,
`pending_base`, `zeta_base`, `maxretry_base`, `zeta_expected_manifest`, and
the `pending_jobs`, `zeta_jobs`, and `maxretry_jobs` arrays. Each file entry
contains exactly its canonical absolute `path` and lowercase `sha256`; each
job entry additionally contains its ordered `job` ID. The caller must preserve
that receipt before checkpointing; the tool has no command that generates or
silently refreshes it from the files under examination.

`partition` selects modules only through its required `--statuses` argument.
It allows the six retryable non-success statuses, rejects `success` and
`noop`, and creates between one and eight deterministic disjoint jobs. Each
job gets a schema-and-row-equivalent SQLite backup, a sorted `modules.txt`, and
weights in `partition.json`. It does not inspect theorem names or error text.

Example invocation shape (paths must be the preserved run inputs and the
pre-run zeta target list):

```sh
python3 -B Experiment/t78_checkpoint_prepare.py checkpoint \
  --input-receipt /path/to/immutable-T78-input-receipt.json \
  --input-receipt-sha256 <digest-recorded-in-launch-authorization> \
  --t76-database /path/to/mathlib-db-isolated-merged.sqlite3 \
  --pending-base /path/to/mathlib-db-stopped-merged.sqlite3 \
  --pending-job /path/to/pending/jobs/job-000 \
  --pending-job /path/to/pending/jobs/job-001 \
  --pending-job /path/to/pending/jobs/job-002 \
  --pending-job /path/to/pending/jobs/job-003 \
  --zeta-base /path/to/mathlib-db-isolated-merged.sqlite3 \
  --zeta-job /path/to/named-zeta/jobs/job-000 \
  --zeta-job /path/to/named-zeta/jobs/job-001 \
  --zeta-expected-manifest /path/to/pre-run-named-zeta-modules.txt \
  --maxretry-base /path/to/mathlib-db-named-zeta-merged.sqlite3 \
  --maxretry-job /path/to/max-retry/jobs/job-000 \
  --maxretry-job /path/to/max-retry/jobs/job-001 \
  --maxretry-statuses record_failed,render_failed,compile_failed \
  --repo-root /path/to/pinned-lean-checkout \
  --output-root /path/to/new-checkpoint

python3 -B Experiment/t78_checkpoint_prepare.py partition \
  --database /path/to/new-checkpoint/mathlib-db-checkpoint.sqlite3 \
  --jobs 8 \
  --statuses pending,record_failed,render_failed,compile_failed \
  --output-root /path/to/new-cloud-jobs
```

Focused verification on the synthetic fixtures:

```text
python3 -B -m py_compile Experiment/t78_checkpoint_prepare.py Experiment/check_t78_checkpoint_prepare.py
python3 -B Experiment/check_t78_checkpoint_prepare.py
Ran 12 tests ... OK
git diff --check
```

The tests mock TSA's Lean parser boundary; they verify that the checker is
called for changed successes and that an identified direct-simp failure is
quarantined. No real Mathlib worker-database merge or corpus parser sweep has
been run by this preparation task. In particular, the real checkpoint must
still supply the independently preserved pre-run zeta module list and pass
TSA validation before its output is used for dispatch. Negative receipt tests
verify that a wrong expected receipt digest, swapped pending baseline,
symlinked CLI path, post-receipt symlink retarget, and stale/tampered worker
database or manifest are rejected before an output directory or SQLite read
is created.
