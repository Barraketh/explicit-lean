# T78 bounded Scaleway retry-run controller support

Status: implementation and local mock validation complete; no cloud/provider
operations were performed.

`Experiment/scaleway_simp_replacements.py` supports a policy-pinned generic
`python3 -B Experiment/*.py` argv template for 2–8 fixed, contiguous jobs while
retaining the one-host, authorization/cost/deadline, bootstrap, process identity,
dispatch reconciliation, completion, collection, and cleanup gates. Generic
policies pin an exact disjoint module workset and per-job SHA-256 inventories of
additional immutable inputs. Artifact inputs are hash-checked and made
read-only on the host. Each job's writable database copy, scratch, copied
artifact evidence, and `TMPDIR` live on a private, size- and inode-limited
tmpfs. The writable database is copied (not hard-linked) under the T77 run root
required by `retry_missing_traces.py`. Completion markers authenticate the
expanded argv and immutable input inventory as well as the existing commit,
manifest, exit status, result database, and whether the archive contains a
full result or diagnostics only.

Per-job extracted output is capped at `min(32 GiB / N, 8 GiB)` (including a
64 MiB maximum log and 1 MiB completion marker); tmpfs is smaller by those two
external files. Per-job compressed archives are capped at `min(8 GiB, 32 GiB /
N)`, with a 32 GiB aggregate archive cap. The archive writer enforces the
compressed limit while writing a temporary file, checks free space before tar
creation, and falls back to a small diagnostics-only archive if output or disk
limits are hit. If even that archive cannot be written, collection fetches
only the authenticated baseline DB and bounded log/marker. Worker outputs are
unmounted only after archive finalization.

For eight workers, the tmpfs ceilings total under 32 GiB on the policy's
128-GiB minimum-RAM host; actual tmpfs pages are consumed on demand. The remote
disk gate reserves the aggregate 32 GiB extracted-output ceiling, 32 GiB
archive ceiling, and 16 GiB operational margin, in addition to the exact bytes
to upload (all job databases, manifests, and immutable input trees). It
rechecks the 80 GiB reserve after upload. Generic jobs are rejected if their
baseline DB would not fit the per-job tmpfs copy. This guards disk and result
sizes but does not establish a per-worker RAM guarantee beyond the policy's
128-GiB host requirement.

The generic writable DB path is beneath
`/opt/explicit-lean/.lake/private/T77-error-fix-20260923`, so
`retry_missing_traces.read_only_snapshot_guard` accepts the private copy while
continuing to reject the frozen snapshot and original databases.

The SBS cleanup mappings preserve the dedicated CLI profile for both the
attached-volume and already-detached-volume paths.

Validation run from this checkout:

- `python3 -B -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py`
- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 25 mock checks passed, including verifier cwd rejection, generated shell syntax, eight-worker generic dispatch and read-only input handling, bounded log streaming, oversized scratch/database rejection, archive-space fallback, scratch result collection, disk preflight, aggregate archive limits, and dedicated-profile SBS cleanup.

These checks exercise mocks only. They do not launch a Scaleway host or certify
any Mathlib retry result.
