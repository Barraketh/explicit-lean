# T83 Scaleway `explicit_rw_v2` retry

The bounded one-host run reached its fixed deletion deadline on
2026-09-24. All 32 pass-2 shards and all 9 pass-3 shards completed. Pass 6
launched all 32 original disjoint shards with the latest principled replay
fixes; 21 completed pass-6 databases were collected intact before cleanup.
Six additional shards use their completed pass-2/pass-3 fallback, so 27 of the
32 original shards are represented by a terminal cloud database.

The transfer was still active when the deletion watchdog reached the immutable
12:30Z deadline. Five fallback databases were not collected: `job-008b`,
`job-009a`, `job-011b`, `job-012a`, and `job-013a`. Two interrupted transfer
files failed SQLite integrity checking and were excluded. Those five shards
therefore retain their T82 input state in the final partial merge.

The 27 accepted job databases each passed `PRAGMA integrity_check`. Their
disjoint manifest-owned rows were merged directly into a fresh copy of the T82
input without reparsing successes or overwriting any input. The merged database
is:

`.lake/private/T83-scaleway-v2-20260924/mathlib-db-t83-partial-merged.sqlite3`

It passed `PRAGMA integrity_check` and has these exact status counts:

- `success`: 34,529
- `noop`: 4,900
- `record_failed`: 4,652
- `render_failed`: 3,177
- `compile_failed`: 4,064

This is 4,750 new successes over the immutable T82 input's 29,779 successes.
The merge covers 2,624 modules from the 27 collected shard manifests. It is a
partial newest-available merge, not a whole-tree or simp-disabled
certification.

The deletion watchdog removed server
`bd83daa6-ed35-4b67-ac4c-422bce8009a4`, volume
`7e9cab30-2600-443d-9e89-037aca28f5b0`, flexible IP
`f3f8ad24-95cb-4ad5-bf18-59939737830e`, and security group
`0ffa22ab-5875-4b83-8a6e-0dcd2c01ec4a`. Exact provider lookups confirm all
four resources are absent.
