# T77 isolated recovery and pending-site run

Status: active local campaign. Implementation commit:
`79b2f6aa7f854f2a4ef6b06b0ba8e436c6d06682`.

## Implemented controls and principled fixes

- `Experiment/isolated_trace_compile.py` now masks only an authenticated
  theorem/lemma body suffix after its top-level declaration assignment. Named
  arguments and top-level `let` assignments cannot be mistaken for the proof
  boundary. Explicit status retries archive the prior audit result.
- Existing successful replacements must be nonblank and proof-hole-free before
  they enter a compile baseline. Writable databases must be single-link copies
  inside the exact T76 jobs or T77 run roots; frozen snapshots, original
  databases, hard links, and empty manifests fail closed.
- `Experiment/retry_missing_traces.py` records missing source sites one at a
  time, reauthenticates resumed traces, compiles an unchanged baseline, and
  then compiles one full command replacement at a time. Manifest ownership,
  source hashes, command ownership, status transitions, and all database writes
  are checked transactionally.
- Module-absolute T22 `sourceArgs` spans are compared for exact equality with a
  canonical manifest derived from the pinned original source for every
  invocation record, then deep-copied and rebased to command-local Unicode
  coordinates. In-bounds wrong-argument spans and later-invocation tampering
  fail before rendering.
- The generated spelling `at []]` is rendered as `at [] ]`, which Lean parses
  as the empty rewrite path followed by the surrounding `explicit_rw` list
  close. Isolated command rendering now honors comment suppression.
- A proposed text/line-regex expansion of generic `<;>` was removed after
  review. Structural expansion remains limited to the existing parsed binary
  branch-spine contract; no heuristic syntax inference was accepted.

## Verified checks

- 19 isolated-compile focused tests.
- 18 per-site retry focused tests.
- 15 renderer regressions.
- 11 replacement-worker checks, including real recorder and Lean compile
  fixtures.
- T9 trace identity tests and T22 source-argument tests.
- 316 pipeline checks excluding the unavailable historical T1/T2
  worktree-dependent site-count and end-to-end checks.
- `py_compile` and `git diff --check` passed for the changed implementation.
- Independent trust review passed the final database, manifest, transactional,
  source-provenance, and renderer boundaries.

## Real smoke evidence

The disposable database
`.lake/private/T77-error-fix-20260923/post-review-smoke/mathlib-db.sqlite3`
was copied from the stopped-run baseline. Two commands in
`Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne` were recorded
per site and stock-compiled as full-command replacements:

- ordinal 35: `compiled_success`, 519-byte replacement;
- ordinal 36: `compiled_success`, 463-byte replacement.

Both replacements are nonblank ordinary `explicit_rw`, contain no executable
`simp`/`simpa`/`dsimp`, and contain no `sorry`/`admit`. Database integrity is
`ok`. This is stock isolated compilation, not simp-disabled certification.

## Active pending run

Run root:
`.lake/private/T77-error-fix-20260923/pending-run-20260923`.

The four manifests are pairwise disjoint and cover 1,662 modules / 13,102
baseline-pending rows. Each worker has its own one-link database copy. Workers
000 and 001 are active in detached screen sessions; workers 002 and 003 are
prepared and will start one-for-one as a local slot becomes available, with a
hard ceiling of six concurrent campaign workers. The original four T76 workers
remain active and untouched.

The `monitor-isolated-trace-compile` heartbeat now monitors both runs, launches
only the two prepared local shards as slots free, validates and merges into new
copies, and then retries audited T76 failures using the reviewed implementation.
It is forbidden from provisioning cloud resources or mutating any original,
baseline, or frozen database.

Whole-tree coverage and simp-disabled certification remain unclaimed.
