# T77 isolated recovery and pending-site run

Status: active local campaign. Implementation commit:
`79b2f6aa7f854f2a4ef6b06b0ba8e436c6d06682`.
Exact bulk-record/batch-compile fast path commit:
`78189c32636004d62e50b611e6f2c997456960ac`.
Subsequent reviewed mechanism commits:

- `4780f5a`: terminal hypothesis closes;
- `bf32f05`: atomic, evidence-preserving trace refresh;
- `4816f8a`: ordinary-Lean `change.to` printing;
- `7537456`: audit-gated T76 failure refresh;
- `251a659`: authenticated Lean tactic-syntax ancestry extraction groundwork.

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
- An unbounded module first attempts one exact multi-site recorder invocation.
  It accepts the result only if the source-site key set and full trace identity
  exactly match the request; any defect discards the entire batch and retries
  every site independently. Rendered commands likewise get one exact combined
  module compile; a failure falls back to isolation from the already-compiled
  baseline and accumulates only individually compiling commands.
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
- A hypothesis-location close is emitted as the exact ordinary sequence
  `explicit_rw [...] at h; <recorded closer>`. Multiple or nonterminal closes
  remain refused. A real disposable retry compiled
  `Mathlib.Algebra.GroupWithZero.Basic.zero_pow_eq_zero` with its `@[simp]`
  annotation preserved and a 190-byte replacement.
- `change.to` is now printed as ordinary Lean in the captured local context,
  leaving implicits, instances, and universes to elaboration. Fresh real traces
  rendered `3` and `a + 0` and replayed successfully; authenticated term text
  is no longer lexically rewritten by the renderer.
- `--refresh-recorded` installs a durable shadow for the complete selected
  site set in one SQLite transaction before recording. Old bundle traces
  cannot re-enter after a failed, deferred, or interrupted refresh; prior
  evidence is archived. Exact recorder dictionaries reject Boolean/float key
  aliases and reauthenticate every invocation.
- Explicit render/compile failure retries may be selected from matching T76
  `isolated_trace_audit` evidence only when the row status and stage-specific
  trace state agree. Pinned source bytes and command hashes are still checked
  before work begins.
- The Lean syntax extractor authenticates the full module and exact site range,
  then reports the unique parsed `simp` ancestry and `<;>` child ranges. This is
  groundwork only: it performs no replacement and local macro syntax currently
  refuses the module rather than falling back to full elaboration.

## Verified checks

- 19 isolated-compile focused tests.
- 25 per-site/batch retry focused tests.
- 30 per-site/batch/audited-refresh focused tests after the refresh extensions.
- 15 renderer regressions.
- 122 renderer/layout checks and 16 focused renderer regressions after the
  close and ordinary-term changes.
- 11 replacement-worker checks, including real recorder and Lean compile
  fixtures.
- Ordinary `change.to` recorder/render/replay fixtures, the SimpTrace build,
  T9 identity, and T22 source-argument checks passed.
- The syntax ancestry extractor passed seven focused checks, including a
  pinned `Mathlib.Logic.Basic` smoke and Unicode byte/scalar ranges.
- T9 trace identity tests and T22 source-argument tests.
- 316 pipeline checks excluding the unavailable historical T1/T2
  worktree-dependent site-count and end-to-end checks.
- `py_compile` and `git diff --check` passed for the changed implementation.
- Independent trust review passed the final database, manifest, transactional,
  source-provenance, and renderer boundaries.

## Real smoke evidence

The disposable database
`.lake/private/T77-error-fix-20260923/post-review-smoke/mathlib-db.sqlite3`
was copied from the stopped-run baseline. Four commands in
`Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne` were recorded
per site and stock-compiled as full-command replacements:

- ordinal 35: `compiled_success`, 519-byte replacement;
- ordinal 36: `compiled_success`, 463-byte replacement.
- ordinals 37 and 69: one authenticated two-site bulk recording and one
  combined candidate compile produced two further `compiled_success` rows.

All replacements are nonblank ordinary `explicit_rw`, contain no executable
`simp`/`simpa`/`dsimp`, and contain no `sorry`/`admit`. Database integrity is
`ok`. This is stock isolated compilation, not simp-disabled certification.

The disposable close smoke at
`.lake/private/T77-error-fix-20260923/close-smoke2/mathlib-db.sqlite3` also has
integrity `ok`; ordinal 63 of `Mathlib.Algebra.GroupWithZero.Basic` is a compiled
success with no executable simp-family or proof-hole token. Five separate
fresh-recording pp-all/change smokes reached independent recorder blockers
(`not_isEmpty_of_nonempty`, `Fin.succAbove_ne`, or `Std.le_refl`) and therefore
correctly persisted no replacement. They are not counted as successes.

## Active pending run

Run root:
`.lake/private/T77-error-fix-20260923/pending-run-20260923`.

The four manifests are pairwise disjoint and cover 1,662 modules / 13,102
baseline-pending rows. Each worker has its own one-link database copy. Workers
000 and 001 are active in detached screen sessions; workers 002 and 003 are
prepared and will start one-for-one as a local slot becomes available, with a
hard ceiling of six concurrent campaign workers. The original four T76 workers
remain active and untouched.

Workers 000 and 001 were interrupted with targeted `SIGINT` after the fast path
passed review. Their SQLite transactions remained consistent; pre-restart
logs/completion/exit markers are preserved under `prebatch-79b2f6a` names.
Both resumed from their existing databases at the fast-path commit, reusing
already authenticated site traces and completed command results.

The `monitor-isolated-trace-compile` heartbeat now monitors both runs, launches
only the two prepared local shards as slots free, validates and merges into new
copies, and then retries audited T76 failures using the reviewed implementation.
It is forbidden from provisioning cloud resources or mutating any original,
baseline, or frozen database.

Whole-tree coverage and simp-disabled certification remain unclaimed.
