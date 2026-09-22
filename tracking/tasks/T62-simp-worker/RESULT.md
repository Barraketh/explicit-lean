# T62: module-scoped simp replacement worker

Implemented a manifest-driven worker that processes one module at a time in its
own writable SQLite copy. The SQL-derived `body` is never read. Each module's
full database source and SHA-256 are checked against the pinned Mathlib file;
command byte ranges and hashes are checked before candidate rows are touched.

The worker finds actual executable `simp` and `simp only` calls, maps their
UTF-8 byte ranges to queued command ordinals, and treats queued commands with
no selected calls as `noop`. It instruments only selected calls using
`ExplicitLean.SimpTrace`, validates selected trace identities including
noncontiguous source ordinals and invocation counts, renders through the
existing `explicit_rw` renderer without adding original-call comments, and
stock-compiles temporary full modules. Successful rows store the complete
rewritten command. Compilation fallback accumulates individually compiling
commands in source order. Each module's pending row updates commit in one
SQLite transaction, so an interrupted module remains resumable.

Recorder and renderer imports are added only to temporary sources. A clean
worktree builds `ExplicitLean.SimpTrace` and `ExplicitLean.ExplicitRw` once on
worker startup. No simp-disabled or certification pass is run.

## Checks

- `python3 -B Experiment/check_simp_replacement_worker.py` — passed 7 focused
  checks, including compiled nested executable tactic contexts, multiline
  `simp`/`simp only` record → identity → render → stock compilation, and a
  queued-row check proving `/- lead -/ example ... := by simp` is not committed
  as a noop. Non-target decoys and tactics following the multiline call are
  also checked.
- `python3 -B test/SimpTrace/test_trace_identity.py` — passed, including
  selected noncontiguous ordinals through finalization.
- `Experiment/pipeline/check_pipeline.py` local renderer/control fixture
  functions — 316 passed. This covers the `(by simp : Nat)` ascription case as
  well as existing pipeline controls; the full command still requires the
  unavailable external T1 worktree described below.
- `python3 -B test/SimpTrace/check_transcription.py` — all seven committed
  trace copies match their source, 91/91 sites.
- `python3 -B Experiment/check_source_command_db.py` — passed.
- `python3 -B -m py_compile` on the worker, replay module, trace identity, and
  finalizer — passed.
- `lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw` — passed (11
  jobs).
- `git diff --check` — passed.

The review correction generalized executable-site recognition in both the
renderer and recorder identity scanner. Tactic prefixes and layout contexts
are recognized without treating `simpa`, `dsimp`, attributes, comments, or
string contents as targets; balanced multiline call ranges preserve Unicode
character offsets, nested comments, and following tactic syntax. Both
scanners are checked for exact agreement on the new compiled syntax fixture.
In a read-only audit of the queued SQLite database, 68,281 pending target calls
were identified: 4,691 had unmatched opening delimiters under the previous
line-limited range detector, while none are unbalanced with the new ranges.
The same offset-masked scanning also fixes the prior same-line block-comment
false-negative classification. Attribute recognition now runs only after
comments and strings have been masked, matching the recorder's lexical order;
this prevents a comment-contained `@[` from swallowing later live code. The
read-only alignment audit covered 5,957 pending modules and found 80,633
executable target sites in their sources, including 68,281 owned by pending
queue rows, with zero renderer/recorder mismatches.

## Limits

The worker has not processed the production SQLite copy. The selected-site
recorder/render/compile path was exercised on a small Mathlib-importing fixture;
full corpus throughput and rare renderer shapes remain unmeasured. Job
partitioning, result-database merging, cloud provisioning, and later
certification are outside T62 ownership.
