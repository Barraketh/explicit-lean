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

- `python3 -B Experiment/check_simp_replacement_worker.py` — passed 5 focused
  checks, including selected-site record → identity validation → render → stock
  compile and a transactional false-positive `noop` fixture.
- `python3 -B test/SimpTrace/test_trace_identity.py` — passed, including
  selected noncontiguous ordinals through finalization.
- `python3 -B test/SimpTrace/check_transcription.py` — all seven committed
  trace copies match their source, 91/91 sites.
- `python3 -B Experiment/check_source_command_db.py` — passed.
- Existing `Experiment/pipeline/check_pipeline.py` local fixture/control
  functions — 316 passed. The full command stops at its external-worktree
  precondition because `/Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture`
  is absent; its end-to-end T1/T2 replay was not run.
- `python3 -B -m py_compile` on the worker, replay module, trace identity, and
  finalizer — passed.
- `lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw` — passed (11
  jobs).
- `git diff --check` — passed.

## Limits

The worker has not processed the production SQLite copy. The selected-site
recorder/render/compile path was exercised on a small Mathlib-importing fixture;
full corpus throughput and rare renderer shapes remain unmeasured. Job
partitioning, result-database merging, cloud provisioning, and later
certification are outside T62 ownership.
