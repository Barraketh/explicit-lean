# T61 source-command database

Status: completed for the bounded implementation and full pinned-tree extraction.

Implementation:
- `Experiment/source_command_db.py` adds validated positive `--jobs N` (default
  1) and bounded process-level extraction. At most N batch extractors run in
  private process groups; the coordinator alone validates records, checks TOCTOU
  hashes, and commits one complete batch transaction at a time. Completed
  batches may be observed out of order and progress/ETA is aggregate.
- SIGINT/SIGTERM, extractor failure, validation failure, and SQLite failure cancel
  peers, terminate and reap owned groups, roll back an incomplete transaction,
  leave `.partial` durable, and do not publish the final rename.
- The schema remains exactly the three tables `modules`, `imports`, `commands`.
  Resumption validates schema, foreign keys, integrity, source blobs/hashes,
  command ranges/hashes, and rejects drift/extra/corrupt rows.
- `Experiment/SourceCommandExtractor.lean` preserves all parsed header import
  modifiers while projecting imports to unique names in the three-table graph.
- `Experiment/check_source_command_db.py` covers jobs>1, cancellation,
  interruption, out-of-order completion, transactional partials, and
  resume-equivalence.

Focused checks:
- `python3 -B Experiment/check_source_command_db.py` — PASS.
- `python3 -B -m py_compile Experiment/source_command_db.py Experiment/check_source_command_db.py` — PASS.
- `git diff --check` — PASS.
- `lake build sourceCommandExtractor` — PASS (135 jobs).
- `lake build ExplicitLean ExplicitLeanMathlibAudit` — PASS (763 jobs; existing warnings only).

Production resume used `--jobs 2 --batch-size 16` against the preserved
192-module partial. Progress reached 2,000 and then 5,600 modules across
interrupt/resume attempts; aggregate ETA was reported on every committed batch.
The final output is now independently validated: 8,265 modules, 34,662 imports,
405,766 commands, 195,346,432 bytes. `stats`, full source/hash/range validation,
`PRAGMA foreign_key_check`, `PRAGMA integrity_check`, and internal import DAG
validation all pass. The later retained `.partial` is a valid 5,600-module
checkpoint; no source or schema mutation was made.

No simp coverage or translation claim is made.
