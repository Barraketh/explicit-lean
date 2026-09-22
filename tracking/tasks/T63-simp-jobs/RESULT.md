# T63 simp replacement job coordinator

Implemented plain module manifests, deterministic weighted job fan-out, SQLite
backup copies, queue status reporting, retry manifest generation, and a
transactional merger for independently updated worker databases.

The manifest format is UTF-8 text with one exact module name per nonblank line.
`prepare` sorts module names within each job and uses greedy weighted partitioning
over candidate count and source byte size. It does not modify the source DB and
refuses an existing output directory. Each job gets a consistent SQLite backup
of the full database.

The merger accepts job directories containing `modules.txt` and
`mathlib-db.sqlite3`. It verifies the required table schemas, SQLite integrity,
all original `modules`/`imports`/`commands` content, queue keys, manifest
disjointness, assigned result shapes, and unassigned queue mutations. A single
`BEGIN IMMEDIATE` transaction validates and applies every result; any conflict
rolls back the complete merge. Identical terminal results are idempotent,
interrupted pending rows leave primary unchanged, and stale pending rows from
older independent copies cannot reset a terminal primary result.

## Reproducible checks

- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 synthetic tests
  passed, including partition coverage/balance, DB fan-out, resume, idempotence,
  conflicts and rollback, overlapping/malformed manifests, schema/source drift,
  unassigned mutations, result validation, status and interrupted jobs.
- `python3 -m py_compile Experiment/simp_replacement_jobs.py
  Experiment/merge_simp_replacement_dbs.py
  Experiment/check_simp_replacement_jobs.py` — passed.
- `git diff --check` — passed.

The local orchestration gate uses a dummy row updater against isolated job
copies. It does not invoke the T62 recorder worker or establish Lean compilation
results; those integration checks depend on the worker implementation.

The supplied task worktree did not contain the populated campaign database, so
fan-out and merging were exercised against synthetic databases. The empty
untracked `mathlib-db.sqlite3` present at task start was not included in the
commit.
