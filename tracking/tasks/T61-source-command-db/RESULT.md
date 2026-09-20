# T61 source-command database

Status: completed for the bounded implementation and focused fixtures.

The schema is exactly the agreed three user tables (`modules`, `imports`,
`commands`) with no analysis or versioning state. The Lean extractor uses
`Parser.parseHeader`, normalized explicit import names, sequential parser
state, canonical UTF-8 byte positions, syntax kinds, and excludes only EOI.
A bounded exact-import frontend fallback handles source-local parser syntax.

The Python builder restricts discovery to `Mathlib.lean` and
`Mathlib/**/*.lean`, validates TOCTOU hashes, records, ranges, hashes and
imports, checks graph acyclicity, runs SQLite foreign-key/integrity checks,
and atomically renames a fresh database. Existing destinations require
`--overwrite`; package-tree output is rejected.

Checks:

- `python3 -B Experiment/check_source_command_db.py` — PASS.
- `python3 -m py_compile Experiment/source_command_db.py Experiment/check_source_command_db.py` — PASS.
- `lake build sourceCommandExtractor` — PASS.
- Fresh pinned three-module sample (`Logic.Basic`, `Logic.Function.Basic`,
  `Logic.ExistsUnique`) — 3 modules, 14 imports, 663 commands, 262144 bytes.
- A full-tree attempt with the initial single-process extractor was stopped by
  OS exit 137 after 42 records; no partial database was published. The final
  builder batches extractor workers to bound frontend memory. A complete
  full-tree run was not claimed because the measured initial run was not
  runtime-bounded.

No simp coverage or translation claim is made.
