# T79 term-free simp operations and `explicit_rw_v2`

Implemented a separate operational recorder and replay syntax without changing
the legacy `explicit_rw` format.  The recorder emits committed operations in
execution order with their exact current-expression child path, rule identity,
direction, phase, variant, extra-argument count, premise terminal summaries,
and terminal goal action.  The source-facing JSON contains no expressions,
proof terms, or fingerprints.

`explicit_rw_v2` replays the closed readable operations directly.  It supports
global, equation-indexed, and local-context rules; forward and reverse
rewrites; exact positions; explicit premise closures; beta/iota/projection/zeta
and named unfolding; hypothesis locations; and term-free terminal closure.
It does not call or import `Lean.Meta.Simp`, discover a rule, or search another
position.  Simprocs are parsed only to produce an explicit residual failure.

The Python renderer converts operation JSON to `explicit_rw_v2` source and
fails closed on unsupported operations.  Current explicit residuals are
simprocs, builtins, source-syntax/opaque rules, traversal without a principled
raw position, nested premise simplification, and the remaining uncommon
definitional operations.

Independent focused review found and the implementation fixed two major
issues before integration: legacy local-rule/local-definition fingerprints
were leaking into the new IR, and metadata child paths were one level too
shallow.  The operational IR now has narrow identity-only origin/reduction
types, and metadata traversal records child `0` exactly.

Verified checks:

- `lake build ExplicitLean:shared`
- `lake env lean test/SimpTrace/T79OperationalReplay.lean`
- `lake env lean test/ExplicitRw/Definitional.lean`
- `python3 -B Experiment/check_render_simp_operations.py` (6 tests)
- `python3 -B Experiment/check_simp_operations.py`
- `python3 -B Experiment/check_no_simp_family.py`
- `git diff --check`

The recorder regression covers declaration, contextual-local, beta, nested
application, and metadata paths.  The replay regression covers rule kinds,
all phase spellings, reverse direction, extra arguments, premises, reductions,
goal/hypothesis locations, proposition rules, exact-path refusal, and simproc
refusal.  This is not a whole-tree or simp-disabled certification claim.

## Local failed-row retry driver

Added `Experiment/retry_simp_operations.py` as a separate local retry path for
a writable merged `simp_replacements` database.  It selects all remaining
`record_failed`, `render_failed`, and `compile_failed` rows without requiring
an audit-table gate; instruments selected source sites with labelled
term-free observations; renders `explicit_rw_v2`; and compiles a module-level
candidate.  If the combined candidate fails, it compiles selected rows
incrementally to identify the specific residual.  Results are committed in a
single transaction per module with a status compare-and-swap, and only the
selected rows are updated.  Unsupported locations/operations and compile
failures retain explicit row-level diagnostics.  Recorder/probe scratch
directories are removed in `finally`; only the final report remains in the
artifacts directory.

Before reading module content, the driver requires the database path to equal
`module.replace('.', '/') + '.lean'`.  It then trusts the pinned-source model
only after exact DB/source byte equality.  A trusted source containing the
reserved `SIMP_OPERATIONS_SITE ` log marker is refused before instrumentation,
and the parser accepts the marker only at the beginning of a stripped Lean
log line.  This is deliberately a simple trusted-source boundary: this change
adds no hash, random authorization token, provenance record, or receipt.

The focused synthetic SQLite smoke proves selection of all three failure
statuses, one exact `Nat.add_zero` observation/replay, preservation of an
existing successful row and a pending row, and cleanup of the module scratch
directory.  Negative checks prove a noncanonical module path is rejected
before the source reader is called, and a reserved-marker collision is
rejected before the recorder or compiler runs; a prefixed marker in log text
is ignored.  No live worker database was opened or modified, and no real
merged database retry was run.

Additional verified checks:

- `python3 -B Experiment/check_retry_simp_operations.py`
- `python3 -B Experiment/check_simp_operations.py`
- `python3 -B Experiment/check_render_simp_operations.py` (6 tests)
- `lake env lean --load-dynlib=<ExplicitLean shared library> test/SimpTrace/T79OperationalRecording.lean`
- `lake env lean test/SimpTrace/T79OperationalReplay.lean`
- `lake env lean test/ExplicitRw/Definitional.lean`
- `python3 -B -m py_compile Experiment/retry_simp_operations.py Experiment/check_retry_simp_operations.py Experiment/check_simp_operations.py`
- `git diff --check`

The direct `lake env lean test/SimpTrace/T79OperationalRecording.lean` command
without `--load-dynlib` aborts because the recorder uses Lean's native
`Lean.Meta.Simp.Engine.simp` implementation; the shared-library invocation
above succeeds.  This remains focused local validation, not campaign
certification.
