# T4-pipeline: end-to-end replay harness

Implemented the simp-trace-v2 pre-render source-site bijection and the
REVIEW-1/2 fixes in `Experiment/pipeline/`:

- Attribute spans are masked while executable tactics after attributes remain visible; Lean.Meta.Simp API forms remain excluded.
- Isolated probe diagnostics are attributed only when the target file and line are inside that replacement block; otherwise status is `probe_inconclusive`.
- Retained mid-line originals receive a standalone preceding `explicit_rw: unresolved` marker at enclosing indentation.
- Replacement blocks are checked by `simp_family_lint` before a site can become `replayed`.
- Top-level term ascriptions terminate site ranges and are preserved.
- Spec `invocation`/`invocations` metadata is consumed; executions are never deduplicated by trace content. Multiple invocation rendering remains refused as requested.
- Diagnostic line-mapping documentation now describes the implemented file-and-block mapping.
- v1 traces and any incomplete, malformed, extra, duplicate, range, call, or
  invocation-mismatched v2 set fail closed as `identity_failed` before
  rendering or output writes; machine-readable categories cover each failure.
- Each module now gets a fresh T4-owned `trace-runs/<name>-*/stage`, `raw`, and
  `final` tree. Staged `=>trace` paths target run-local raw files; the T1
  environment compiles the staged copy, the explicit-path finalizer writes
  final v2 records, and T4 consumes only that final directory.

## Checks

| command | result |
| --- | --- |
| `python3 -B Experiment/pipeline/check_pipeline.py` | PASS, 240 checks, 2 s |
| focused marker/lint repros and `git diff --check` | PASS |

T1 is clean at `30fb849` and T2 is clean at `8b57c4a`; the focused real-module
run left both statuses and T1 shared outputs unchanged. The six-module harness
is deferred because T1's committed finalizer still verifies hard-coded trace
paths and rejects T4's staged raw-root paths (`traced source differs from
deterministic transform`). The parameterized deterministic-transform follow-up
must land before identity/replay counts are reported. Focused lifecycle mocks
cover the five-path CLI, raw-v1/final-v2 separation, repeat-run isolation, and
missing-final fail-closed behavior.

Known limitations: per-branch `<;>` calls remain explicitly refused pending the
later per-branch rendering task; T1 currently has two newly visible attributed
sites not present in its older traced-copy count, and T1-origin trace defects
remain recorded as failures.
