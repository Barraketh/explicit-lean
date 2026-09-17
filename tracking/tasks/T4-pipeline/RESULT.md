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
| `python3 -B Experiment/pipeline/check_pipeline.py` | PASS, 241 checks, 5 s |
| focused marker/lint repros and `git diff --check` | PASS |

T1/main is clean at `6313029` and T2 is clean at `8b57c4a`; the fresh run left
both statuses and T1 shared outputs unchanged. All seven configured modules
passed identity (`91/91` sites, `renderAttempted=true`). Replay totals were
`56 replayed`, `1 unresolved`, `18 render_failed`, and `16 compile_failed`.
The bounded `OptionBasicTraced` mapping added the requested seventh module.

Known limitations: per-branch `<;>` calls remain explicitly refused pending the
later per-branch rendering task; T1 currently has two newly visible attributed
sites not present in its older traced-copy count, and T1-origin trace defects
remain recorded as failures.
