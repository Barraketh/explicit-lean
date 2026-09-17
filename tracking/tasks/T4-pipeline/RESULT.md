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

## Checks

| command | result |
| --- | --- |
| `python3 -B Experiment/pipeline/check_pipeline.py` | PASS, 224 checks, 2 s |
| focused marker/lint repros and `git diff --check` | PASS |

The six-module harness was not rerun: T1 is dirty at `0b4fd28` with
uncommitted producer/sidecar changes, and v2 output is not clean and available
for all six modules. No six-module result is claimed here; the prior clean
baseline is not current evidence.

Known limitations: per-branch `<;>` calls remain explicitly refused pending the
later per-branch rendering task; T1 currently has two newly visible attributed
sites not present in its older traced-copy count, and T1-origin trace defects
remain recorded as failures.
