# T4-pipeline: end-to-end replay harness

Implemented the REVIEW-1 fixes in `Experiment/pipeline/`:

- Attribute spans are masked while executable tactics after attributes remain visible; Lean.Meta.Simp API forms remain excluded.
- Isolated probe diagnostics are attributed only when the target file and line are inside that replacement block; otherwise status is `probe_inconclusive`.
- Retained mid-line originals receive a standalone preceding `explicit_rw: unresolved` marker at enclosing indentation.
- Replacement blocks are checked by `simp_family_lint` before a site can become `replayed`.
- Top-level term ascriptions terminate site ranges and are preserved.
- Spec `invocation`/`invocations` metadata is consumed; executions are never deduplicated by trace content. Multiple invocation rendering remains refused as requested.
- Diagnostic line-mapping documentation now describes the implemented file-and-block mapping.

## Checks

| command | result |
| --- | --- |
| `python3 -B Experiment/pipeline/check_pipeline.py` | PASS, 194 checks, 5 s |
| focused marker/lint repros and `git diff --check` | PASS |

The six-module harness was not rerun in this round because T1 remains dirty at
`db97d8f` with its recorder `.olean` unavailable; no six-module result is
claimed here. The previous clean baseline is intentionally not repeated as
current evidence.

Known limitations: per-branch `<;>` calls remain explicitly refused pending the
later per-branch rendering task; T1 currently has two newly visible attributed
sites not present in its older traced-copy count, and T1-origin trace defects
remain recorded as failures.
