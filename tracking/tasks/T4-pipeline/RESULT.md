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
| `python3 -B Experiment/pipeline/check_pipeline.py` | PASS, 189 checks, 5 s |
| six-module harness against T1 `a066bc1c` / T2 `dbb6c703` | PASS, 84 sites, 145 s |

Harness counts: IsEmpty 15/17 replayed; Nontrivial 1/1; Function/Defs 1/2;
ExistsUnique 8/8; Function/Basic 3/25 (13 compile failures, 6 render failures,
1 unresolved, 2 probe-inconclusive); Logic/Basic 16/31 (3 compile failures,
12 render failures). No site was falsely charged for an out-of-block probe
diagnostic. The full report is under `/private/tmp/t4-round2c.Mg8yPt/`.

A later rerun was intentionally not counted: T1 was being edited and its
recorder `.olean` was absent, so the harness produced `no_trace` for all sites.
The retry is a T1 stability blocker, not evidence of replay failure.

Known limitations: per-branch `<;>` calls remain explicitly refused pending the
later per-branch rendering task; T1 currently has two newly visible attributed
sites not present in its older traced-copy count, and T1-origin trace defects
remain recorded as failures.
