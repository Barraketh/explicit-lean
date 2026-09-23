# T76 isolated stopped-trace compilation

Status at 2026-09-23T09:42:45Z: **COMPLETE, VALIDATED, AND MERGED TO A NEW COPY**.

This run consumes every collected partial trace bundle for the 2,867 modules
whose candidate rows were labelled `record_failed` by the stopped Scaleway
run. It does not record new traces and does not use cloud resources.

The recovery harness authenticates the original staged transformation and raw
trace identity, finalizes the emitted subset using global source-site ordinals,
renders complete command-level replacements, and stock-compiles the result.
Commands with a missing or failed trace remain precise per-command errors. To
isolate otherwise valid replacements, only failed theorem or lemma proof bodies
are replaced with `by sorry`, and only in ephemeral scratch module copies.
Definitions, instances, abbreviations, and examples are never masked. A
fail-closed persistence guard rejects any `sorry` or `admit` token before a
replacement can enter SQLite.

## Inputs and partition

- Harness commit: `f13aa0f19feeff474b340ed8fb82a0d12c0972c6`.
- Immutable trace artifacts:
  `.lake/private/T65-scaleway-full-20260922/results-stopped-analysis`.
- Baseline merged database copy:
  `.lake/private/T65-scaleway-full-20260922/mathlib-db-stopped-merged.sqlite3`.
- Run root: `.lake/private/T76-isolated-trace-20260923`.
- Four writable database copies began with SHA-256
  `59ce60baa642d759e09f1b9b481354c229b399018d0a41497ba0d6ad92f2e55d`
  and passed `PRAGMA integrity_check`.
- The manifests are disjoint and their union is exactly the 2,867
  `record_failed` modules: 717, 717, 717, and 716 modules respectively.
- Manifest SHA-256 values are `5d273790992503946f711137b93dfe77b11de7d1771612d2e362ff564ed5bef9`,
  `a1c744699eb96998fff27aecd726081c487837ef82240b8f9fcc44b0421d17c3`,
  `c8f05737a9ecf76fb6f6977dcf0bcd559b3866413ae3d74757e7a1109c4fb0e2`,
  and `dd62354d7181a0cc23f3ebd766c89303afe28f0d77411aa5cf014637bcc34727`.

## Launch and checks

Eight focused tests, Python byte compilation, and `git diff --check` passed.
An end-to-end disposable-database smoke test on
`Mathlib.Algebra.AffineMonoid.Irreducible` authenticated and finalized its one
emitted trace, produced one compiling success, and retained the other command
as `record_failed` because its trace was absent. The database integrity check
passed and no audited replacement contained a proof hole.

Four detached workers launched under these screen sessions:

- `explicit-lean-isolated-000`
- `explicit-lean-isolated-001`
- `explicit-lean-isolated-002`
- `explicit-lean-isolated-003`

Each worker had a separate manifest, writable SQLite database, scratch tree,
log, and terminal completion marker. All four workers exited zero. Their
completion reports and databases passed `PRAGMA integrity_check`; the manifests
remained pairwise disjoint and still covered exactly the original 2,867
modules. Across the four manifest-owned partitions, 30,057 command rows were
audited and 10,828 became compiled successes. Every audited success had
nonempty `replacement_text`, a null error, and no executable `sorry` or
`admit` token.

## Validated merged output

The result was merged into a new copy at
`.lake/private/T76-isolated-trace-20260923/mathlib-db-isolated-merged.sqlite3`.
Its SHA-256 is
`2c87114f971b9e7d17237fd8ed61ba3f307a502e6d379d732f017ec169202c04`
and its integrity check is `ok`. The merged database contains the unioned
30,057-row `isolated_trace_audit` table and these final replacement statuses:

- `success`: 13,489;
- `noop`: 3,956;
- `render_failed`: 13,282;
- `compile_failed`: 4,564;
- `record_failed`: 2,929;
- `pending`: 13,102.

The merge refined only manifest-owned rows whose exact baseline status was
`record_failed`; 30,057 rows were merged and 2,404 already-identical terminal
rows were accepted without changing their value. The original user database,
the stopped-run baseline, and all four worker databases were preserved. This
is isolated stock compilation evidence, not simp-disabled certification or
whole-tree acceptance.
