# T6 structural multi-invocation rendering

Implemented deterministic source-structural expansion in
`Experiment/pipeline/replay_module.py`. Complete invocation records are mapped
by ordinal to the leaves of the smallest supported binary `<;>` spine. The
renderer preserves branch binders/order, copies existing non-tail suffixes to
each leaf, keeps the original `simp` call adjacent as a comment, and refuses
missing, duplicate, gapped, unsupported, or mismatched metadata without
partial replay. `sites.splice` now accepts an authenticated expanded source
range. Fixtures cover groups A--D, nested four-leaf expansion, identical step
lists, non-tail suffixes, comment adjacency, exact ordering/count, and
malformed metadata.

## Checks

| command | result |
| --- | --- |
| `python3 -B Experiment/pipeline/check_pipeline.py` | PASS, 265 checks |
| structural fixture compile with T2 `lake env lean` | PASS |
| fresh seven-module replay gate | PASS; 91 identity, 59 replayed, 5 unresolved, 6 render_failed, 0 structurally_refused, 21 compile_failed |
| `git diff --check` | PASS |

The authoritative fresh report is `/private/tmp/t6-seven-review2/report.json`.
It accepted all 91 identities, with totals of 59 replayed, 5 unresolved, 6
render_failed, 0 structurally_refused, and 21 compile_failed (91 total). The
earlier 2 render_failed + 4 structurally_refused split was a stale/older
classification and is superseded by that report. Former
multi-invocation sites with complete, replayable traces (including
`Function/Defs.lean:139` and the replayable `Logic/Basic.lean` leaves) now
render structurally; trace-side unresolved and compile defects remain visibly
unresolved/failing. Summary accounting includes `structurally_refused` as its
own machine-readable bucket, and every status total reconciles to the site
total.
