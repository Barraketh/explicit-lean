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
| `python3 -B Experiment/pipeline/check_pipeline.py` | PASS, 261 checks |
| structural fixture compile with T2 `lake env lean` | PASS |
| fresh six-module replay gate | PASS to completion; 54 replayed, 19 compile_failed, 6 render_failed, 5 unresolved |
| requested fresh seven-module replay gate | BLOCKED before rendering: T1 worktree lacks `OptionBasicTraced.lean` |
| `git diff --check` | PASS |

The six-module run used T1 `task/T1-trace-capture` (`7c4119a`) and T2
`task/T2-explicit-rw` (`8b57c4a`), writing only to
`/private/tmp/t6-six-structural-r2` and the final two-module confirmation to
`/private/tmp/t6-two-structural-final`. Former multi-invocation sites with
complete, replayable traces (including `Function/Defs.lean:139` and the
replayable `Logic/Basic.lean` leaves) now render structurally; trace-side
unresolved and compile defects remain visibly unresolved/failing.
