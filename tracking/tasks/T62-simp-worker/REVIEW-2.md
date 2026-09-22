# T62 simp replacement worker review 2

Review target: `a1d261f62197f24bb3935deefcf85e1cae8d37b4` (T62 worker plus
the nested-site fix), compared with `46f560598286be5ea88b5186c46146960e07eba4`.

## Result: FAIL

Two reproduced P1 source-accounting defects prevent accepting the worker. Both
can misclassify executable `simp` sites in valid Lean source. The focused
`all_goals` regression passes, but the detector still does not cover these
layouts.

### P1 — multiline simp arguments are truncated and fail recording

Both `Experiment/pipeline/sites.py::find_sites` and
`test/SimpTrace/trace_identity.py::find_sites` call `call_end` on the current
line only. For a multiline argument list, the recorded source site therefore
ends at the opening bracket. For example:

```lean
import Mathlib
example (n : Nat) : n + 0 = n := by
  simp only [
    Nat.add_zero,
  ]
```

The ordinary source compiles successfully with the stock compiler. The worker
detector reports the site text as only `simp only [` (and `simp [` for the
corresponding `simp` case). Calling the worker's actual `record_sites` path
fails before Lean runs, in `instrument_selected` / `_source_args`, with
`ValueError: unterminated simp argument list at site 0`. The candidate then
becomes `record_failed`, rather than receiving a replacement. This affects
ordinary multiline `simp` and `simp only` calls across the corpus.

Reproduction: a `simp only` proof in the format above passed
`compile_candidate` (`True`, 9.64 seconds); `record_sites` failed with the
unterminated-argument error. A multiline `simp [ ... ]` produced the same
recording failure.

### P1 — a leading block comment makes a real site a committed noop

`skip_line()` in `sites.py` and `_skip_line()` in `trace_identity.py` skip the
whole physical line whenever its trimmed text begins with `/-`. That happens
even if the block comment closes before executable Lean code on the same line.
The new comment masker preserves source positions, but `find_sites` still
discards that line before consulting the masked text.

This valid source compiles:

```lean
import Mathlib
/- lead -/ example : True := by simp
```

Both scanners return zero sites. I reproduced the worker using a pending
candidate row for the command containing that source: `process_module`
committed the row as `noop` with a NULL replacement and error. This silently
marks an executable source call as requiring no work, violating source-site
accounting and the worker's intended noop semantics.

## Checks run

- `python3 -B Experiment/check_simp_replacement_worker.py` — PASS (six focused
  checks, including recording, rendering and stock compilation of
  `all_goals simp`).
- `python3 -B test/SimpTrace/test_trace_identity.py` — PASS.
- `python3 -B Experiment/pipeline/check_pipeline.py` — could not complete; the
  checkout reports `not a worktree: /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture`.
- Stock compilation of the valid multiline `simp only` example — PASS.
- Stock compilation of the valid leading-block-comment example — PASS.
- Worker recording of multiline examples — FAIL as detailed above.
- Worker processing of the leading-block-comment candidate — incorrectly
  committed `noop` as detailed above.

The UTF-8 character-to-byte mapping and command ownership path are covered by
the focused test and code inspection. Module result updates are grouped under
`BEGIN IMMEDIATE` and guarded by `status='pending'`; however, I did not run a
fault-injection test for SQLite rollback/idempotence. No implementation files
were changed during this review.
