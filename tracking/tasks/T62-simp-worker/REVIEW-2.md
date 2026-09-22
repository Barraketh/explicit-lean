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

## Review 3: re-review of `6e8abbf` (source commit `966af2d`)

Review target: `6e8abbf4416d1dc67b868a8042195a540441c3a2`.

### Result: FAIL — the two prior P1s are closed, one source-accounting P1 remains

The multiline-range and leading-block-comment regressions from review 2 are
closed in the worker's end-to-end checks. The generalized range scanner also
passed the boundary probes below. However, a full read-only scan of all queued
modules found a recorder/renderer disagreement in two modules. In one module,
19 queued executable simp sites are absent from the renderer list. Since
`align_sites` rejects a target present in the recorder but absent from the
renderer, the worker marks candidates `worker_failed` instead of translating
them (and can fail unrelated queued false positives in that module as well).

### P1 — the two scanners mask comments and attributes in opposite order

The renderer calls `mask_comments_and_strings(mask_attributes(source))`, while
the recorder calls `_mask_attributes(_mask_comments(source))`. The renderer's
`mask_attributes` does not skip comments inside attribute syntax. Mathlib has
doc comments nested in attributes, for example:

```lean
@[to_dual /-- `Ioi a` is the left-open right-infinite interval $(a, ∞)$. -/]
```

The `@[` in that doc comment is seen as a real attribute opener by the
renderer masker. Bracket characters in the doc text then make it blank source
code through a later `]`, including executable simp sites. The recorder masks
comments first and finds those sites, so the scanners disagree.

Reproduction against the read-only index:

- `Mathlib.Order.Interval.Set.Basic`: recorder finds 31 pending target sites;
  renderer finds 12. Nineteen queued targets are missing. The first is
  `simp only [isMin_iff_forall_not_lt, eq_empty_iff_forall_notMem, mem_Iio]`
  at character span `14637:14709`, command ordinal 106.
- `Mathlib.Order.Interval.Set.Defs`: the source scanners report 4 recorder
  targets and 0 renderer targets. They are in `to_dual_insert_cast` commands
  with no queued target rows, but the module has two pending false-positive
  rows (ordinals 5 and 8; `@[... attr := simp ...]` text). Since the worker
  calls module-wide `align_sites` before determining that these pending rows
  have no owned target sites, the disagreement makes them `worker_failed`
  instead of the intended `noop`.

A disposable writable database containing the exact Set.Basic module source,
all of its command hashes, and one pending row for ordinal 106 reproduced the
failure: `align_sites` raises at `14637:14709`, and `process_module` commits
that row as `worker_failed`. The report-only review worktree was not used to
modify any implementation file.

### Read-only production-index audit

I independently scanned the 5,957 modules with pending candidates in
`/Users/ptsier/projects/explicit-lean/mathlib-db.sqlite3` using a SQLite
`mode=ro` connection. `PRAGMA quick_check` returned `ok`; the database had
51,322 pending rows across those modules. For every module I compared exact
`(start, end, callText)` identities from both scanners, and counted recorder
`simp`/`simp only` sites whose UTF-8 byte range belonged to a pending command.
For those same sites I reconstructed the former line-limited range from the
source and checked delimiter balance while ignoring nested comments and
quoted strings. Results:

| Measure | Result |
| --- | ---: |
| Recorder target sites mapped to pending commands | 68,281 |
| Former line-limited ranges with unmatched delimiters | 4,691 |
| New recorder ranges with unmatched delimiters | 0 |
| Candidate modules with recorder/renderer identity disagreement | 2 |
| Pending target sites missing from renderer in `Interval.Set.Basic` | 19 |

Thus the claimed 68,281 / 4,691 / 0 counts reproduce, but the balance check
alone does not establish scanner agreement or corpus coverage. The current
renderer list accounts for 68,262 of the pending recorder targets because of
the 19-site disagreement above.

### Range and source-argument probes

- Both scanners returned identical ranges for multiline `simp` and
  `simp only` calls with nested delimiters and nested block comments.
- The captured ranges stopped before a following `<;> rfl` tactic and before
  the next top-level command.
- Quoted strings containing commas, `]`, `;`, and parentheses, plus multiline
  triple-quoted strings containing those characters, did not truncate a call.
- `_source_args` returned the expected two argument spans for quoted/triple-
  quoted and nested-comment cases.
- A Unicode prefix produced the expected differing character/UTF-8 byte
  offsets; the existing command-mapping regression passed.
- The new worker fixture successfully traced, validated, rendered, and
  stock-compiled the three-site module containing both multiline forms, the
  leading block comment, nested comments, and following tactics/commands.

### Checks run

- `python3 -B Experiment/check_simp_replacement_worker.py` — PASS (7 checks,
  including the exact multiline record/render/compile and queued leading-
  comment candidate regressions).
- `python3 -B test/SimpTrace/test_trace_identity.py` — PASS.
- `python3 -B Experiment/check_source_command_db.py` — PASS.
- `python3 -B -m py_compile Experiment/pipeline/sites.py test/SimpTrace/trace_identity.py Experiment/simp_replacement_worker.py` — PASS.
- Pipeline renderer/control fixture functions — PASS (316 checks). The full
  `check_pipeline.py` entry point still cannot complete here because its
  external T1/T2 worktrees are unavailable.
- Full pending-module site-range audit — counts above; found the two
  scanner-disagreement modules.

The remaining P1 is fixed by making both scanners apply comment masking before
attribute masking, or by making the attribute masker comment-aware, then
rerunning the all-module identity audit. No implementation files were changed
during this review.

### Final re-review of `24158e3` — PASS

The author applied the mask-order correction in
`Experiment/pipeline/sites.py`: comments and strings are masked before
attributes. The exact corpus cases from the prior finding now agree:

- `Mathlib.Order.Interval.Set.Basic`: 31 renderer sites = 31 recorder sites;
  the first previously missing site at `14637:14709` is present in both.
- `Mathlib.Order.Interval.Set.Defs`: 4 renderer sites = 4 recorder sites.
  A disposable database containing pending attribute-only candidate ordinal
  5 now commits it as `noop`, with NULL replacement and error, despite the
  module's four real target sites being in nonqueued commands.

The full read-only audit was rerun over all 5,957 modules with pending
candidates. All `(start, end, callText)` lists now match exactly between the
renderer and recorder scanners. It reproduced the counts above: 68,281 target
sites mapped to pending commands, 4,691 ranges unmatched by the previous
line-limited detector, zero unbalanced ranges with the new detector, and zero
scanner identity mismatches. The database `quick_check` remained `ok`.

The author’s worker test now exercises both prior P1 reproductions end to end:
multiline `simp`/`simp only` calls pass recording, identity validation,
rendering and stock compilation, and a queued call following a leading block
comment no longer becomes a noop. The suite also checks nested block comments,
following `<;> rfl` tactics, and following top-level commands. Additional direct
range probes with nested delimiters, quoted strings, multiline triple-quoted
strings, comment decoys and a Unicode prefix passed; `_source_args` returned
the expected argument spans, and the site range stopped before the next tactic
and command.

Final checks:

- `python3 -B Experiment/check_simp_replacement_worker.py` — PASS (7 checks).
- `python3 -B test/SimpTrace/test_trace_identity.py` — PASS.
- `python3 -B Experiment/check_source_command_db.py` — PASS.
- `python3 -B -m py_compile Experiment/pipeline/sites.py test/SimpTrace/trace_identity.py Experiment/simp_replacement_worker.py` — PASS.
- Pipeline renderer/control fixture functions — PASS (316 checks).
- Full pending-module scanner audit — PASS (5,957 modules, zero identity
  mismatches).
- `git diff --check` — PASS.

I found no remaining concrete issue in the reviewed worker changes. The full
pipeline entry point that requires external T1/T2 worktrees was not run; the
focused worker path and local pipeline fixture checks passed. No implementation
files were changed in the review worktree.
