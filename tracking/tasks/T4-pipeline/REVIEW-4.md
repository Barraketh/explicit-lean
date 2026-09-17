# T4-pipeline final merge-gate review (round 4)

Reviewed 2026-09-17 at T4 `7db88a8` (`task/T4-pipeline`). This is a fresh
full review of the T4 implementation and its fail-closed boundary. No T4
implementation files were changed.

## Verdict

**Critical defects: none found. Major defect: one integration defect remains.
Merge eligibility: HOLD / not eligible.** The required clean-tip run now
exists, but it exposes a site/trace cardinality mismatch described below.
T1 was clean at `0b4fd2875246f82b74b8bf8c0c319f8cdc689129` and T2 was clean at
`8b57c4a008fcef73859eedbcc95f7605a58d5e8c`, both before and after the run.

## Review findings

- **Site completeness:** `sites.find_sites` on the six Mathlib sources counts
  17, 1, 2, 8, 25, and 31 sites respectively, total **84**. The two
  `@[simp] lemma ... := by simp` same-line sites are detected; attribute spans
  are masked while later executable tactics remain visible. `Simp.simp` API
  text is excluded. T1's current committed traced copies/checker still report
  23 for `Function/Basic`, so that old detector/output is not evidence for
  this corrected denominator.
- **MAJOR — trace/site positional mismatch:** the fresh report has 25
  `Function/Basic` source records but only `trace_count: 23`; T1's
  `check_transcription.py` still passes its older 23-site detector. T4's
  `transcribe` stores traces by numeric filename index and `render_site` then
  consumes them by source-site index, so after the two same-line attribute
  sites at lines 698 and 700, traces are attached to later source sites by a
  shifted position. In this run the shifted records did not produce an
  observed `replayed` result (the three Function/Basic replays precede the
  gap), but their failures are not conservatively attributable to the named
  source sites, and a future coincidental compile could be a false replay.
  T4 must refuse any module whose trace/site mapping is incomplete or require
  an authenticated occurrence mapping; the current 44/84 count is therefore
  not acceptance evidence.
- **Splice/source preservation:** direct adversarial checks passed for
  attribute-plus-tactic lines, top-level `(by simp : Nat)` ascriptions,
  Unicode prefixes, CRLF/trailing text, and multiple retained sites on one
  source line. Replacements are planned in original coordinates and applied
  right-to-left; retained calls remain adjacent to standalone unresolved
  markers.
- **Invocation grouping:** trace `invocation`/`invocations` metadata is
  consumed, observed executions are never content-deduplicated, and counts
  greater than one fail closed as `render_failed:multiple_invocations`.
- **Unresolved retention and lint:** unresolved and render-failed calls keep
  the original call; retained mid-line calls receive a preceding standalone
  `explicit_rw: unresolved` marker. `simp_family_lint` is run on replacement
  blocks before `replayed` can be reported. Focused forged-token and marker
  checks passed.
- **Isolation and attribution:** whole-module success is required for the
  fast path; otherwise per-site probes restore every other call to the
  original. Probe diagnostics are selected only when the diagnostic file and
  line lie in that site's replacement range; otherwise the status is
  `probe_inconclusive`, never an attributed site failure. The out-of-block
  diagnostic repro passed.
- **Read-only guarantees:** the harness refuses regeneration/output in the
  driven worktrees and records dirty state before/after. No T1/T2 writes were
  made by this review.

## Checks and counts

- `python3 -B Experiment/pipeline/check_pipeline.py`: **PASS, 194 checks**.
- Focused adversarial Python repros: **PASS, 9 checks** for the corrected
  84-site count, attribute/API exclusion, type-ascription preservation,
  Unicode/CRLF/trailing-source preservation, same-line marker aggregation,
  out-of-block diagnostic refusal, invocation refusal, and replacement lint
  gate.
- `python3 -m py_compile` on all T4 Python modules and `git diff --check`:
  **PASS**.
- The only available end-to-end report is stale (2026-09-16, old T1/T2 tips,
- Fresh six-module harness (external output, T1 `0b4fd287`, T2 `8b57c4a`):
  **84 records / 44 replayed / 1 unresolved / 19 render-failed / 18
  compile-failed / 2 probe-inconclusive**; all module reports recorded
  `dirty_before=false` and `dirty_after=false`. These counts are diagnostic,
  not acceptance evidence, because of the Function/Basic mismatch above.
- The prior 2026-09-16 report (old tips) was **82 / 45 / 1 / 27 / 9** and is
  explicitly rejected as current evidence.
