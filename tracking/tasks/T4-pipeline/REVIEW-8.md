# T4-pipeline final gate review (round 8)

Reviewed 2026-09-17 at T4 `12f1b86` (implementation `00d076d`). The
stale-publication fix is reviewed against the full implementation and tests;
no T4 implementation files were changed.

## Verdict

**PASS — merge eligible.** The prior REVIEW-7 lifecycle defect is closed:
each module clears only its exact prior publication and `.success` marker
before doing work, and a generated file is promoted from the private run tree
with `os.replace` only after an all-`replayed` acceptance.

## Prior-defect regression

An independent temporary-fixture driver reused a nonempty output directory
containing an old translated module and old success marker, then exercised
four current failure classes: identity rejection, `render_failed` from two
invocations, a classified `unresolved:` trace, and whole-module plus isolated
compile failure. In all four cases the exact target and marker were absent,
`published` was false, and an unrelated good module and its marker retained
their original bytes. A separate success fixture asserted that the target was
absent while compilation ran, the translated file lived below the run-local
temporary tree, and publication occurred only after the mocked acceptance.

The committed `publication_tests` adds the identity-failure stale-file and
marker regression to the suite. `clear_publication` refuses a real directory
at either exact publication path and never traverses or removes neighboring
modules.

## Bounded evidence

- `python3 -B Experiment/pipeline/check_pipeline.py`: **PASS, 246 checks**.
- Fresh seven-module run:
  `/tmp/t4-review8-seven-clean.0DoDgw/report.json` (SHA-256
  `df5d41088c4dfbc9eeac76f1cd95923311ad3f4f2dbae3a4bab1fe09510aa5cd`).
  Clean T1/main is `f8219efec8ddc1440c973de8756edfab22f9931e`; clean T2 is
  `8b57c4a008fcef73859eedbcc95f7605a58d5e8c`. Every module accepted identity
  and attempted rendering: **7/7 modules, 91/91 sites**. Totals are exactly
  **56 replayed / 1 unresolved / 18 render_failed / 16 compile_failed**;
  only `Nontrivial/Defs` and `ExistsUnique` were published. T1 and T2 were
  clean before and after (`dirty_before=false`, `dirty_after=false`); their
  shared T1 outputs were not touched.
- The two published files are the only files under the report's `Mathlib/`
  output tree. Running `simp_family_lint` over both translated files found
  **0 findings**.
- Independent identity fixtures passed for shuffled records, arbitrary and
  repeated `occurrence` values, and range/call mismatches failing closed (4
  checks). Matching uses the authenticated module/site/range/call tuple and
  invocation ordinals; no filename, list position, or occurrence fallback is
  present.
- `python3 -m py_compile Experiment/pipeline/*.py Experiment/simp_family_lint.py`,
  `git diff --check`, and the review diff scope all pass. The implementation
  change is limited to lifecycle clearing, run-local temporary generation,
  atomic promotion, and its focused regression test; no hashes, nonces,
  security/authentication expansion, or generated simp-family code was added.

