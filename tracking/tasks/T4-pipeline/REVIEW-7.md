# T4-pipeline final gate review (round 7)

Reviewed 2026-09-17 at T4 `0166a54`, including `e5df160`. The clean-tip
seven-module evidence is `/private/tmp/t4-seven-review7.sTyafH/report.json`,
generated 2026-09-17T13:00:41 against T1 `631302900d6ead65755d5a407b3b768fbb8359ac`
and T2 `8b57c4a008fcef73859eedbcc95f7605a58d5e8c`; both were clean before and
after that run. A later rerun reproduced the totals but saw concurrent T1
activity (`0fb25ac`, dirty at start), so it is diagnostic only.

## Verdict

**One major lifecycle defect; merge HOLD / not eligible.** No hidden
filename/index fallback, stock-artifact fallback, simp-family leakage in
rendered replacements, weakened identity validation, or scope creep was found.

## Finding

### M1 — reused `--out` can expose stale translated output after identity failure

`replay_module()` returns from its identity-rejection branch before creating or
overwriting the translated target. It also does not require `--out` to be empty
or remove a prior target. Therefore a prior successful run can leave
`--out/Mathlib/<module>.lean` present while the current report says
`identity_failed`, `renderAttempted=false`, and claims no output write. I
reproduced this with a temporary output directory containing a stale translated
file and a monkeypatched empty trace set: the result was identity rejected and
the stale file remained byte-for-byte unchanged. The fix should refuse a
non-fresh output target (or otherwise make stale-target presence an explicit
failure) before any run; do not delete user files implicitly.

## Evidence passed

- `python3 -B Experiment/pipeline/check_pipeline.py`: **PASS, 241 checks**.
- Clean-tip report: all **7/7 modules** accepted v2 identity, all **91/91
  source sites** matched, and every module had `renderAttempted=true`. Totals
  are exactly **56 replayed / 1 unresolved / 18 render_failed / 16
  compile_failed**; no `probe_inconclusive` or `identity_failed` records.
- The clean report's run-local trees contain only raw `simp-trace-v1` and final
  `simp-trace-v2` records. Finalizer exits are zero for all seven modules; raw
  and final record counts are 7, 17, 1, 3, 8, 30, and 47, respectively.
- Independent shuffled-record and same-call-range fixtures accepted identity;
  altered ranges/call text, missing/extra/duplicate records, v1 records and
  invalid invocation ordinals rejected before rendering. Matching uses
  `modulePath`, `siteOrdinal`, `startChar`, `endChar`, and exact `callText`,
  not trace filenames, list order, or `occurrence` values.
- A direct v2 renderer fixture produced `explicit_rw [h at []]`; all rendered
  records from the clean report passed `simp_family_lint` before replay status.
- `rg` audit found no `meas_out` access in the implementation path and no
  fallback from final v2 records to raw v1 or stock artifacts. T1/T2 status was
  clean after the authoritative run; the T4 worktree and diff are clean aside
  from this review file.

