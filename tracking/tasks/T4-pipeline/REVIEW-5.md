# T4-pipeline simplified-v2 consumer review (round 5)

Reviewed 2026-09-17 at T4 `e94a72c` (`task/T4-pipeline`). This review is
consumer-only; no T4 implementation files were changed.

## Verdict

**Identity contract: PASS. Merge eligibility: HOLD pending the six-module
integration gate.** The consumer recomputes source sites from the exact
unpinned-source text and matches trace records only by `modulePath`,
`siteOrdinal`, `startChar`, `endChar`, and exact `callText`, then requires the
complete `0 .. invocations-1` ordinal set for every site. It does not use trace
filenames, list positions, line numbers, or generated `occurrence` values for
matching. Any missing, extra, duplicate, malformed, range/call mismatch, v1
record, or invocation mismatch rejects before render/splice/output, reports
`identity_failed`, and gives every expected site zero replay.

## Independent attacks and focused checks

- Synthetic fixtures passed for same-line calls, text-identical calls at
  distinct ranges, a Unicode prefix, shuffled records, altered occurrences,
  missing/extra records, malformed records, wrong ranges/call text, v1, and
  missing/duplicate/out-of-range invocation ordinals.
- The real `Mathlib/Logic/Function/Basic.lean` source counted 25 sites; a
  deliberately constructed 23-record set was rejected with exactly the two
  missing ordinals and `renderAttempted == false`.
- `python3 -B Experiment/pipeline/check_pipeline.py`: **PASS, 224 checks**.
  `py_compile` for all T4 Python modules and `git diff --check`: **PASS**.
- The simplified spec and implementation require no source/manifest/call
  hashes, nonces, or forgery machinery. Existing git commit hashes in the
  report are provenance only and are not identity validation inputs.

## Six-module gate

T1 was clean at `573e6d0`; `check_transcription.py` passed with 17/17, 1/1,
2/2, 8/8, 25/25, and 31/31 source/converted sites, and all manifests and
existing traces were v2. I ran the full six-module harness to
`/tmp/t4-review5-six.5bP5Mm`; it produced 17, 1, 2, 8, 25, and 31
`identity_failed` modules because `transcribe` ignored unchanged trace files as
stale after the compile (`ignored N trace file(s) left by an earlier compile`).
Thus no replay count is acceptance evidence and merge remains blocked until a
fresh complete v2 output run is consumable by the harness.
