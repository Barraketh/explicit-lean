# T1-trace-capture: RESULT (T9 producer identity)

## Delivered

- Added `test/SimpTrace/trace_identity.py`: attribute/comment-aware executable
  site scanning, exact original character ranges, source manifests, and
  fail-closed ordinary consistency validation. Top-level `--`/`/-` comments
  now terminate a call while delimiters inside strings, syntax data, or nested
  terms do not.
- Reworked `make_traced.py` to derive the manifest before rewriting and verify
  every replacement through a deterministic edit ledger; `FunctionBasicTraced`
  is 25/25, including both `@[simp]` declaration-line calls.
- Added `finalize_traces.py`, converting raw recorder files into self-contained
  `simp-trace-v2` envelopes with module/site identity, diagnostic occurrence,
  and complete invocation ordinals. Missing, extra, duplicate, range, call,
  and invocation mistakes reject before output is consumed. Its explicit
  `--traced-source --manifest --source --raw-dir --out-dir` interface never
  mutates raw inputs.
- Regenerated all six traced copies and manifests: 84 mapped sites and 106
  records. Added T9 regressions for attributes, same-line and identical calls,
  Unicode offsets, trailing comments (including nested/string data), and
  malformed invocation sets. Conversion checks use the edit ledger, so
  commented `=>trace` text cannot count.
- Parameterized the deterministic transform and verifier by an explicit trace
  output root. The five-path finalizer now binds that root to `--raw-dir` and
  checks each raw v1 call path against it; legacy module mode retains the
  committed relative root. The temp regression invokes the CLI, proves raw
  bytes are unchanged, and rejects a staged source rooted elsewhere.

## Checks (2026-09-17)

- `lake build ExplicitLean.SimpTrace`: PASS.
- `python3 -B test/SimpTrace/check_transcription.py`: PASS (84/84;
  Function.Basic 25/25).
- Six traced Lean runs: expected classified exits only; finalizer PASS (106
  v2 records, 84 sites).
- `python3 -B test/SimpTrace/test_trace_identity.py`: PASS, including malformed
  invocation and comment-boundary rejection; Function.Basic compile emitted
  and five-path finalization produced 30 v2 records without changing raw files.
- `python3 -B Experiment/check_simp_trace.py`: PASS (72 fixtures);
  `--report`: PASS (84 sites, 106 records, 592 steps).
- `git diff --check`: PASS.
- Explicit-path root-binding regression: PASS (separate v2 output, unchanged
  raw input, and mismatched-root rejection).

## Remaining blockers

- Consumer-side identity gate and replay integration remain T4 work.
- Existing classified replay families and named-zeta are intentionally out of
  scope for this producer batch.
