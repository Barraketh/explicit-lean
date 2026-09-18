# T35 — recorder-side dependent-forall transport

Implemented recorder/traversal metadata for T32's transport contract.

Changed:

- `ExplicitLean/SimpTrace/Traversal.lean`: records a `transport` event at the
  `forall_prop_domain_congr` construction point; captures exact root-relative
  domain/body event positions and stable per-call introduced handles.
- `ExplicitLean/SimpTrace/Types.lean`: exports `kind: "transport"`, `handle`,
  `domain`, and `body` metadata fields; no proof/Expr objects cross JSON.
- `ExplicitLean/SimpTrace/Tactic.lean`: serializes transport events and maps
  body fvar arguments to `introduced_ref N`; validates nested domain/body runs.
- `ExplicitLean/SimpTrace/Recorder.lean`: includes transport in event plumbing.
- `test/SimpTrace/T35DependentTransport.lean` and
  `check_t35_transport.py`: focused body/domain fixture and payload checks.

Checks:

- `lake build ExplicitLean.SimpTrace` — PASS.
- `lake env lean test/SimpTrace/T35DependentTransport.lean` — PASS.
- `lake env lean test/SimpTrace/FunctionBasicTraced.lean` — expected existing
  unresolved/replay diagnostics; no transport validation/panic diagnostics.
- `lake env lean test/SimpTrace/LogicBasicTraced.lean` — expected existing
  unresolved/replay diagnostics; no transport validation/panic diagnostics.
- `python3 -B test/SimpTrace/check_t35_transport.py test/SimpTrace/meas_out` —
  PASS (focused fixture plus 8 branch transport records).
- `python3 -B test/SimpTrace/test_trace_identity.py` — PASS.
- `python3 -B test/SimpTrace/check_transcription.py` — PASS.
- `python3 -B Experiment/check_no_simp_family.py` and `git diff --check` — PASS.

Schema note: transport uses the existing T32 syntax contract; the minimal JSON
addition is `handle` plus root-relative `domain`/`body` step arrays on a
`kind: "transport"` step. T32 renderer integration remains coordinator-owned.
