# T27 T20 site-17 regression fix

Status: implemented on a fresh worktree from `97800b0b2a197bd922377892e16e69772638e97a`.

The recorder now takes the bounded `reduceIte`/`reduceDIte` path only when the
simproc frame's observed condition is exactly the conditional redex's
condition.  A later invocation after forked traversal has emitted
`ite_congr` therefore falls through to the ordinary proof-backed event path;
the actual congruence and conditional transitions are both retained.  The
auto-congruence event also uses the trimmed application redex position, keeping
applied conditionals positional.

Changed files:

* `ExplicitLean/SimpTrace/Recorder.lean`
* `ExplicitLean/SimpTrace/Traversal.lean`
* `test/SimpTrace/T20IteSimproc.lean`

Focused checks:

* `lake build ExplicitLean.SimpTrace` — PASS.
* `lake env lean test/SimpTrace/T20IteSimproc.lean` — PASS; the diagnosis
  trace has 4 `rw` events (3 derivations), including `ite_congr`, `eq_self`,
  and `ite_cond_eq_true`; applied/nested ite/dite fixtures pass.
* `lake env lean test/SimpTrace/Fixtures.lean` — PASS.
* `lake env lean test/SimpTrace/T21MissingRulePaths.lean` — PASS.
* `lake env lean test/SimpTrace/T22SourceArgIdentity.lean` — PASS.
* `python3 -B test/SimpTrace/check_t22_source_args.py` — PASS.
* `python3 -B test/SimpTrace/test_trace_identity.py` — PASS (22 tests).
* `python3 -B test/SimpTrace/check_transcription.py` — PASS (91/91 identity).
* `python3 -B Experiment/check_simp_engine_ite.py` and `..._dite.py` — PASS.
* `python3 -B Experiment/check_simp_engine_recording.py` — PASS (42 branches).
* `python3 -B Experiment/check_simp_engine_simproc.py` — PASS.
* campaign supervisor/worker/translation-index checks — PASS.
* `python3 -B Experiment/check_no_simp_family.py` — PASS; pipeline checker —
  PASS (265 checks); `git diff --check` — PASS.

The fresh seven-module capture/replay gate was not run in this isolated T20
worktree; no corpus replay credit is claimed.  The known 18 cache-provenance
gap remains T26-owned.
