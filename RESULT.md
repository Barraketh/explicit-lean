# T29 principled simp-cache fork

## Result

Implemented the local provenance-bearing cache fork in
`ExplicitLean/SimpTrace/Traversal.lean` and routed the built-in conditional
simproc boundary in `ExplicitLean/SimpTrace/Recorder.lean`.  Each recorder
cache entry keeps the stock `Simp.Result` plus the ordered, root-relative
event slice produced for that expression.  Hits return the cached result and
replay/re-root the slice; no matcher reruns and no term/proof payload is
serialized.  Fresh and preserved cache scopes switch/restore both cache
layers.  `reduceIte`, `reduceDIte`, `dreduceIte`, and `dreduceDIte` are locally
routed only when the corresponding source simproc is enabled, with the stock
conditional entries erased from the invocation array to avoid duplicate
firings.

## Checks

* `lake build ExplicitLean.SimpTrace` — PASS.
* `lake env lean test/SimpTrace/CacheFork.lean` — PASS; 6 trace invocations,
  including repeated-expression re-rooting, `memoize := false`, contextual
  fresh-cache scope, recursive discharging, and `ite`/`dite`.
* `lake env lean test/SimpTrace/T20IteSimproc.lean` — PASS; applied and nested
  `ite`/`dite` plus conditional `dsimp` paths.
* `git diff --check` — PASS.
* `python3 -B Experiment/check_simp_family_lint.py` — PASS (46 tests, 2
  opt-in skips).
* `python3 -B Experiment/check_no_simp_family.py` — PASS (4 files scanned).

The focused six-invocation run measured about 4.25 s wall time and 1,284 MiB
maximum resident set size in this fork.  Three baseline runs from main ranged
from 3.95–4.61 s; one baseline memory sample was 1,283 MiB.  This is only a
focused measurement, not the seven-module capture.

The fresh seven-module 91/91 and 599-rewrite capture was not run here: this
isolated worktree has Mathlib source but no completed Mathlib `.olean` cache,
and a full Mathlib rebuild is outside this focused fork.  The remaining
opaque `simpHaveTelescope` path is intentionally unchanged; it is not a
reachable conditional simproc registration and should remain an explicit
integration boundary for the coordinator.
