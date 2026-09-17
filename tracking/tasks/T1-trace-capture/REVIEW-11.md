# T1-trace-capture: merge-gate review, round 11

Reviewed commit `369fb3fe27040482d05ce3caef35babf4ac782d9` in a clean
worktree. Verdict: **NO DEFECTS OBSERVED; T1 merge-eligible**.

## Checks

- `lake build ExplicitLean.SimpTrace`: PASS, exit 0, 1.11 s.
- `python3 -B test/SimpTrace/check_transcription.py`: PASS, all 6 traced
  modules, 82/82 source sites converted.
- `lake env lean test/SimpTrace/Fixtures.lean`: PASS, exit 0.
- `python3 -B Experiment/check_simp_trace.py`: PASS, 72 fixtures and path
  containment checks.
- `python3 -B Experiment/check_simp_trace.py --report`: PASS; 84 sites, 110
  traces, 633 steps. The report contains the required nested regression line.
- Adversarial JSON checks: a temporary copy with the nested
  `exists_apply_eq_apply` verdict omitted exits 1; likewise omission of all
  nested `ne_eq` verdicts exits 1; removing all `source: congr` side arrays
  exits 1. Original evidence was not modified.
- Nested shape attack: `FunctionBasicTraced_11.1.json` has a three-sibling
  `dite_congr` side tree; side 0 step 0 is exactly marked
  `unapplied_quantified_prop:exists_apply_eq_apply`, while sibling sides remain
  clean. Four nested `ne_eq` steps are each marked at their own paths.
- Current T4 end-to-end command completed in 155.11 s: 44/84 replayed, 1
  unresolved, 19 render failures, 18 compile failures, 2 probe inconclusive.
  The remaining renderer non-consumption of step-level `unresolved` is a
  separate T4 defect, not a T1 verdict-association defect.

The structured verdict recursion is exact for top-level, side, dependent-
congruence, and recursively nested events; fixture skeletons confirm existing
top-level behavior. Known T1 cases are serialized and therefore fail-closed at
the trace boundary. No critical or major T1 finding remains.
