# T4-pipeline incremental review, round 3

Reviewed at `646e6bf`. Verdict: **NO DEFECTS** in the REVIEW-2 marker-fix
scope; no critical or major defects found. The scope is merge-eligible,
subject to the normal final full merge-gate review. Marker edits are planned
from immutable original-source coordinates, aggregated per source line, and
ordered by site index before right-to-left application.

## Checks

- `python3 -B Experiment/pipeline/check_pipeline.py`: **PASS, 194 checks**;
  end-to-end `Nontrivial/Defs` check passed.
- Focused adversarial Python repros: **PASS** for deterministic mapping-order
  and marker-order aggregation; 2 and 3 retained sites on one line; mixed
  retained/replayed sites; Unicode prefixes; multiple source lines; original
  source preservation; and replacement lint visibility.
- `git diff --check` and `git show --check HEAD`: **PASS**.
- Six-module harness: **not run**. T1 remains an external dirty/unstable
  precondition at `db97d8f` (`Tactic.lean` modified, `check_simp_trace.py`
  modified, and untracked `test/SimpTrace/linkescape`); T2 is clean at
  `8b57c4a`. This is not penalized against T4.

