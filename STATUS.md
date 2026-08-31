# Search-free Mathlib campaign

Updated 2026-08-31T12:25:38.387792+00:00

- Indexed: 83,425 calls in 8,264 modules.
- Accepted per-module verification: 0 translated calls in 0 modules.
- Provisional cache awaiting current semantic checks: 180 calls in 20 modules.
- Unresolved source classifications: 5.
- Missing cached report files: 0.

Frozen per-module results against stock imports; not full translated-tree closure. Accepted counts require replay-error checks in both compilation and the declaration oracle, plus local matcher and auxiliary-cache state comparison (report schema 8). Earlier cached results are provisional until revalidated. Report existence is checked here; full evidence integrity is checked by acceptance tooling.

Queue: failed=15, queued=84, running=1, succeeded=20, unplanned=8144

## Active modules

- `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean` (schema7-diverse)

## Failures and partial results

- `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean`: materializer exit 1
- `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplexOne.lean`: materializer exit 1
- `Mathlib/Analysis/Real/Pi/Bounds.lean`: materializer exit 1
- `Mathlib/CategoryTheory/Sites/Subcanonical.lean`: materializer exit 1
- `Mathlib/Combinatorics/SimpleGraph/Basic.lean`: materializer exit 1
- `Mathlib/Data/Fin/Basic.lean`: materializer exit 1
- `Mathlib/Data/Nat/Init.lean`: materializer exit 1
- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`: materializer exit 1
- `Mathlib/Order/Defs/LinearOrder.lean`: materializer exit 1
- `Mathlib/RingTheory/MvPolynomial/Basic.lean`: materializer exit 1
- `Mathlib/RingTheory/WittVector/Basic.lean`: materializer exit 1
- `Mathlib/Tactic/Group.lean`: materializer exit 1
- `Mathlib/Tactic/SimpRw.lean`: materializer exit 1
- `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`: materializer exit 1

Regenerate with `python3 Experiment/campaign_status.py --markdown`.
