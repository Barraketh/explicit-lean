# Search-free Mathlib campaign

Updated 2026-08-31T12:40:41.591720+00:00

- Indexed: 83,425 calls in 8,264 modules.
- Accepted per-module verification: 7 translated calls in 2 modules.
- Provisional cache awaiting current semantic checks: 254 calls in 22 modules.
- Unresolved source classifications: 5.
- Missing cached report files: 0.

Frozen per-module results against stock imports; not full translated-tree closure. Accepted counts require replay-error checks in both compilation and the declaration oracle, plus local matcher and auxiliary-cache state comparison (report schema 8). Earlier cached results are provisional until revalidated. Report existence is checked here; full evidence integrity is checked by acceptance tooling.

Queue: failed=23, queued=89, running=2, succeeded=24, unplanned=8126

## Active modules

- `Mathlib/Data/Int/DivMod.lean` (schema8-frontier)
- `Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean` (schema7-diverse)

## Failures and partial results

- `Mathlib/Algebra/Homology/CochainComplexOpposite.lean`: materializer exit 1
- `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean`: materializer exit 1
- `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplexOne.lean`: materializer exit 1
- `Mathlib/Analysis/Complex/CanonicalDecomposition.lean`: materializer exit 1
- `Mathlib/Analysis/Real/Pi/Bounds.lean`: materializer exit 1
- `Mathlib/CategoryTheory/Sites/Subcanonical.lean`: materializer exit 1
- `Mathlib/CategoryTheory/SmallObject/Construction.lean`: materializer exit 1
- `Mathlib/Combinatorics/SimpleGraph/Basic.lean`: materializer exit 1
- `Mathlib/Combinatorics/SimpleGraph/Tutte.lean`: materializer exit 1
- `Mathlib/Data/Fin/Basic.lean`: materializer exit 1
- `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`: materializer exit 1
- `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean`: materializer exit 1
- `Mathlib/Order/Defs/LinearOrder.lean`: materializer exit 1
- `Mathlib/RingTheory/HopfAlgebra/Convolution.lean`: materializer exit 1
- `Mathlib/RingTheory/MvPolynomial/Basic.lean`: materializer exit 1
- `Mathlib/RingTheory/OrderOfVanishing/Basic.lean`: materializer exit 1
- `Mathlib/RingTheory/OreLocalization/Basic.lean`: materializer exit 1
- `Mathlib/RingTheory/WittVector/Basic.lean`: materializer exit 1
- `Mathlib/Tactic/Group.lean`: materializer exit 1
- `Mathlib/Tactic/SimpRw.lean`: materializer exit 1
- `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`: materializer exit 1

Regenerate with `python3 Experiment/campaign_status.py --markdown`.
