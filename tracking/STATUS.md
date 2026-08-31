# Search-free Mathlib campaign

Updated 2026-08-31T16:15:56.785935+00:00

- Indexed: 83,425 calls in 8,264 modules.
- Accepted per-module verification: 234 translated calls in 26 modules.
- Provisional cache awaiting current semantic checks: 0 calls in 0 modules.
- Unresolved source classifications: 5.
- Missing cached report files: 0.

Frozen per-module results against stock imports; not full translated-tree closure. Accepted counts require campaign report schema 10 (implemented producer: 10), including replay-error checks, declaration comparison and boundary state guards. Earlier cached results are provisional until revalidated. Report existence is checked here; full evidence integrity is checked by acceptance tooling.

Queue: failed=20, queued=590, running=2, succeeded=26, unplanned=7626

## Active modules

- `Mathlib/Algebra/Algebra/NonUnitalSubalgebra.lean` (schema10-full)
- `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean` (schema10-expansion)

## Failures and partial results

- `Mathlib/Algebra/AffineMonoid/Irreducible.lean`: materializer exit 1
- `Mathlib/Algebra/Algebra/Bilinear.lean`: materializer exit 1
- `Mathlib/Algebra/CubicDiscriminant.lean`: materializer exit 1
- `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean`: materializer exit 1
- `Mathlib/Analysis/Real/Pi/Bounds.lean`: materializer exit 1
- `Mathlib/Control/Basic.lean`: materializer exit 1
- `Mathlib/Control/Functor.lean`: materializer exit 1
- `Mathlib/Data/Fin/Basic.lean`: materializer exit 1
- `Mathlib/Data/List/ModifyLast.lean`: materializer exit 1
- `Mathlib/Data/List/TFAE.lean`: materializer exit 1
- `Mathlib/Data/Nat/BinaryRec.lean`: materializer exit 1
- `Mathlib/Data/Nat/Init.lean`: materializer exit 1
- `Mathlib/Data/String/Lemmas.lean`: materializer exit 1
- `Mathlib/Logic/ExistsUnique.lean`: materializer exit 1
- `Mathlib/Order/Defs/LinearOrder.lean`: materializer exit 1
- `Mathlib/RingTheory/OreLocalization/Basic.lean`: materializer exit 1
- `Mathlib/RingTheory/WittVector/Basic.lean`: materializer exit 1
- `Mathlib/Tactic/Group.lean`: materializer exit 1
- `Mathlib/Tactic/SimpRw.lean`: materializer exit 1

Regenerate with `python3 Experiment/campaign_status.py --markdown`.
