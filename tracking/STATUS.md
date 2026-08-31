# Search-free Mathlib campaign

Updated 2026-08-31T18:33:02.055161+00:00

- Indexed: 83,425 calls in 8,264 modules.
- Accepted per-module verification: 0 translated calls in 0 modules.
- Provisional cache awaiting current semantic checks: 1,323 calls in 137 modules.
- Unresolved source classifications: 5.
- Missing cached report files: 0.

Acceptance on hold: The cold serialized comparator, independent compilation consumer, and unconditional pending-synthesis barrier are integrated and bounded schema11 controls passed. Complete translated dependency-tree certification remains pending; previous candidates and proof checks stay provisional. Frozen per-module results against stock imports; not full translated-tree closure. Accepted counts require campaign report schema 11 (implemented producer: 11), including replay-error checks, declaration comparison and boundary state guards. Earlier cached results are provisional until revalidated. Report existence is checked here; full evidence integrity is checked by acceptance tooling.

Queue: failed=74, queued=426, running=1, succeeded=137, unplanned=7626

## Active modules

- `Mathlib/Algebra/Category/ModuleCat/FilteredColimits.lean` (schema10-full)

## Failures and partial results

- `Mathlib/Algebra/AffineMonoid/Irreducible.lean`: materializer exit 1
- `Mathlib/Algebra/Algebra/Bilinear.lean`: materializer exit 1
- `Mathlib/Algebra/Algebra/NonUnitalSubalgebra.lean`: materializer exit 1
- `Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean`: materializer exit 1
- `Mathlib/Algebra/Algebra/Subalgebra/Centralizer.lean`: materializer exit 1
- `Mathlib/Algebra/Algebra/Subalgebra/Tower.lean`: materializer exit 1
- `Mathlib/Algebra/Algebra/Subalgebra/Unitization.lean`: materializer exit 1
- `Mathlib/Algebra/Algebra/Tower.lean`: materializer exit 1
- `Mathlib/Algebra/Algebra/Unitization.lean`: materializer exit 1
- `Mathlib/Algebra/Azumaya/Matrix.lean`: materializer exit 1
- `Mathlib/Algebra/BigOperators/Balance.lean`: materializer exit 1
- `Mathlib/Algebra/BigOperators/Expect.lean`: materializer exit 1
- `Mathlib/Algebra/BigOperators/Finprod.lean`: materializer exit 1
- `Mathlib/Algebra/BigOperators/Finsupp/Basic.lean`: materializer exit 1
- `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`: materializer exit 1
- `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`: materializer exit 1
- `Mathlib/Algebra/BigOperators/Group/List/Basic.lean`: materializer exit 1
- `Mathlib/Algebra/BigOperators/Group/List/Lemmas.lean`: materializer exit 1
- `Mathlib/Algebra/BigOperators/Intervals.lean`: materializer exit 1
- `Mathlib/Algebra/Category/Grp/EpiMono.lean`: materializer exit 1
- `Mathlib/Algebra/Category/ModuleCat/Differentials/Basic.lean`: materializer exit 1
- `Mathlib/Algebra/CubicDiscriminant.lean`: materializer exit 1
- `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean`: materializer exit 1
- `Mathlib/AlgebraicGeometry/Cover/Open.lean`: materializer exit 1
- `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`: materializer exit 1
- `Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/DoldKan/Faces.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/ModelCategory/BifibrantObjectHomotopy.lean`: materializer exit 1

Regenerate with `python3 Experiment/campaign_status.py --markdown`.
