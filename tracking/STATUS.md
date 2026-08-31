# Search-free Mathlib campaign

Updated 2026-08-31T16:54:25.405402+00:00

- Indexed: 83,425 calls in 8,264 modules.
- Accepted per-module verification: 0 translated calls in 0 modules.
- Provisional cache awaiting current semantic checks: 513 calls in 55 modules.
- Unresolved source classifications: 5.
- Missing cached report files: 0.

Acceptance on hold: Metadata export hooks mutate a process-global symbol-frequency cache. Observational boundary/audit reads and equivalence to separate fresh compilations must be repaired and revalidated; existing generated candidates and proof checks are preserved. Frozen per-module results against stock imports; not full translated-tree closure. Accepted counts require campaign report schema 10 (implemented producer: 10), including replay-error checks, declaration comparison and boundary state guards. Earlier cached results are provisional until revalidated. Report existence is checked here; full evidence integrity is checked by acceptance tooling.

Queue: failed=44, queued=537, running=2, succeeded=55, unplanned=7626

## Active modules

- `Mathlib/Algebra/Azumaya/Defs.lean` (schema10-full)
- `Mathlib/Computability/Ackermann.lean` (schema10-expansion)

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
- `Mathlib/Algebra/CubicDiscriminant.lean`: materializer exit 1
- `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean`: materializer exit 1
- `Mathlib/AlgebraicGeometry/Cover/Open.lean`: materializer exit 1
- `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`: materializer exit 1
- `Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/DoldKan/Faces.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean`: materializer exit 1
- `Mathlib/AlgebraicTopology/ModelCategory/BifibrantObjectHomotopy.lean`: materializer exit 1
- `Mathlib/Analysis/AperiodicOrder/Delone/Basic.lean`: materializer exit 1
- `Mathlib/Analysis/BoxIntegral/Box/SubboxInduction.lean`: materializer exit 1
- `Mathlib/Analysis/MellinInversion.lean`: materializer exit 1
- `Mathlib/Analysis/Real/Pi/Bounds.lean`: materializer exit 1
- `Mathlib/CategoryTheory/Abelian/DiagramLemmas/KernelCokernelComp.lean`: materializer exit 1
- `Mathlib/CategoryTheory/Sites/Subcanonical.lean`: materializer exit 1
- `Mathlib/CategoryTheory/SmallObject/Construction.lean`: materializer exit 1
- `Mathlib/Combinatorics/Additive/Corner/Roth.lean`: materializer exit 1
- `Mathlib/Combinatorics/Matroid/Basic.lean`: materializer exit 1
- `Mathlib/Combinatorics/Matroid/IndepAxioms.lean`: materializer exit 1
- `Mathlib/Combinatorics/SimpleGraph/Basic.lean`: materializer exit 1
- `Mathlib/Combinatorics/SimpleGraph/Tutte.lean`: materializer exit 1

Regenerate with `python3 Experiment/campaign_status.py --markdown`.
