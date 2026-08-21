#!/bin/sh
set -eu

lake build ExplicitLean.SimpExplicit
lake env lean Experiment/PassiveSimpProbe.lean
lake env lean Experiment/ProofExportProbe.lean
lake env lean Experiment/PremiseReplayProbe.lean
lake env lean Experiment/GuardedPremiseProbe.lean
lake env lean Experiment/TermPremiseProbe.lean
lake env lean Experiment/SelectorProbe.lean
lake env lean Experiment/ReductionProbe.lean
lake env lean Experiment/LocalRenameProbe.lean
lake env lean Experiment/ContextReplayProbe.lean
lake env lean Experiment/ContextRecordProbe.lean
lake env lean Experiment/ContextPassiveProbe.lean
lake env lean Experiment/ContextLocationProbe.lean
lake env lean Experiment/BodyScopeProbe.lean
lake env lean Experiment/BodyMaterializationProbe.lean
lake env lean Experiment/FirstOwnerProbe.lean
lake env lean Experiment/ClosureProbe.lean
lake env lean Experiment/SpecialFallbackProbe.lean
python3 Experiment/check_premise_replay.py
python3 Experiment/check_selectors.py
python3 Experiment/check_reductions.py
python3 Experiment/check_local_renames.py
python3 Experiment/check_context_replay.py
python3 Experiment/check_context_record.py
python3 Experiment/check_context_passive.py
python3 Experiment/check_context_locations.py
python3 Experiment/check_body_scopes.py
python3 Experiment/check_simp_final_state.py
python3 Experiment/check_body_materialization.py
python3 Experiment/check_first_owner.py
python3 Experiment/check_closure.py
python3 Experiment/check_body_scope_proof.py
python3 Experiment/check_nondefault_config.py
python3 Experiment/check_proof_export_scaling.py
python3 Experiment/check_simp_fixtures.py
python3 Experiment/check_mixed_certificates.py
python3 Experiment/check_simp_coverage.py
python3 Experiment/mixed_certificate_rewrites.py
for module in \
  Mathlib/CategoryTheory/PathCategory/Basic.lean \
  Mathlib/CategoryTheory/Yoneda.lean \
  Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean \
  Mathlib/CategoryTheory/Triangulated/Subcategory.lean \
  Mathlib/CategoryTheory/EqToHom.lean
do
  lake env lean \
    -Dlinter.unusedVariables=false \
    -DmaxHeartbeats=0 \
    ".lake/mixed-certificate-rewritten/$module"
done

lake build ExplicitLean.Normalize
lake env lean Experiment/NormalizationProbe.lean
python3 Experiment/normalization_modules.py

for module in \
  Mathlib/Data/List/DropRight.lean \
  Mathlib/Analysis/RCLike/Sqrt.lean \
  Mathlib/CategoryTheory/Localization/SmallHom.lean \
  Mathlib/LinearAlgebra/Vandermonde.lean \
  Mathlib/AlgebraicGeometry/Normalization.lean \
  Mathlib/NumberTheory/ModularForms/Derivative.lean
do
  lake env lean \
    -Dlinter.unusedVariables=false \
    -DmaxHeartbeats=0 \
    ".lake/normalization-probe/rewritten/$module"
done

python3 Experiment/normalization_analysis.py

python3 Experiment/simp_heavy_modules.py rewritten

for module in \
  Mathlib/Data/List/DropRight.lean \
  Mathlib/Analysis/RCLike/Sqrt.lean
do
  lake env lean \
    -Dlinter.unusedVariables=false \
    -DmaxHeartbeats=0 \
    ".lake/simp-explicit-probe/rewritten/$module"
done

lake env lean Experiment/Main.lean
lake env lean Experiment/StatementCheck.lean
python3 Experiment/rewrite.py

for module in \
  Mathlib/SetTheory/Cardinal/NatCount.lean \
  Mathlib/Algebra/ContinuedFractions/Translations.lean \
  Mathlib/Algebra/DualNumber.lean \
  Mathlib/Data/List/Range.lean \
  Mathlib/Topology/Basic.lean \
  Mathlib/NumberTheory/Divisors.lean
do
  lake env lean \
    -Dlinter.unusedVariables=false \
    -Dlinter.auxLemma=false \
    -DmaxHeartbeats=0 \
    -DmaxRecDepth=100000 \
    ".lake/proof-term-probe/rewritten/$module"
done
