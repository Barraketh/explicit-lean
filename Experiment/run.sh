#!/bin/sh
set -eu

lake build ExplicitLean.SimpExplicit
lake env lean Experiment/SimpExplicitProbe.lean
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
