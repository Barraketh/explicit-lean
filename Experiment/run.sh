#!/bin/sh
set -eu

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
