#!/bin/sh
set -eu

lake env lean Experiment/Main.lean
lake env lean Experiment/StatementCheck.lean
python3 Experiment/rewrite.py

lake env lean \
  -Dlinter.unusedVariables=false \
  -DmaxHeartbeats=0 \
  -DmaxRecDepth=100000 \
  .lake/proof-term-probe/rewritten/Mathlib/SetTheory/Cardinal/NatCount.lean

lake env lean \
  -Dlinter.unusedVariables=false \
  -DmaxHeartbeats=0 \
  -DmaxRecDepth=100000 \
  .lake/proof-term-probe/rewritten/Mathlib/Algebra/ContinuedFractions/Translations.lean

lake env lean \
  -Dlinter.unusedVariables=false \
  -DmaxHeartbeats=0 \
  -DmaxRecDepth=100000 \
  .lake/proof-term-probe/rewritten/Mathlib/Algebra/DualNumber.lean
