#!/bin/sh
set -eu

lake build \
  ExplicitLean \
  ExplicitLean.SimpEngine.Inventory \
  ExplicitLean.SimpEngine.Reference
python3 Experiment/check_simp_engine_pin.py
python3 Experiment/check_simp_engine_reference.py
python3 Experiment/check_simp_engine_observers.py
python3 Experiment/check_simp_engine_review.py
python3 Experiment/check_simp_engine_recording.py
python3 Experiment/check_simp_engine_replay.py
python3 Experiment/check_simp_engine_mutations.py
python3 Experiment/check_simp_engine_source.py
python3 Experiment/check_simp_engine_cloud.py
