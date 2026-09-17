# T4 trace lifecycle diagnosis (2026-09-17)

## Finding

The REVIEW-5 failure is a producer/consumer directory-lifecycle bug, not a
Lean correctness failure. At T1 `573e6d0`, `make_traced.py` writes a traced
copy and manifest under `test/SimpTrace/`; generated clauses hard-code
`test/SimpTrace/meas_out/<name>_NN.json`. T4 `transcribe` runs that copy in the
T1 working directory. The recorder resolves those relative paths under the
package root and writes raw `simp-trace-v1` JSON. On an existing path it
overwrites only byte-identical output; otherwise it allocates `.<run>.json`
(for example `_01.1.json`).

T1's `finalize_traces.py` is not called by T4. It enumerates every matching
file in `meas_out` and mutates each raw file in place into a `simp-trace-v2`
envelope, using the traced copy's manifest and pinned source
(`finalize_traces.py:19-70`). Consequently, after one successful finalization
the base `_NN.json` is v2. A later T4 compile emits fresh v1 files as
`_NN.1.json`; T4's mtime filter (`replay_module.py:333-358`) ignores the old v2
base files and admits only the fresh v1 suffixes. Identity validation then
rejects every admitted record as an invalid schema. If the compile emits no
file, the same filter rejects all old v2 records as stale. Thus a clean Lean
compile can leave zero consumable v2 records.

The saved REVIEW-5 report is an exact reproduction: each module logs
`ignored N trace file(s) left by an earlier compile`; it observes 17, 1, 3, 8,
30, and 47 fresh records respectively, all invalid v1 records, while the
corresponding old v2 records are classified stale. This explains the six
`identity_failed` results even though the trace compiler reached its expected
classified exits.

## Minimal reproduction

Run in a fresh T1 snapshot at `573e6d0` whose `test/SimpTrace/meas_out/` is
empty (do not delete the shared T1 directory):

```sh
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean test/SimpTrace/IsEmptyBasicTraced.lean       # raw v1 _01.json
python3 -B test/SimpTrace/finalize_traces.py IsEmptyBasicTraced  # _01.json -> v2
lake env lean test/SimpTrace/IsEmptyBasicTraced.lean       # fresh raw v1 _01.1.json
python3 - <<'PY'
from pathlib import Path
import json
p = Path("test/SimpTrace/meas_out")
for x in sorted(p.glob("IsEmptyBasicTraced_*.json")):
    print(x.name, json.loads(x.read_text())["schema"])
PY
```

The listing contains both `_01.json simp-trace-v2` and `_01.1.json
simp-trace-v1` (and similarly for each site). T4's corresponding consumer run
is:

```sh
cd /Users/ptsier/projects/explicit-lean-worktrees/T4-pipeline
python3 -B Experiment/pipeline/replay_module.py \
  --module Mathlib/Logic/IsEmpty/Basic.lean \
  --t1 /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture \
  --t2 /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw \
  --out /tmp/t4-trace-lifecycle
```

Its log reports ignored old files and identity rejection of admitted v1
suffixes. Running against the six modules gives the REVIEW-5 pattern.

## Smallest fix and ownership

T4 should own the consumer-side fix in `Experiment/pipeline/replay_module.py`:
for each module, copy the committed traced source and manifest into a fresh
run-owned staging directory, rewrite each `=>trace` path deterministically to
that run's raw directory, set `SIMP_TRACE_OUT_ROOT` to permit that directory,
compile the staged source with T1 as the Lean working directory, and consume
only files from that run. This removes the mtime heuristic and needs no hashes,
nonces, or adversarial-forgery machinery.

Finalization must also happen in the run-owned tree. The smallest T4-only
adapter is to stage T1's `finalize_traces.py` and `trace_identity.py` beside the
staged traced copy (with a read-only `.lake` link to T1's pinned dependencies),
then invoke the staged finalizer and consume only its v2 outputs. If an API
change is preferred, T1 owns adding an explicit `--root/--out-dir` to the
finalizer; T4 still invokes it on run-owned paths and never writes T1/T2.

It is safe to remove only T4's run-owned staging/raw/final directories after
the report. Do not clean or rerun the finalizer over T1's mixed `meas_out`:
that directory is shared evidence, and mixed v1/v2 inputs correctly trigger
the finalizer's duplicate/already-finalized guard.
