# T47 strict translated cone acceptance

## Result

Fresh worktree `/private/tmp/explicit-lean-accept-t47-full-cone` was created at
`86f90d1ca6aef852253135a52ad4cb862713efc2`.

The fresh seed replay used the current T1/T2 pipeline and automatic manual
overlays.  It accepted all seven modules and all 91/91 source-site identities;
all 91 sites replayed, with zero unresolved, render failures, structural
refusals, compile failures, probe-inconclusive results, or identity failures.
The six overlay records used were `8e17e105590e562a`, `c28dd19f3d6d3d67`,
`42f1163b9fd99b7b`, `a30cdf5ef0f79ad7`, `bcd40e80cbe2ffe1`, and
`acca7bbba4fc669d`.

T13 then materialized the exact reviewed closure (69 modules, 134 edges) into
a fresh translated root and compiled this order:

1. `Mathlib.Logic.Basic`
2. `Mathlib.Logic.ExistsUnique`
3. `Mathlib.Logic.Function.Defs`
4. `Mathlib.Logic.Nontrivial.Defs`
5. `Mathlib.Logic.Relator` (bridge)
6. `Mathlib.Logic.Function.Basic`
7. `Mathlib.Logic.IsEmpty.Basic`
8. `Mathlib.Data.Option.Basic`

All eight builds returned 0, emitted fresh `.olean` families, and resolved
from the private translated root.  No stale artifact was reused.  The strict
lint recorded 101 unchanged baseline simp-family findings in pinned Mathlib,
introduced 0 new findings, and passed.  The baseline-aware distinction is
needed because this milestone replaces the 91 executable `simp`/`simp only`
seed sites; untouched `simpa`/simproc calls are outside that seed target.

## Evidence and measurements

- Seed report: `/tmp/t47-seed-20260917T2011Z/report.json`
- Seed summary: `/tmp/t47-seed-20260917T2011Z/summary.md`
- Cone manifest: `/tmp/t47-cone-run-20260917T2030Z/manifest.json`
- Cone logs: `/tmp/t47-cone-run-20260917T2030Z/logs/`
- Fresh source closure: `/private/tmp/explicit-lean-accept-t47-full-cone/.lake/t47-source-20260917T2011Z/`
- Seed runtime/RSS: 38.06 s, 762,691,584 bytes maximum RSS
- T13 runtime/RSS: 11.99 s, 668,991,488 bytes maximum RSS
- Lean: 4.32.2 (`f3b06c705e6c85f5314019d5d3baab0fec5b580c`)

## Checks

```text
python3 -B Experiment/check_readable_cone.py        PASS (5 tests)
python3 -m py_compile Experiment/run_readable_cone.py Experiment/check_readable_cone.py  PASS
git diff --check                                    PASS
```

The authoritative T13 manifest reports `status: "passed"`.  This is cone
acceptance only; whole-Mathlib acceptance remains unclaimed.
