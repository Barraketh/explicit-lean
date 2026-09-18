# T37 — renderer wiring for dependent-forall transport

## Result

Added renderer support for T35 `kind: "transport"` records. The renderer
mechanically validates the stable non-negative handle and exact `domain`/`body`
step arrays, recursively renders their child-rooted positions, and emits T32's
`transport forall <handle> [...] body [...] at [...]` syntax. Nested transport
is refused because T32's inner-step grammar does not admit it. No binder-name
recovery, term payload, inference, or search was added.

Changed:

- `Experiment/pipeline/render.py`
- `test/Pipeline/renderer_cases.json`

## Checks

- `lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw` — PASS.
- `python3 -B Experiment/pipeline/check_pipeline.py` — PASS, 301 checks
  (includes T36 universe-annotation and T37 transport fixtures).
- `python3 -B Experiment/check_no_simp_family.py` — PASS.
- T35 fixture rendered with exact handles/positions and body/domain separation — PASS.
- Fresh/current replay:
  `python3 -B Experiment/pipeline/replay_module.py --module Mathlib/Logic/Basic.lean --t1 <T37-integration> --t2 <T37-integration> ...`
  — Logic.Basic 28/31 replayed; target ordinals 7, 26, 27, 28 all replayed.
  Full report: `/tmp/t37-integration-ejxiZB/report.json`.
- T36 focused manual overlays for `Mathlib/Logic/Basic.lean` and
  `Mathlib/Logic/Function/Basic.lean` — both `lake env lean` compiles PASS.
  (Generated focused sources: `/tmp/t36-focused-ZAgQb4/`.)

This integration was rebased from main `b5c601f`; T36's pp.all fixes and
manual-override entries are preserved.
