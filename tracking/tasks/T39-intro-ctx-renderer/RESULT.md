# T39 — wire stable `intro_ctx` metadata to the renderer

Implemented the renderer path for T34's nested `intro` metadata using the T33
`explicit_rw` scoped form. The renderer copies and validates the stable handle,
domain position, dependency indices, scope id, and exact enter/exit positions;
it never reads or emits a display name and refuses structural steps that T33's
inner grammar does not admit.

Files changed:

- `Experiment/pipeline/render.py`
- `Experiment/pipeline/check_pipeline.py`
- `test/Pipeline/renderer_cases.json`

Checks:

- `python3 -B Experiment/pipeline/check_pipeline.py` — PASS (307 checks; one
  existing Nontrivial.Defs render-failed measurement is reported by the harness).
- `lake build ExplicitLean.ExplicitRw` — PASS.
- `lake env lean test/ExplicitRw/IntroCtx.lean` — PASS (focused
  Function.Basic site-7-shaped scoped replay).
- `lake env lean test/ExplicitRw/Negative.lean` — PASS.
- Renderer output compared against the focused site-7 fixture after whitespace
  normalization — PASS.
- `python3 -m py_compile Experiment/pipeline/render.py Experiment/pipeline/check_pipeline.py` — PASS.
- `python3 -B Experiment/check_no_simp_family.py` — PASS.
- `git diff --check` — PASS.

The focused renderer suite now reports a positive stable `intro_ctx` case and
explicit refusals for missing/display-name metadata and forbidden nested
structural steps.
