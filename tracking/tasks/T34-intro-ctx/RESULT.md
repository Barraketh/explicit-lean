# T34 — stable `intro_ctx` recorder metadata

Implemented stable contextual-binder recorder metadata from the exact
`simpArrowT` introduction point.

Files changed:

- `ExplicitLean/SimpTrace/Types.lean`: term-free domain/dependency, scope, and
  introduced-handle records; optional `intro` payload on trace steps.
- `ExplicitLean/SimpTrace/Traversal.lean`: per-call handle/scope allocation,
  operational local-declaration dependencies, explicit enter/exit events, and
  fresh handle remapping for cached event replays.
- `ExplicitLean/SimpTrace/Recorder.lean`: recognizes scope-exit metadata while
  placing nested events.
- `ExplicitLean/SimpTrace/Tactic.lean`: emits `intro_ctx` metadata without the
  unstable inaccessible display name; scope exits remain recorder-internal.
- `test/SimpTrace/IntroCtxStable.lean` and
  `test/SimpTrace/check_intro_ctx_metadata.py`: alpha-renamed Function.Basic
  site-7-shaped capture and stable-handle/payload assertions.

Checks:

- `lake build ExplicitLean.SimpTrace` — pass.
- `lake env lean test/SimpTrace/IntroCtxStable.lean` — pass (only the existing
  unused-tactic warnings for the no-op focused capture).
- `python3 test/SimpTrace/check_intro_ctx_metadata.py` — pass; both renamed
  captures have handles `[0, 1]`, operational domain dependencies, and no
  `name` field.
- `python3 Experiment/check_no_simp_family.py` — pass.
- `git diff --check` — pass.

The fixture uses the exact dependent-function/update shape of Function.Basic
site 7 and a bounded `only` simp set so the focused recorder capture is
replay-neutral; the proof is closed with ordinary Lean steps.
