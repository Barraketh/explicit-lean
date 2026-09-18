# T46 — fresh Function.Basic contextual-intro propagation

Fixed the sole T44 `Function.Basic` site-8 (line 683) renderer failure
(`missing_introduced_ref`).  The recorder now carries each contextual local's
stable T34 handle in its `local` record, and assembles `intro_ctx` enter/exit
events into T33's scoped nested step list, rebasing those steps to the
introduced forall body.  The renderer consumes only that numeric handle and
continues to fail closed when it is absent; it never falls back to an
inaccessible display name.  The finalizer required no change: its verbatim
location copy preserves the new metadata.

The fresh actual pipeline run was:

```text
python3 -B Experiment/pipeline/replay_module.py \
  --module Mathlib/Logic/Function/Basic.lean \
  --t1 /Users/ptsier/projects/explicit-lean \
  --t2 /Users/ptsier/projects/explicit-lean \
  --out /tmp/t46-function-basic-r2 --per-site-limit 8
```

It produced a fresh trace/finalizer run and compiled all 25 Function.Basic
sites as `replayed`; site 8 (source line 683, zero-based ordinal 7) is now
replayed.  Its final record contains `intro_ctx 0` with one scoped nested
rewrite and the contextual side local carries `"handle": 0`.

Focused checks:

- `lake build ExplicitLean.SimpTrace` — PASS.
- `lake build ExplicitLean.ExplicitRw` — PASS.
- `lake env lean test/SimpTrace/IntroCtxStable.lean` — PASS.
- `lake env lean test/ExplicitRw/IntroCtx.lean` and `Negative.lean` — PASS.
- `python3 -B test/SimpTrace/check_intro_ctx_metadata.py` — PASS.
- `python3 -B Experiment/pipeline/check_pipeline.py` — PASS, 331 checks.
- `python3 -B Experiment/check_no_simp_family.py` — PASS.
- `git diff --check` — PASS.

