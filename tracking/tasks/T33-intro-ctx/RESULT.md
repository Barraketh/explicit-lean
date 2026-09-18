# T33 — scoped `intro_ctx` consumer

Implemented the closed consumer form for T34's stable contextual-binder
metadata. `intro_ctx` now requires a numeric introduced handle, exact domain
position, dependency local indices, scope enter/exit positions, and a closed
nested step list. The nested replay runs under the arrow-domain local and
exposes it only as `introduced_ref <handle>`; it rebuilds the arrow with a
kernel-checked forall congruence proof. No name lookup, context search,
serialized term/proof payload, or generic tactic slot is used.

Files changed:

- `ExplicitLean/ExplicitRw/Tactic.lean`
- `test/ExplicitRw/IntroCtx.lean` (Function.Basic site-7-shaped fixture)
- `test/ExplicitRw/Negative.lean` (scope/shape rejection expectation)

Checks:

- `lake build ExplicitLean.ExplicitRw` — PASS.
- `lake env lean test/ExplicitRw/IntroCtx.lean` — PASS.
- `lake env lean test/ExplicitRw/Negative.lean` — PASS.
- `python3 -B Experiment/check_no_simp_family.py` — PASS.
- `python3 -B Experiment/check_explicit_rw.py` — PASS (12 fixtures, 14
  rejected-syntax cases; axiom audit 136 theorems; 110 escape probes and 40
  benign probes).
- `git diff --check` — PASS.

The fixture uses the exact dependent-function/update shape of Function.Basic
site ordinal 7 and closes the contextual rewrite with ordinary `rfl`.
