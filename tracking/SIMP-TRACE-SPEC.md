# simp trace format v1 (interface between trace capture and positional replay)

One trace per executed simp call. JSON object:

```
{ "schema": "simp-trace-v1",
  "module": "Mathlib.Logic.IsEmpty.Basic", "occurrence": "<occurrence id or source range>",
  "call": "<original simp syntax text>",
  "locations": [ { "loc": "goal" | {"hyp": "<user name>"},
                   "pre": "<pp of the location before>", "post": "<pp after, or null if closed>",
                   "steps": [ STEP, ... ],
                   "close": null | {"by": "rfl" | "trivial" | "assumption:<name>" | "eq_self" | "decide"} } ] }
```

`STEP` is one of:

- `{"kind":"rw", "pos": POS, "name": "<lemma or hyp name>", "dir": "fwd"|"rev",
   "args": ["<explicit arg term>", ...] (optional), "side": [TRACE-LIKE, ...] (optional),
   "before": "<pp of subterm>", "after": "<pp of subterm>"}`
  Rewrite exactly the subterm at `pos` with the equation or iff `name` (a global
  constant, or a local hypothesis in scope at that position, including binder
  variables introduced by the path). `side` holds, for each hypothesis of a
  conditional lemma, how it was discharged: a nested trace object with the same
  `steps`/`close` shape.
- `{"kind":"unfold", "pos": POS, "name": "<constant>", "before": ..., "after": ...}`
  Delta-unfold one constant at that position (definitional).
- `{"kind":"beta"|"eta"|"proj", "pos": POS, "before": ..., "after": ...}` Definitional
  reductions simp performs silently.
- `{"kind":"change", "pos": POS, "to": "<pp.all term>", "before": ...}` Last-resort
  definitional replacement when no named kind applies; replay checks defeq.
- `{"kind":"eq", "pos": POS, "lhs": "<pp>", "rhs": "<pp>", "by": "rfl"|"decide",
   "source": "<simproc name>"}` A simproc-computed equation. Replay proves it with
  the named ordinary tactic, never with the simproc.
- `{"kind":"intro_ctx", "pos": POS, "name": "<hyp name>"}` Contextual simp made the
  antecedent of an implication at `pos` available as a hypothesis for later steps.

`POS` is a JSON array of child indices from the root of the location, using
Lean's `SubExpr.Pos` convention: for `app f a`, 0 = f and 1 = a; for
`lam`/`forallE`, 0 = binder type and 1 = body; for `letE`, 0 = type, 1 = value,
2 = body; `mdata` and `proj` have child 0. Crossing a `lam`/`forallE` body
introduces that binder as a local for subsequent matching. `[]` is the whole
location. `before`/`after` are debug fields (pretty-printed subterms) used by
validation; replay must not depend on them.

Steps are applied in array order; each step's `pos` refers to the term as
produced by the previous step. Unknown `kind` values are a hard error for the
replay tactic. Any change to this file is a schema bump and a coordinator
decision.
