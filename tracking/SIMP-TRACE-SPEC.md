# simp trace format v2 (interface between trace capture and positional replay)

Amended 2026-09-17 after T4 final review 4: every trace is tied to an exact
executable call in the uninstrumented pinned source. The producer emits a site
manifest and the consumer proves a complete bijection before rendering.
Generated-copy positions and filenames are diagnostic only. The environment is
not adversarial: cryptographic hashes, nonces and forgery resistance are not
part of this contract. The rejected stronger design is preserved historically
in `tracking/tasks/T9-site-trace-identity/DESIGN.md`.

Amended 2026-09-16 after T4 run 1: `invocation`/`invocations` for sites executed
more than once; rendering rule in PLAN.md step 3.
Amended 2026-09-16 after T1 round 6: side traces carry `pre`/`post`; dsimproc
firings are `change` steps with `source`.
Amended 2026-09-16 after T1 congr implementation: user `@[congr]` theorems are
`rw` steps with `source: "congr"` and `intros` on implication-shaped side traces.
Amended 2026-09-16 after T1 round 4: `congr` step kind for dependent
congruence transports; `ctxIndex` semantics clarified.
Amended 2026-09-16 after review round 3 of T1: `iota` kind, `prop` flag on
`rw` steps, `omega` side close, classified `unresolved:` outcomes.
Amended 2026-09-16 after review round 1 of T1/T2: `zeta` kind, `true_intro` and
`absurd:<hyp>` close forms (replacing `trivial`/`eq_self`), local-hypothesis
reference object. Schema id stays `simp-trace-v1` because nothing has shipped.
Amended 2026-09-23: named `zeta` events represent zeta-delta unfolding of a
local definition and carry its exact indexed `local` identity. Replay uses
`zeta_local local_ref <ctxIndex>`, avoiding serialization of the local body.

One trace per executed simp call. JSON object (identity fields are mandatory):

```
{ "schema": "simp-trace-v2",
  "modulePath": "Mathlib/Logic/IsEmpty/Basic.lean",
  "site": { "siteOrdinal": <source-order diagnostic ordinal>,
            "startChar": <inclusive Unicode scalar offset>,
            "endChar": <exclusive Unicode scalar offset>,
            "callText": "<exact original simp syntax text>" },
  "occurrence": "<diagnostic getRef position in generated traced copy>",
  "invocation": <k>, "invocations": <n> (a source site executed n times, e.g. under `t <;> simp`
                                        or inside a tactic run per goal, produces n traces numbered
                                        in execution order; the renderer decides the per-goal form),
  "locations": [ { "loc": "goal" | {"hyp": "<user name>"},
                   "pre": "<pp of the location before>", "post": "<pp after, or null if closed>",
                   "steps": [ STEP, ... ],
                   "close": null | {"by": "rfl" | "true_intro" | "assumption:<name>" | "absurd:<hyp name>" | "decide" | "nofun"} } ] }
```

The producer derives the site manifest from the uninstrumented source text,
then generates the traced copy. Every executable site must be present and
replaced exactly once. The consumer recomputes the source manifest and requires
an exact bijection by module path, character range, exact call slice, site
ordinal and complete invocation ordinals. Any missing, extra, duplicate,
malformed or mismatched record rejects the whole module as `identity_failed`
before rendering; it contributes zero replayed sites. Never map by filename,
list index, line number, generated position, or nearest call.
`"nofun"` closes a goal of the form `c₁ ... = c₂ ... → False` (distinct constructors) or
any goal refutable by empty pattern matching; replay is `exact nofun`. It is the close
form for `reduceCtorEq`-style side conditions.

The JSON `close.by` values above are unchanged. In generated `explicit_rw` source,
named exact-term closes use the self-delimiting form `close [<term>]` (for example,
`close [True.intro]` or `close [h.elim]`) so a following unbulleted tactic cannot
be consumed as another term argument. The tactic continues to accept legacy
`exact <term>` side-proof source. A goal close emitted after a hypothesis
rewrite uses a second `explicit_rw [] then close [<term>]`, so the term remains
self-delimiting.

`STEP` is one of:

- `{"kind":"rw", "pos": POS, "name": "<lemma or hyp name>", "dir": "fwd"|"rev",
   "args": ["<explicit arg term>", ...] (optional), "side": [TRACE-LIKE, ...] (optional),
   "before": "<pp of subterm>", "after": "<pp of subterm>"}`
  Rewrite exactly the subterm at `pos` with the equation or iff `name` (a global
  constant, or a local hypothesis in scope at that position, including binder
  variables introduced by the path). If `name` is Prop-valued rather than an
  equation (simp uses `p` as `p = True` and `¬p` as `p = False`), the step
  carries `"prop": "true"` or `"prop": "false"` and replay rewrites with
  `eq_true name` / `eq_false name` respectively. `side` holds, for each hypothesis of a
  conditional lemma, how it was discharged: a nested trace object with the same
  `steps`/`close` shape and, like a location, `pre` and `post` (pp of the
  side goal before and after; `post` null if closed). A side trace's `close.by` may additionally be `"omega"`
  when the user-supplied discharger was `omega`; any other non-simp discharger
  is recorded as `{"by": "unresolved:<discharger text>"}` and the whole call is
  reported unresolved (classified, not a generic abort).
- `{"kind":"unfold", "pos": POS, "name": "<constant>", "before": ..., "after": ...}`
  Delta-unfold one constant at that position (definitional).
- `{"kind":"beta"|"eta"|"proj"|"zeta"|"iota", "pos": POS, "before": ..., "after": ...}` Definitional
  reductions simp performs silently (`zeta` = `let x := v; b` to `b[v/x]`;
  `iota` = matcher/recursor application to a constructor, reduced one step).
  A `zeta` step may additionally carry `"name": "<local user name>"` when
  simp's `zetaDelta` option unfolds a local definition at that position. In
  this form it also carries the ordinary indexed `local` reference object for
  that exact let-declaration. Replay renders
  `zeta_local local_ref <ctxIndex> at [pos]`; `explicit_rw` directly checks
  that the selected subterm is that exact local free variable, reads its
  recorded local-declaration value, and checks the replacement by definitional
  equality. `before` and `after` remain diagnostic only, so a large or
  proof-bearing local body never becomes generated source. Legacy named-zeta
  traces without `local` may still render their authenticated `after` as
  `change`. A nameless `zeta` continues to denote contraction of a `let`
  expression. Reduction kinds other than `zeta` do not accept `name`.
- `{"kind":"change", "pos": POS, "to": "<ordinary Lean surface term>", "before": ..., "source": "<dsimproc name>" (optional)}`
  Definitional replacement when no named kind applies, including any
  dsimproc firing (`dreduceIte`, `Nat.reduceAdd` in dsimp mode, ...), which is
  definitional by construction and must not be recorded as a propositional
  `eq`; replay checks defeq. The recorder prints `to` as ordinary Lean surface
  syntax in the captured local context; implicit arguments, instances and
  universe levels are left for elaboration.
- `{"kind":"eq", "pos": POS, "lhs": "<pp>", "rhs": "<pp>", "by": "rfl"|"decide",
   "source": "<simproc name>"}` A simproc-computed equation whose proof is by
  kernel computation. Replay proves it with the named ordinary tactic, never
  with the simproc. A simproc whose returned proof is an application of one
  lemma (e.g. `reduceIte` returning `if_pos h`, `reduceDIte` returning
  `dif_pos h`) is NOT an `eq` step: it is recorded as an ordinary `rw` step
  with that lemma as `name`, the discharged condition as a `side` sub-trace,
  and `"source": "<simproc name>"` for provenance. A simproc proof that is
  neither is a classified `unresolved:simproc:<name>` outcome.
- `{"kind":"congr", "pos": POS, "arg": <i>, "steps": [STEP, ...], "before": ..., "after": ...}`
  Dependent congruence: the subterm at `pos` is an application `f a₀ ... aₙ` whose
  argument `i` is rewritten by the nested `steps` (positions relative to that
  argument), and later arguments that depend on it are transported by the
  auto-generated congruence theorem for `f` (`Lean.Meta.mkCongrSimp?`, which
  lives in `Lean.Meta.CongrTheorems`, not in the simplifier, and is what
  `conv => congr` uses). Replay must not call simp; it obtains the congruence
  theorem, proves the argument equation from the nested steps, and applies it.
  Use this kind only when plain positional rewriting would need casts (a
  `CongrArgKind.cast` dependent); ordinary arguments stay plain `rw` steps.
  A USER congruence theorem (`@[congr]`, e.g. `ite_congr`, `dite_congr`,
  `exists_prop_congr`, fired through `trySimpCongrTheorem?`) is not this kind:
  it is an ordinary `rw` step whose `name` is that theorem, with
  `"source": "congr"`, and one `side` sub-trace per hypothesis in order. A
  hypothesis of implication shape (`c → x = u`) is a side trace that first
  introduces its antecedents, recorded as `"intros": ["<name>", ...]` on the
  side trace object, followed by the steps proving the consequent. Replay is
  `rw [ite_congr h₁ h₂ h₃]` with each `hᵢ` proved by the side trace.
- `{"kind":"intro_ctx", "pos": POS, "name": "<hyp name>"}` Contextual simp made the
  antecedent of an implication at `pos` available as a hypothesis for later steps.

Local hypothesis references: when `name` is a local hypothesis rather than a
global constant, the step also carries
`"local": {"userName": "<name>", "inaccessible": true|false, "ctxIndex": <n>}`
where `ctxIndex` is the hypothesis's `LocalDecl.index` in the local context at
that point. It identifies the declaration; it is not a `rename_i` argument. A
generator derives `rename_i` names from the order of inaccessible declarations
in the context.
Hypotheses introduced by contextual simp use `{"contextual": true, "ctxIndex": <n>}`
instead; the two namespaces never collide. A replay generator names an
inaccessible hypothesis with `rename_i` before using it.

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
