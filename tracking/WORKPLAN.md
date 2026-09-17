# Work plan and task board

Governing rule: `AGENTS.md`. Plan: `PLAN.md` direction change section.
Protocol: `tracking/COORDINATION.md`. Interface: `tracking/SIMP-TRACE-SPEC.md`.

| Task | Scope | Depends on | Status | Branch | Review |
| --- | --- | --- | --- | --- | --- |
| T0-remote-host | On demand only: Scaleway GP1-L (32 vCPU, 128 GB, $0.89/hr). Provision only when a local job fails on resources; delete when idle for an extended period and re-provision later | a local resource failure | deferred (user decision 2026-09-16) | | |
| T1-trace-capture | `simp_trace` tactic: run stock simp with instrumented methods, emit spec-v1 JSON; fixtures + Python validator | spec | review round 7 running | task/T1-trace-capture | R6 fixed; structural rw validation added; pending from T2 R7: `change` steps lack `to`, most locations lack pre/post |
| T2-explicit-rw | `explicit_rw` positional replay tactic per spec, no simp machinery; fixtures with hand-written traces; conv reference | spec | fix round 7 in progress | task/T2-explicit-rw | R7: 0 critical/major, 3 minor, 1 trivial; integration gate 5/5 traces replay |
| T3-compliance | Rewrite two `dsimp` overrides; simp-family lint for overrides and generated regions | none | **merged** (af33e32) | task/T3-compliance | R3: NO DEFECTS |
| T4-pipeline | Per-module driver: capture traces for a module, render `explicit_rw` source with original comment, build, oracle | T1, T2 | planned | | |
| T5-cone | Run T4 on the seven-module cone (91 calls); record per-call outcomes | T0, T4 | planned | | |
| T6-readability-pass | Collapse top-level steps to `rw`/`exact`/`change` when re-elaboration matches | T2 | planned | | |

Log (newest first):

- 2026-09-16: T2 round 7: no critical/major; `elabStrict` withstood 8 attacks; `congr` refused every unsound rebuild; 270-probe recursive-slot sweep 0 escapes; integration gate 5/5 T1 traces replay. Two T1-side findings held for T1's next fix round: `change` steps carry no `to`, 59/61 locations omit `pre`/`post`. T1: structural rw validation (re-elaborate every recorded lemma against before/after) added with zero corpus false positives; review round 7 running with a Logic/Basic measurement.

- 2026-09-16: T1 round 6: zero divergence on 20 dsimp-path goals; defects: character-whitelist name resolution (non-ASCII hypotheses), explicit class-typed args unrecorded, plumbing-head list incomplete, dsimproc firings as propositional `eq`, macro-scope erasure in closes. Spec bump e95c745: side traces carry pre/post; dsimproc firings are `change` with `source`. Fix dispatched.

- 2026-09-16: T1 round 5: fidelity confirmed (no goal-state divergence, 1.01x overhead, T2 replays ordinary and user-congr traces verbatim); defects in local-hypothesis origins, `propext` misclassified as a rewriting lemma, a misplaced unresolved marker, `withInDSimp` not entered, and drifted RESULT.md counts (now to be script-generated). T2 asked to add `congr` step syntax via `mkCongrSimp?`.

- 2026-09-16: T1: `congr` kind implemented for cast transports; user `@[congr]` theorems recorded as `rw` with `source: "congr"` and `intros` side traces (spec 2e73661); all 46 calls across five modules trace clean. T2 round 6: critical `eq`-slot `sorryAx` acceptance (false theorem compiles); decision: one strict elaboration helper for all sites plus runner-enforced `#print axioms`; also recursive closed side-proof grammar (`intro h; explicit_rw [...] then rfl`) for implication-shaped side conditions.

- 2026-09-16: T1 round 4 fixed: the panic's root cause was a mis-ported `subst` loop in `tryAutoCongrTheoremT?`, not the binder path; `dsimpT` re-ported verbatim; 46/46 calls across five modules trace, zero panics/validation failures; Function/Basic 19 calls, 3.84s vs stock 2.62s. Six calls unresolved because dependent congruence transports had no representation: spec gains a `congr` step kind (replay via `mkCongrSimp?`, which is not simp), T1 implementing it now; T2 gets it next round. T2 round 5 fixed plus a self-found `sorryAx` acceptance hole; round 6 review auditing every elaboration site.

- 2026-09-16: T1 round 4: fork fidelity good across 41 functions and performance fine (0.82x real module, 1.99x pathological), but `zeta := false`/`letToHave` shapes fail, a loose-bvar panic on Logic/Function/Basic.lean:390, `dsimpT` dropped three upstream behaviours, a fixture exit code was misreported, `nofun` unimplemented. T2 round 5: no safety defects (385 probes; closed-set tactics hygienic); fidelity fixes plus a class-polymorphic instance-resolution failure found by integration. Both fix rounds dispatched.

- 2026-09-16: T3 review round 3 clean; merged into the working branch. T1b fork complete: 31 functions copied from Simp/Main.lean + 6 from Types.lean with `SOURCE:` annotations, reconstruction deleted, exponential chains now flat, simproc proofs classified generically (`reduceIte` -> `ite_cond_eq_true` etc. as `rw` with `side`); simp result cache disabled in the fork (watch performance). Spec: `nofun` close form for `reduceCtorEq`. T2 round 4 fixes in (grammar widened to pp output, `iota`, `with [...]`, `eq_true`/`eq_false`). Reviews running: T1 R4 (incl. fork fidelity diff and performance on Function/Basic), T2 R5.

- 2026-09-16: T1 review round 3: 2 critical (unattributed simproc/iota firings; exponential `findBridgeChain?`), 3 major (custom discharger, real-Mathlib failures with leaked fvar, Prop-valued lemmas recorded as `rw`), and the reviewer refuted the fork assessment's congruence claim. Decision: fork simp's traversal in the recorder (T1b, fresh implementer, same branch); reconstruction code to be deleted; validator kept. Spec amended (`iota`, `prop` flag, `omega` side close, classified `unresolved:`). T2 round 3: MetaM term-elab smuggler defeated both guards; fixed with a parser-level whitelist grammar; round 4 review running. T3 round 2: three low attribute-spelling gaps; fix in progress.

- 2026-09-16: user permitted forking simp's traversal in the recorder. T1 implementer assessed and declined for now (600-700 lines to resync per Lean bump; congruence-slot mapping remains either way); replaced single-step bridge with breadth-first `findBridgeChain?`, fixed `whnf` panic on open terms, delimiter now `=>trace`. T2 round 2 fixed (semantic tactic-mvar guard, `withLetDecl` let handling, `zeta` kind, bare `assumption` dropped as it searches). Round 3 reviews dispatched for both, with a second real-module measurement and integration replay in T1's.

- 2026-09-16: T3 review round 1: only two low defects (lint flags `attribute [simp]` forms); fix dispatched. T2 review round 2: round-1 fixes verified, 4 new major (`let` handling changes term shape; macro-expanded `by simp` bypasses syntax guard; no `zeta` kind); fix dispatched with semantic tactic-mvar guard. T1/T2 `proj` cross-check: no mismatch. T1 round-1 fixes complete (`with_trace` trailing clause); review round 2 running with a hand-translated integration test.

- 2026-09-16: T3 implemented (both `dsimp` overrides rewritten with `show`/`rw`/`unfold`/`exact`; lint in the loader `simp_manual_overrides.py`; note `check_simp_manual_composition.py` fails on main too, in the retired formatter). Review round 1 dispatched.
- 2026-09-16: T1 review round 1: 11 defects, notably `simp_trace` rejecting `(config := ...)` forms, `+decide` unattributed, shadowed binders and `let` unlocatable, unbounded `out` path, hypothesis labels colliding. Spec amended (`zeta`, close forms, local refs); fixes dispatched.
- 2026-09-16: T2 review round 1: 7 defects, notably `then`/`eq ... by` accepting arbitrary tactics (product-rule hole); closed set now `rfl | decide | assumption | exact <term without by>`; fixes dispatched.

- 2026-09-16: T1 implemented (7 commits). Positions via post-hoc localisation with in-tactic validation; definitional steps recovered by `findBridge?` since simp performs them outside `pre`/`post`. Measurement on IsEmpty.Basic: 17/17 calls traced, 76 steps, 15 KB total (~0.9 KB/call) versus the rejected 7,113-line DAG. `intro_ctx`/`eta` not emitted in v1. Review round 1 dispatched.

- 2026-09-16: T2 implemented (6 commits, direct Expr navigation, dependent positions refused with error, `at *` and `intro_ctx` not implemented). Open question raised: `explicit_rw` matches up to reducible defeq, so the readability post-pass must re-verify before collapsing to `rw`. Review round 1 dispatched.

- 2026-09-16: user chose Scaleway GP1-L as the remote worker, but only if local work fails on resources; AWS ruled out (not cheaper). Pricing in tracking/tasks/research-cloud-pricing.md.
- 2026-09-16: protocol, spec and board created; T1, T2, T3 dispatched in parallel on the Mac; cloud worker pending user choice.
