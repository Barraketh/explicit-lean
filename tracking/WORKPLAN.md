# Work plan and task board

Governing rule: `AGENTS.md`. Plan: `PLAN.md` direction change section.
Protocol: `tracking/COORDINATION.md`. Interface: `tracking/SIMP-TRACE-SPEC.md`.

| Task | Scope | Depends on | Status | Branch | Review |
| --- | --- | --- | --- | --- | --- |
| T0-remote-host | On demand only: Scaleway GP1-L (32 vCPU, 128 GB, $0.89/hr). Provision only when a local job fails on resources; delete when idle for an extended period and re-provision later | a local resource failure | deferred (user decision 2026-09-16) | | |
| T1-trace-capture | `simp_trace` tactic: run stock simp with instrumented methods, emit spec-v1 JSON; fixtures + Python validator | spec | fix round 9 in progress | task/T1-trace-capture | R9 merge gate failed: 48/78 traces replay; 4 critical (side goal recorded as subterm; `name` holds raw syntax; inaccessible tokens; off-by-one position), 3 major, 1 minor |
| T2-explicit-rw | `explicit_rw` positional replay tactic per spec, no simp machinery; fixtures with hand-written traces; conv reference | spec | fix round 8 in progress | task/T2-explicit-rw | R8: no soundness defects; 4 major in gates/docs (axiom audit, sweep slots, rename_i docs, forms table) |
| T3-compliance | Rewrite two `dsimp` overrides; simp-family lint for overrides and generated regions | none | **merged** (af33e32) | task/T3-compliance | R3: NO DEFECTS |
| T4-pipeline | Per-module driver: transcribe, trace, render `explicit_rw` source with original comment, splice, compile in T2 worktree, per-site report attributed to a side | T1, T2 worktrees (read-only) | implemented; review round 1 running | task/T4-pipeline | R1 pending |
| T5-cone | Run T4 on the seven-module cone (91 calls); record per-call outcomes | T0, T4 | planned | | |
| T6-readability-pass | Collapse top-level steps to `rw`/`exact`/`change` when re-elaboration matches | T2 | planned | | |

## Next steps (written at session end, 2026-09-16)

### Active resume batch (2026-09-17)

Coordinator-only session; implementation and adversarial review are delegated to
Luna at high reasoning in the existing task worktrees. Fresh Codex telemetry at
batch start reports ordinary work available with no rate-limit or spend stop.
The coordinator reads only committed `RESULT.md` / `REVIEW-*.md` summaries and
terse completion notices, then makes merge and next-dispatch decisions.

- **T2 review 9: COMPLETE.** No critical or major defects; review commit
  `dbb6c703`. T2 merged to main at `5ec2da5` and is wired through
  `ExplicitLean.lean`. Focused main-check rerun is the integration gate.
- **T1 review 10: MAJOR, fix dispatched.** Round-9 fidelity checks passed, but
  validator reasons from nested side steps are logged without being serialized
  on the exact nested `Step`, permitting known-bad replay. The bounded fix must
  propagate structured verdicts recursively through side/congr trees, add
  fail-closed JSON regressions, and return for review 11.
- **T4 review 2 fix COMPLETE; review 3 running.** Commits `c47f3fe`/`646e6bf`
  plan replacements and aggregated marker insertions entirely against original
  coordinates; 194 focused checks pass. A fresh incremental reviewer is
  attacking same-line, mixed, Unicode and multi-line cases. Per-branch
  multiple-invocation rendering follows only after this merge gate passes.
- **Named `zeta` decision:** T1's local-let fvar delta is represented as an
  existing `change` step with an explicit `pp.all` `to` value. Plain `letE`
  zeta remains `zeta`. Do not broaden T2's zeta semantics or add a name-based
  step; the fixed position plus kernel-checked definitional equality is the
  portable contract. Implement after the current T1 round-10 fix to avoid
  overlapping ownership.
- **T6 multi-invocation design: COMPLETE.** Commit `b2a03c2` classifies all 16
  sites / 38 executions into four source shapes. Decision: deterministic
  structural bullet expansion keyed only by complete invocation ordinals; no
  `first` dispatch or goal fingerprints. Non-tail continuations may be copied
  only when simp-free and scope/order preserving; otherwise refuse the site.
  T1 must emit the specified ordinals before T4 implementation begins.
- **T7 declaration-oracle design: COMPLETE.** Commit `3615686` specifies a
  source-pair gate with a stock companion carrying the same ExplicitRw import.
  Reuse the existing oracle and strict parser unchanged; `replayed` requires
  compile plus oracle success. Whole-module failures remain module-scoped and
  per-site attribution requires an isolated successful compile. Implement only
  after T4's current merge gate passes.
- **T5 cone preflight:** independent read-only work is reconciling the corrected
  six-module denominator with the 91-call headline, inventorying
  `Data.Option.Basic`, and specifying the translated-import-root build order.

After a slot completes, reuse it immediately for the next independent review or
fix. The coordinator alone integrates accepted branches and updates this plan.

State at handoff: main branch clean at this commit. Task branches (each in
`/Users/ptsier/projects/explicit-lean-worktrees/<task>`, all committed, no
uncommitted work): `task/T1-trace-capture` (recorder, forked simp traversal;
round 9 fixes COMPLETE and committed: all four criticals, both majors, minor 7
and the replay fixtures; harness replay at this tip 50/82; the 6 failures the
harness attributes to t2 are steps T1 now classifies via a new field the T4
renderer does not read yet; `.stx` steps were previously never validated,
classified lines rose 16 to 29; RESULT.md 215 lines; awaiting incremental
review 10), `task/T2-explicit-rw`
(replay tactic; round 8 fixes committed at 6dc6932+, all 9 items fixed incl. the axiom-set audit; awaiting incremental review 9; one open coordinator item: whether `zeta` steps carry a `name`, which the spec does not define),
`task/T4-pipeline` (harness; review round 1 done, REVIEW-1.md at 171079f: 3 major, no critical: `@[` lines skipped hide two sites so the corpus is 84 not 82; stale diagnostics mis-charged to sites; mid-line retained originals drop the `unresolved:` marker; plus minors incl. the harness never running the simp-family lint). T3 is merged.
Agents from this session are gone; a new session re-dispatches per
`tracking/COORDINATION.md` (revised gate: no critical/major; incremental
reviews; harness replay counts are the primary test).

1. **T2 merge gate.** Dispatch an incremental review 9 of `task/T2-explicit-rw`
   (verify REVIEW-8 fixes: axiom-set audit, structured sweep slots, `rename_i`
   docs and fixture, complete step-forms table). If no critical/major, merge
   into main and wire `ExplicitLean.ExplicitRw` into `ExplicitLean.lean`.
2. **T1 incremental review 10** (round 9 fixes are committed; see RESULT.md
   "Round 9 fixes"). Main input: the T4 harness replay table at the T1 tip.
   Check the new classification field T1 added and decide whether T4's
   renderer reads it (spec update if so).
   Merge when no critical/major; wire `ExplicitLean.SimpTrace` (recorder only,
   not product) into the build.
3. **T4 fix round 1** (REVIEW-1.md items above), then an incremental review 2. Then
   implement the multiple-invocation rendering rule (PLAN.md step 3,
   "Rendering"), switch the harness from driving worktrees by path to the
   merged main checkout, and add the declaration oracle
   (`Experiment/SimpEngineDeclarationOracle.lean`) as a post-compile check.
4. **Iterate on the six-module table** until every non-replayed site is either
   a classified unresolved with an agreed reason or a tracked defect. First
   run: 82 sites, 45 replayed, 1 unresolved, 27 render_failed, 9 compile_failed.
5. **T5 cone.** Run the harness on the seven-module cone (Logic.Basic,
   ExistsUnique, Function.Basic, Function.Defs, IsEmpty.Basic,
   Nontrivial.Defs, Data.Option.Basic) with a translated import root so
   modules import translated dependencies, and record per-call outcomes in
   `campaign.json`. Data.Option.Basic is the only cone module not yet traced.
6. **Follow-ups (minors, tracked, not blocking):** T2 error-message wording
   items from REVIEW-7/8; implement the recorded named-`zeta` decision; T1/T2
   RESULT.md length; the harness `.gitignore` line.
7. **Remote worker:** none provisioned. Provision Scaleway GP1-L only if a
   local job fails on resources (see `campaign.json.remoteWorker`).

Log (newest first):

- 2026-09-16: T4 harness built (179 unit checks). First six-module run at T1 1d8ba00 / T2 7ccb98b: 82 sites, 45 replayed, 1 unresolved, 27 render_failed, 9 compile_failed; attribution t1 21, harness 16, t2 0. Largest blocks: 16 sites executed more than once (`t <;> simp`), 11 `rw.name` holding raw syntax (T1 R9 defect), 4 quantified `prop` steps without `args`. Spec gains `invocation`/`invocations`; PLAN gains the per-goal rendering rule. T4 review round 1 dispatched.

- 2026-09-16: user decision after slow convergence: merge gate is now no critical/major (minors tracked), reviews incremental after round 2, end-to-end replay is the primary test (COORDINATION.md e2ffee1). T4 pipeline harness dispatched driving the T1 and T2 worktrees read-only. T1 round 9: mechanical replay 48/78, all failures T1-side (side goal recorded as the simproc subterm, raw syntax in `name`, inaccessible tokens, one off-by-one position); fix dispatched. T2 round 8: no soundness defects; gate/doc majors in fix.

- 2026-09-16: T1 round 8: Logic/Basic's 12 classified lines are 6 sites: 6 genuine dependent-proof transports, 6 false positives (side goals `True`/`¬False` never inspected). Also `Ne`-stated lemmas always rejected, side-trace positions outer-relative, `args` with `⋯`, two `; simp` sites untransplanted. Fix dispatched with structural guards (checker validates side positions; args re-elaborated from text; site-count check on traced copies).

- 2026-09-16: T1 round 7: fidelity clean (25 goals byte-identical; Logic/Basic 42 calls, 1.33x wall) but quantified/conditional local hypotheses unresolved with the validator passing them as "none", `exists_prop_congr` false positive from reversed args, `of_eq_true` misdescribed as rfl, and 4 `unexpected bound variable` crashes. Decision: "none" is never a pass; every origin resolves or the call is classified. Fix dispatched with T2's `to`/pre-post findings folded in.

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
