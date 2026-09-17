# T1-trace-capture: RESULT

**Built.** `simp_trace` runs **stock simp**, emitting `simp-trace-v1` JSON per the amended spec. It accepts
every form `simp` accepts — `(config := ...)`, `(discharger := ...)`, `(disch := ...)`, `+decide`, `-flag`,
`only`, `[*]`, `[← h]`, `at h ⊢`, `at *` — plus a trailing `with_trace "<path>"`; without it the JSON is
logged as `simp-trace-json:{...}` for a driver. The delimiter is load-bearing: a *leading* `(out := ...)`
makes the parser commit on `(` and blocks simp's parenthesized forms, a *trailing* one is eaten by
`optConfig`, and a bare trailing `out :=` is eaten by the `location` parser after `at h`; a distinct keyword
is unambiguous everywhere. Other slots stay positionally identical to `Parser.Tactic.simp`, so a real `simp`
node is rebuilt and passed to stock `mkSimpContext`. Goal state matches stock simp: `Meta.simpGoal` takes no
`Methods`, so its structure is replicated with the same `applySimpResult*` helpers, verified by compiling
identical goals under both.

**Positions: approach (b), plus three corrections the task did not anticipate.** Replay recorded
`(before, after)` pairs against a running term from the pre-state, locate `before` structurally, one step per
occurrence in pre-order. (1) *Definitional steps are invisible to `Simp.Methods`*: beta/proj/iota/zeta and
delta unfolding run in `simpLoop`'s `reduceStep`, outside `pre`/`post`; rather than fork simp's traversal (an
escalation condition), `findBridge?` recovers them from the running term and emits
`unfold`/`beta`/`proj`/`zeta`/`change`, validated like any other step. (2) *`post` fires on stale terms*:
simp keeps the pre-rewrite parent and rebuilds, so a `post` firing's `before` can predate child rewrites
already replayed; recorded terms are refreshed first. (3) *A refreshed term collapsing to the step's own
`after` is a no-op match* that consumes the step at the wrong position — rejecting those is what makes
shadowed binders and `let` work. Binder crossings use `Expr.abstract`; `Expr.replace` is **wrong** here (not
binder-depth aware). Validation is in-tactic and fails loudly: navigating `pos` reaches `before`, replacing
yields the next term, and the final term equals simp's actual result.

**Kinds.** `rw` (globals both directions, local hyps, `simp [h]`, `simp at h`); conditional lemmas with
`side` sub-traces; `eq` for simprocs and `+decide` closures (`by` set only after a scratch check confirms the
tactic proves it); `unfold`, `beta`, `proj`, `zeta`, `change`; `close` in the amended forms. Local references
carry the spec's `local` object, contextual hypotheses in the separate namespace. **Not emitted in v1:
`intro_ctx`, `eta`** — unexercised, both still in the checker's `KNOWN_KINDS`. Nothing is dropped silently:
unattributable firings, unlocatable subterms, bridge-bound exhaustion and unnameable closes each raise
distinct errors.

**Round 1 fixes** — all 11 defects of REVIEW-1, each reproduced before and after. *Critical:* (1)
parenthesized `simp` forms were unparseable — out-clause moved to a trailing `with_trace`; (2) `+decide`
aborted — unattributed Prop→`True`/`False` firings now route to `mkEqStep` after reattribution fails,
recording `eq`/`by:decide`/`source:decide`; (3) shadowed binders and (4) `let` failed position solving —
fixed by rejecting no-op refreshed matches (correction 3 above) and adding `zeta` to `reduceHere?` as the
amended spec's kind. *Major:* (5) cache policy now mirrors stock simp
(`wellBehavedDischarge := discharge?.isNone`); (6) writes are confined to the package root or
`SIMP_TRACE_OUT_ROOT`, `..` escapes normalised away, covered negatively by `test/SimpTrace/OutsideRoot.lean`
and a checker assertion; (7) close forms follow the amendment, `absurd:<hyp>` names the eliminated
hypothesis, and an unnameable close is an error rather than a guessed `rfl`; (8) `ctx:<n>` labels replaced by
the spec's `local` object, contextual hypotheses in their own namespace so they cannot collide with
inaccessible ordinary ones. *Minor:* (9) the 32-reduction bridge bound now throws instead of returning
empty; (10) side `close` and `steps` reconciled — a bare-hypothesis discharge drops its dead steps, otherwise
the steps are the discharge and `close` is `true_intro`; (11) this file rewritten, all claims re-verified.

**Files.** `ExplicitLean/SimpTrace.lean` + `SimpTrace/{Types,Recorder,Position,Tactic}.lean`;
`test/SimpTrace/` (`Fixtures.lean`, `IsEmptyBasicTraced.lean`, `OutsideRoot.lean`, `expected/`,
`.gitignore`); `Experiment/check_simp_trace.py`; this directory. Modules use the Lean module system so the
`module`-based Mathlib copy can import them; `ExplicitLean.lean`/`lakefile.toml` untouched.

**Checks — all rerun from scratch, all pass (macOS, Lean 4.32.2).** `lake build ExplicitLean.SimpTrace`
(oleans deleted first): clean, 7.7 s. `lake env lean test/SimpTrace/Fixtures.lean` (26 fixtures): pass,
3.2 s. `python3 -B Experiment/check_simp_trace.py`: `OK: 26 ... and out-of-root paths are refused`, 3.1 s.
`lake env lean test/SimpTrace/IsEmptyBasicTraced.lean`: pass, 17/17, 2.5 s. Both checker assertions were
verified to fail on a regression (a perturbed `pos`/`dir`; an in-root negative fixture).

**Measurement — 17 `simp only` calls of `Mathlib/Logic/IsEmpty/Basic.lean`.** Unchanged in substance: all 17
traced, none unresolved, **76 steps, mean 4.5, range 2–6**, kinds `rw` 70 / `unfold` 6. Sizes moved slightly
with the `true_intro` rename: mean 886 B (was 881), max 1132 B (was 1127), **15 068 B total** (was 14 983) —
still ~0.9 KB/call against the rejected 7,113-line DAG for the same module.

**Limitations.** `intro_ctx`/`eta` and multi-occurrence emission are unexercised by this corpus. Compile
fixtures from the package root (`out/`, `isempty_out/` gitignored; `expected/` committed). Reattribution
probes theorems individually when `usedTheorems` did not grow: one extra match attempt per such step, worth
watching on a large module.
