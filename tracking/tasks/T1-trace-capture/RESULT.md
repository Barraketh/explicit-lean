# T1-trace-capture: RESULT

**Built.** `simp_trace` runs **stock simp**, emitting `simp-trace-v1` JSON per the amended spec. It accepts
every form `simp` accepts — `(config := ...)`, `(discharger := ...)`, `(disch := ...)`, `+decide`, `-flag`,
`only`, `[*]`, `[← h]`, `at h ⊢`, `at *` — plus a trailing `=>trace "<path>"`; without it the JSON is logged
as `simp-trace-json:{...}` for a driver. The delimiter took three attempts and is worth stating: a *leading*
`(out := ...)` makes the parser commit on `(` and blocks simp's parenthesized forms; a *trailing* one is
eaten by `optConfig`; a plain keyword atom parses but is reserved globally on import, so it breaks any
identifier of that name; a *non-reserved* keyword is swallowed by the `location` parser after `at h`.
`=>trace` is not an identifier at all, so it is unambiguous for the parser and invisible to the namespace —
theorems and hypotheses named `with_trace` or `trace` compile alongside it. Other slots stay positionally
identical to `Parser.Tactic.simp`, so a real `simp` node is rebuilt and passed to stock `mkSimpContext`.

**Positions: approach (b), plus four corrections the task did not anticipate.** Replay recorded
`(before, after)` pairs against a running term from the pre-state, locate `before` structurally, one step per
occurrence in pre-order. (1) *Definitional steps are invisible to `Simp.Methods`*: beta/proj/iota/zeta and
delta unfolding run in `simpLoop`'s `reduceStep`, outside `pre`/`post`; the bridge search recovers them from
the running term (forking was barred when this was written, and stays unattractive — see below) and emits
`unfold`/`beta`/`proj`/`zeta`/`change`, validated like any other step. (2) *`post` fires on stale terms*:
simp keeps the pre-rewrite parent and rebuilds, so a `post` firing's `before` can predate child rewrites
already replayed; recorded terms are refreshed first. (3) *A refreshed term collapsing to the step's own
`after` is a no-op match* that consumes the step at the wrong position — rejecting those is what makes
shadowed binders and `let` work. (4) *One reduction is not enough*: `findBridgeChain?` searches
breadth-first over reduction *sequences* (bounded at 32), because Mathlib stacks `@[reducible]`/`abbrev`
definitions and exposing a subterm can need several delta steps composed at one position; each link is
emitted as its own step. Binder crossings use `Expr.abstract`; `Expr.replace` is **wrong** here (not
binder-depth aware). Validation is in-tactic and fails loudly: navigating `pos` reaches `before`, replacing
yields the next term, and the final term equals simp's actual result.

**Kinds.** `rw` (globals both directions, local hyps, `simp [h]`, `simp at h`); conditional lemmas with
`side` sub-traces; `eq` for simprocs and `+decide` closures (`by` set only after a scratch check confirms the
tactic proves it); `unfold`, `beta`, `proj`, `zeta`, `change`; `close` in the amended forms. Local references
carry the spec's `local` object, contextual hypotheses in the separate namespace. **Not emitted in v1:
`intro_ctx`, `eta`** — unexercised, both still in the checker's `KNOWN_KINDS`. Nothing is dropped silently:
unattributable firings, unlocatable subterms, bridge-bound exhaustion and unnameable closes — in the main
trace *and* in side conditions — each raise distinct errors.

**Round 1 fixes** — all 11 defects of REVIEW-1, each reproduced before and after. *Critical:* (1)
parenthesized `simp` forms were unparseable — out-clause moved to a trailing delimiter; (2) `+decide`
aborted — unattributed Prop→`True`/`False` firings now route to `mkEqStep` after reattribution fails; (3)
shadowed binders and (4) `let` failed position solving — fixed by rejecting no-op refreshed matches and
adding `zeta` to `reduceHere?`. *Major:* (5) cache policy mirrors stock simp
(`wellBehavedDischarge := discharge?.isNone`); (6) writes confined to the package root or
`SIMP_TRACE_OUT_ROOT`; (7) close forms follow the amendment, `absurd:<hyp>` names the eliminated hypothesis,
and an unnameable close is an error rather than a guessed `rfl`; (8) `ctx:<n>` labels replaced by the spec's
`local` object. *Minor:* (9) the bridge bound throws instead of returning empty; (10) side `close` and
`steps` reconciled; (11) RESULT.md claims corrected.

**Round 2 fixes** — all 6 defects of REVIEW-2, each reproduced before and after. *Critical:* (1) a 2-deep
`@[reducible]` chain aborted — `findBridge?` accepted only a reduction that *immediately* exposed the
target, so a chain never started; replaced by the breadth-first `findBridgeChain?` above, verified at depths
2, 3 and 4. Fixing this surfaced a second bug: `reduceHere?` called `whnf`/`unfoldDefinition?` on subterms
carrying loose bvars, which **panics** the elaborator; it now takes only the syntactic reductions there.
*Major:* (2) `eraseMacroScopes` turned inaccessible `a✝` into plain `a` — the name of a *different,
accessible* local, so the trace claimed a rewrite the goal never made; `name` is now the pretty-printed form
(`a✝`), with the raw user name and `ctxIndex` in `local`. (3) a symlink under the root defeated containment,
since textual `..` collapsing cannot see through one; both root and target are now resolved with
`IO.FS.realPath` before comparison. (4) side-condition `close:{"by":"unknown"}` was written silently,
contradicting this file; it is now the same hard error the main trace already raised. *Minor:* (5) the
delimiter no longer reserves a global token (see above); (6) the two overstated claims are narrowed — goal
state was verified to match stock simp on the reviewer's 18-form corpus and every fixture, not universally,
and the "nothing dropped silently" claim now holds for side closes too.

**Fork assessment** (user relaxation permitting a forked traversal; option (b) chosen). A fork would replace
`Position.lean`'s reconstruction — `findBridgeChain?`, `reducibleSites`, `refresh`, `findOccurrences`, the
no-op-match rule (~200 lines) — with an exact `SubExpr.Pos` threaded through the traversal, copying
`simpLoop`/`simpStep`/`simpApp`/`simpLambda`/`simpForall`/`simpArrow`/`simpLet`/`simpProj`/`visitFn`/`congr`/
`reduceStep`/`reduce`/`unfold?` and private helpers from `Simp.Main` (~480 lines) **plus**
`simpAppUsingCongr`/`tryAutoCongrTheorem?` from `Simp.Types` (~180) — ~600-700 lines to resync each Lean
bump. It would have prevented round-1 defects 3-4 and round-2 defect 1 outright and made round-1 defect 10
moot, but not the other 14 (frontend, naming, path, policy). (b) because the hard part survives:
`simpAppUsingCongr` rebuilds through congruence *lemmas*, so a fork still maps congruence-argument slots to
child indices — the same problem, moved. Revisit if a corpus module defeats the chain search.

**Files.** `ExplicitLean/SimpTrace.lean` + `SimpTrace/{Types,Recorder,Position,Tactic}.lean`;
`test/SimpTrace/` (`Fixtures.lean`, `IsEmptyBasicTraced.lean`, `OutsideRoot.lean`, `SymlinkEscape.lean`,
`expected/`, `.gitignore`); `Experiment/check_simp_trace.py`; this directory. Modules use the Lean module
system so the `module`-based Mathlib copy can import them; `ExplicitLean.lean`/`lakefile.toml` untouched.

**Checks — all rerun from scratch, all pass (macOS, Lean 4.32.2).** `lake build ExplicitLean.SimpTrace`
(oleans deleted first): clean, 8.0 s. `lake env lean test/SimpTrace/Fixtures.lean` (30 fixtures): pass,
3.8 s. `python3 -B Experiment/check_simp_trace.py`: `OK: 30 ... and out-of-root paths (including through
symlinks) are refused`, 5.9 s. `lake env lean test/SimpTrace/IsEmptyBasicTraced.lean`: pass, 17/17, 2.4 s.
All three checker assertions were verified to fail on a regression (a perturbed `pos`/`dir`; an in-root
negative fixture; an in-root symlink fixture). REVIEW-1 and REVIEW-2 repros were all re-run after the fixes.

**Measurement — 17 `simp only` calls of `Mathlib/Logic/IsEmpty/Basic.lean`.** Unchanged in substance: all 17
traced, none unresolved, **76 steps, mean 4.5, range 2–6**, kinds `rw` 70 / `unfold` 6. Byte figures moved
with the delimiter rename (it appears in each trace's `call` field): mean 883.4 B (round 1: 886), max
1129 B (1132), **15 017 B total** (15 068) — still ~0.9 KB/call against the rejected 7,113-line DAG.

**Limitations.** `intro_ctx`/`eta` and multi-occurrence emission are unexercised by this corpus. The bridge
chain search is bounded at 32 reductions and throws past that. Compile fixtures from the package root
(`out/`, `isempty_out/` gitignored; `expected/` committed). Reattribution probes theorems individually when
`usedTheorems` did not grow: one extra match attempt per such step, worth watching on a large module.
