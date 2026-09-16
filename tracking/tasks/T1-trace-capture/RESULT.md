# T1-trace-capture: RESULT

**Built.** `simp_trace` runs **stock simp** and emits `simp-trace-v1` JSON per
`tracking/SIMP-TRACE-SPEC.md`. Syntax mirrors `simp` with an optional leading
out-clause: `simp_trace (out := "p.json") +contextual only [f, ← g] at h *`.
Without `out` the JSON is logged as `simp-trace-json:{...}` for a driver. Slots
after `out` are positionally identical to `Parser.Tactic.simp`, so a real `simp`
node is rebuilt and passed to stock `mkSimpContext` (stock argument elaboration,
dischargers, config). Goal state matches stock simp: `Meta.simpGoal` takes no
`Methods`, so its structure is replicated with the same `applySimpResult*`
helpers; verified by compiling identical goals under `simp` and `simp_trace`
(goal, `at h`, `at *`, residual goals, `failIfUnchanged`).

**Positions: approach (b), plus two corrections the task did not anticipate.**
Replay recorded `(before, after)` pairs against a running term from the
pre-state, locate `before` structurally, one step per occurrence in pre-order.

1. *Definitional steps are invisible to `Simp.Methods`* — beta/proj/iota/zeta and
   delta unfolding run in `simpLoop`'s `reduceStep`, outside `pre`/`post`. Rather
   than fork simp's traversal (an escalation condition), `findBridge?` recovers
   them from the running term: when a `before` is unreachable it finds the single
   definitional reduction making it reachable and emits it as
   `unfold`/`beta`/`proj`/`change`. Bridges are validated like any other step.
2. *`post` fires on stale terms* — simp keeps the pre-rewrite parent and rebuilds,
   so a `post` firing's `before` can predate child rewrites already replayed.
   Recorded terms are refreshed against applied replacements before searching.

Binder crossings: simp-introduced locals (in the firing's context, not the
location's) are abstracted with `Expr.abstract`. `Expr.replace` is **wrong** here
— not binder-depth aware, wrong indices under nested binders. That bug passed all
13 original fixtures; only the IsEmpty measurement caught it.

Validation is in-tactic and fails loudly: per step, navigating `pos` reaches
`before`; replacing yields the next term; the final term equals simp's result.

**Kinds.** `rw` (globals both directions, local hyps, `simp [h]`, `simp at h`);
conditional lemmas with `side` sub-traces (nested simp steps; assumption
discharge as `assumption:<name>`); `eq` for simprocs (source recorded, `by` set
to `rfl`/`decide` only after a scratch check confirms it, else `"unknown"`,
counted and logged); `unfold`, `beta`, `proj`, `change` (`pp.all`); `close`.
`+contextual` works: contextual hyps named `ctx:<index>`, occurrence search
constrained by implication depth. **Not emitted in v1: `intro_ctx`, `eta`** —
contextual traces are correct without an explicit `intro_ctx` (the `ctx:<n>`
names carry the reference) and no fixture produced an eta contraction; both stay
in the checker's `KNOWN_KINDS`. Nothing is dropped silently: unattributable
firings raise `unattributed simp step`, unlocatable ones `cannot locate
recorded subterm`.

**Files.** `ExplicitLean/SimpTrace.lean` +
`SimpTrace/{Types,Recorder,Position,Tactic}.lean`;
`test/SimpTrace/{Fixtures.lean,IsEmptyBasicTraced.lean,expected/,.gitignore}`;
`Experiment/check_simp_trace.py`; this directory. Modules use the Lean module
system (`module` + `public meta import`), required for the `module`-based Mathlib
copy to import them. `ExplicitLean.lean` and `lakefile.toml` untouched.

**Checks — all run, all pass (macOS, Lean 4.32.2).**
`lake build ExplicitLean.SimpTrace` (oleans deleted first): clean, 8.0 s ·
`lake env lean test/SimpTrace/Fixtures.lean` (14 fixtures): pass, 3.4 s ·
`python3 -B Experiment/check_simp_trace.py`: `OK: 14 ... match`, 0.04 s ·
`lake env lean test/SimpTrace/IsEmptyBasicTraced.lean`: pass, 17/17, 2.6 s.
Checker verified to fail: perturbing a `pos` and a `dir` reported both, exit 1.

**Measurement — 17 `simp only` calls of `Mathlib/Logic/IsEmpty/Basic.lean`.**
All 17 traced, none unresolved. **76 steps, mean 4.5, range 2–6.** JSON per call:
mean 881 B, max 1127 B, **15.0 KB total**. Kinds: `rw` 70, `unfold` 6
(`Relator.{LeftTotal,RightTotal,BiTotal}`). No `eq`, `change`, or `by:"unknown"`.
Concise: ~0.9 KB/call against the rejected 7,113-line DAG for the same module.

**Limitations / open questions.** `intro_ctx` and `eta` unexercised (above);
adding them is small, not a redesign. Multi-occurrence emission is implemented
but never exercised by this corpus. `findBridge?` is bounded at 32 reductions;
exceeding it fails loudly rather than looping. Fixture `out :=` paths are
repo-root-relative, so compile fixtures from the root; `test/SimpTrace/{out,
isempty_out}/` are gitignored, `expected/` is committed. Reattribution probes
theorems individually when `usedTheorems` did not grow (lemma already fired) —
one extra match attempt per such step, not measurable here, worth watching on a
large module.
