# T1-trace-capture: adversarial review, round 2

Scope check passed: `git diff --stat $(git merge-base codex/search-free-mathlib-2026-08-31
task/T1-trace-capture) task/T1-trace-capture` lists 39 files, all inside
`ExplicitLean/SimpTrace.lean`, `ExplicitLean/SimpTrace/`, `test/SimpTrace/`,
`Experiment/check_simp_trace.py`, `tracking/tasks/T1-trace-capture/`. Working tree clean.

**All round-1 defects re-verified fixed** by re-running REVIEW-1's reproducing commands with
the trailing `with_trace` clause, not by reading the diff. 1 (parenthesized forms): `(config :=
{ decide := true })`, `(discharger := assumption)`, `(disch := assumption)` all parse and
elaborate. 2 (`+decide`): records `eq`/`by:decide`/`source:decide`, no abort. 3 (shadowed
binders) and 4 (`let`): both close, emitting `beta` and `zeta` steps. 5: `wellBehavedDischarge
:= discharge?.isNone` at `Recorder.lean:280`. 6: `..` escapes and absolute paths refused
(but see defect 3 below). 7: `absurd:h`, naming the hypothesis. 8: `local` object replaces
`ctx:<n>` (but see defect 2). 9: `collectBridges` throws at `Position.lean:288`. 10:
`describeProof` reconciles `close` and `steps`.

**All RESULT.md checks reproduce.** `lake build ExplicitLean.SimpTrace` with oleans deleted:
clean, 8.1 s. `test/SimpTrace/Fixtures.lean`: pass, 3.3 s. `python3 -B
Experiment/check_simp_trace.py`: `OK: 26 ... and out-of-root paths are refused`, 3.1 s.
`IsEmptyBasicTraced.lean`: pass, 2.6 s. Measurement reproduces exactly: 17 calls, 76 steps,
`rw` 70 / `unfold` 6, mean 886.4 B, max 1132 B, total 15 068 B. Both checker assertions were
re-verified to fail on a regression (perturbed `pos`; an injected `close: unknown`).

**Substitutability (18 theorems, each compiled under `simp` and `simp_trace`)** — no defects.
Forms exercised: bare `simp`; `simp only [..] at h ⊢`; `simp [*, foo] at *`; `(config := ...)`;
`+contextual +decide`; `-failIfUnchanged`; `(disch := assumption) [foo]`; `(discharger :=
omega) [foo]`; `simp only [foo] at h₁ h₂`; `[← h]`; `only [h, ↓reduceIte]`; `[(h)]`; `only
[..] at this`; `[-Nat.add_zero]`; `only []`; `+zetaDelta +instances`; `only [← h] at h2`.
Every form that parses for `simp` parses for `simp_trace`, and final goals agree — checked
with `guard_hyp`/`guard_target` on the `at`-forms, not by eye. The trailing `with_trace` is
also unambiguous after `<;>`, `;`, `·`, `at h ⊢`, `at *`, inside `first | ... | ...` and
`try`.

**Trace validity (10 traces)** — no defects. Positions were re-derived with a navigator
written from scratch in a scratch file (`nav` over `app`/`lam`/`forallE`/`letE`/`mdata`/
`proj`), not with `Position.lean`. Verified: `s02`/`c5`/`c6` (`at h ⊢`, `at *`), `s07`
(conditional lemma, side sub-trace `assumption:h1`), `s11` (multiple identical `n`
occurrences under an `ite`, plus an `eq` step `source:reduceIte`/`by:rfl`), `s17` (`zeta`
over a `letE`), `s18` (`←` at two positions), `s05` (`+contextual`, nested implications:
`[1,0,0,1]`→`p`, `[1,0]`→`p ∧ q`, `[1,1]`→`q`, `[1]`, `[]` — all five confirmed against
independently constructed `Expr`s), `d7` (`absurd:h` close), `zeta`/`shadowed` fixtures.
`ctxIndex` values are the real `LocalDecl.index`; contextual refs correctly use the separate
`{contextual:true}` namespace. `true_intro` and `absurd:<hyp>` closes are correct.

---

## 1. CRITICAL — a 2-deep chain of reducible definitions aborts on a goal stock `simp` proves

`ExplicitLean/SimpTrace/Position.lean:341-365`, via `findBridge?` (`Position.lean:250-271`)
and `collectBridges` (`Position.lean:285-296`). `findBridge?` accepts the *first* position
whose single reduction makes `target` appear, and `collectBridges` stops as soon as
`findOccurrences` is non-empty. When two delta-unfoldings must be composed at the *same*
position before the recorded subterm appears, neither the single-reduction probe nor the
iteration reaches it, and the run aborts. This is the same class REVIEW-1 defects 3 and 4
covered; the round-1 fix (rejecting no-op refreshed matches, plus a `zeta` case) does not
cover composed delta steps.

Input (`/private/tmp/t1r2/CH2.lean`):
```
@[reducible] def g1 (n : Nat) := n
@[reducible] def g2 (n : Nat) := g1 n
example (n : Nat) : g2 n + 0 = n := by simp [g2, g1]        -- succeeds
example (n : Nat) : g2 n + 0 = n := by simp_trace [g2, g1]  -- fails
```
Observed: `error: simp_trace: cannot locate recorded subterm in running term` /
`before: n + 0` / `after: n` / `running: g2 n + 0 = n`.
Expected: the goal closes, as stock `simp` does, with two `unfold` steps recorded.
Repro:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r2/CH2.lean      # stock simp: exit 0, no output
lake env lean /private/tmp/t1r2/CHAIN.lean    # simp_trace: errors at depth 2 and 3
```
Depth 1 traces correctly (one `unfold` step); depth 2, 3 and 4 all abort. Since Mathlib
routinely stacks `@[reducible]`/`abbrev` definitions, this blocks the stated goal of tracing
real modules. RESULT.md's "Goal state matches stock simp ... verified by compiling identical
goals under both" is therefore still not true in general.

Fix direction: let `findBridge?` return *all* candidate reductions rather than the first, and
let `collectBridges` keep reducing at a position that made progress toward `target` instead of
stopping at the first non-empty `findOccurrences`.

## 2. MAJOR — an inaccessible hypothesis is recorded under a name that denotes a different local

`ExplicitLean/SimpTrace/Tactic.lean:194-202`. `originName` computes
`display := n.eraseMacroScopes.toString` and stores it in both `name` and `local.userName`.
For an inaccessible hypothesis `a✝`, `eraseMacroScopes` strips the hygienic scope and yields
exactly `a` — which is the name of a *different, accessible* local in the same context. The
`inaccessible: true` flag says the name is not usable, but the name shipped is not the `a✝`
form the spec's `rename_i` recipe needs; it is a name that resolves, silently, to the wrong
hypothesis.

Input (`/private/tmp/t1r2/N2.lean`):
```
example (a b : Nat) : a = b → a + 0 = b := by
  intro _
  simp_trace [*]
```
Context is `a b : ℕ`, `a✝ : a = b`. Observed first step:
`{"kind":"rw","name":"a","dir":"fwd","local":{"userName":"a","inaccessible":true,"ctxIndex":3},...}`
with `before: "a"`, `after: "b"` — i.e. the trace claims the rewrite used `a : ℕ`.
Expected: `a✝` (or the hygienic name), so a generator can bind it with `rename_i` and cannot
confuse it with the accessible `a`.
Repro: `lake env lean /private/tmp/t1r2/N2.lean` — the `trace_state` in that file prints the
context alongside the trace.

The same wrong name appears in the committed fixture
`test/SimpTrace/expected/inaccessible.json`, so the checker endorses it. RESULT.md line 44
("`ctx:<n>` labels replaced by the spec's `local` object") is accurate, but the code comment at
`Tactic.lean:196` ("e.g. `a✝` rather than the hygienic form") describes behaviour the code does
not have — `eraseMacroScopes` removes the `✝` marker too. `ctxIndex` is correct and
disambiguates, so a replayer that ignores `userName` is safe; one that reads `name`, as T2's
syntax requires, is not.

## 3. MAJOR — a symlink under the package root defeats the containment check

`ExplicitLean/SimpTrace/Tactic.lean:268-312`. `normalizeComponents` collapses `.`/`..`
textually and `isInside` compares component prefixes; neither resolves symlinks. A symlink
anywhere under the package root is therefore a write primitive to any path on the machine.
REVIEW-1 defect 6 asked that the tactic not be able to write outside the repository; the
textual fix closes `..` and absolute paths but not this.

Input (`/private/tmp/t1r2/OUT4.lean`):
```
ln -s /private/tmp test/SimpTrace/linkescape
example (a : Nat) : a + 0 = a := by
  simp_trace with_trace "test/SimpTrace/linkescape/SYMLINK_ESCAPE.json"
```
Observed: no error; `/private/tmp/SYMLINK_ESCAPE.json` created (410 bytes).
Expected: refused, as for `..` and absolute paths.
Repro:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
rm -f /private/tmp/SYMLINK_ESCAPE.json
ln -s /private/tmp test/SimpTrace/linkescape
lake env lean /private/tmp/t1r2/OUT4.lean
ls -la /private/tmp/SYMLINK_ESCAPE.json   # exists
rm -f test/SimpTrace/linkescape /private/tmp/SYMLINK_ESCAPE.json
```
Fix: resolve the parent directory with `IO.FS.realPath` (after `createDirAll`) and test
containment on the resolved path, resolving the roots the same way.

## 4. MAJOR — `close: {"by":"unknown"}` is emitted silently, contradicting RESULT.md

`ExplicitLean/SimpTrace/Recorder.lean:239`. When a discharger closes a side condition with a
proof that is neither a bare fvar nor an `of_eq_true`/`eq_true_of_decide`/`trivial`/`True.intro`
application, `describeProof` returns `"unknown"`, which is written into the trace. `"unknown"`
is not one of the spec's close forms (`SIMP-TRACE-SPEC.md:12`), T2 has no replay for it, and
nothing throws or logs — the one `unknownEq` counter at `Tactic.lean:463-465` covers `eq`
steps only, not closes.

Input (`/private/tmp/t1r2/UNK2.lean`):
```
example (m n k : Nat) (h1 : n ≤ k) (h2 : k ≤ m) : m - n + n = m := by
  simp_trace (disch := omega) [Nat.sub_add_cancel]
```
Observed: `"side":[{"goal":"n ≤ m","steps":[],"close":{"by":"unknown"}}]`, compile exits 0.
Expected: either a real close form, or the hard error RESULT.md promises.
Repro: `lake env lean /private/tmp/t1r2/UNK2.lean`

This contradicts RESULT.md line 32-33 ("unattributable firings, unlocatable subterms,
bridge-bound exhaustion and unnameable closes each raise distinct errors") and line 44-45 ("an
unnameable close is an error rather than a guessed `rfl`"). Only the *goal/hypothesis* close
path (`Tactic.lean:344-355`) throws; the *side* close path does not. Note the single-hypothesis
form of the same call yields `assumption:h`, so no fixture reaches this branch and
`check_simp_trace.py` — which does reject `"unknown"` (verified by injection) — never sees it.

## 5. MINOR — importing `ExplicitLean.SimpTrace` reserves `with_trace` as a global token

`ExplicitLean/SimpTrace/Tactic.lean:47`, `syntax simpTraceOut := " with_trace " str`. The
atom becomes a reserved keyword for every file that imports the module, so an identifier
named `with_trace` can no longer be bound anywhere in such a file — including in code that
uses plain `simp`, not `simp_trace`.

Input (`/private/tmp/t1r2/TOK.lean`):
```
import ExplicitLean.SimpTrace
example (a b : Nat) (with_trace : a + 0 = b) : a = b := by
  simp at with_trace
  exact with_trace
```
Observed: `error: unexpected token 'with_trace'; expected '_' or identifier`.
Without the import the same file compiles (`/private/tmp/t1r2/TOK2.lean`).
Repro: `lake env lean /private/tmp/t1r2/TOK.lean` then `lake env lean /private/tmp/t1r2/TOK2.lean`

Impact is currently nil — `grep -rn "with_trace" .lake/packages/mathlib/Mathlib` returns
nothing — so this is recorded as a hazard of the delimiter choice, not a blocker. RESULT.md
lines 6-9 argue the trailing keyword is "unambiguous everywhere"; that is true of parsing and
untrue of the identifier namespace.

## 6. MINOR — RESULT.md overstates two claims

- Line 10-12, "Goal state matches stock simp ... verified by compiling identical goals under
  both": contradicted by defect 1, where `simp_trace` hard-errors on a goal stock `simp`
  proves. The 18-theorem corpus in this review found no *other* divergence, so the claim needs
  narrowing, not deleting.
- Line 31-33, "Nothing is dropped silently: ... unnameable closes ... raise distinct errors":
  contradicted by defect 4 for side-condition closes.

Everything else in RESULT.md — every timing, count, kind tally and byte figure — reproduced
exactly. The 69-line length is permitted and is not reported as a defect.

---

## Integration cross-check with T2 (read-only)

Three `IsEmpty` traces were hand-translated from
`test/SimpTrace/isempty_out/` to `explicit_rw` syntax per
`/Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw/ExplicitLean/ExplicitRw/Tactic.lean`
and run inside the T2 worktree.

**T1's traces are correct and replay exactly.** `call01` (`isEmpty_Prop`), `call02`
(`isEmpty_pi`) and `call03` (`isEmpty_sigma`) all replay with the recorded positions,
directions and lemma names, closing with `then rfl`, no goal left over
(`/private/tmp/t1r2/M4.lean`, exit 0, no output). This confirms the position convention
(including binder-crossing positions `[1,1]` and `[1,1,1]` under `∀`/`∃`), the `dir: rev`
encoding of `←`, and the `true_intro` close all agree with T2's reader. No position-convention
mismatch, no missing kind and no missing args were found for these traces.

**One defect, on the T2 side.** The same replay passes or fails depending only on an
*unrelated import*, so it is not a property of the trace:

```
# /private/tmp/t1r2/M2.lean — WITH `import Mathlib.Algebra.Order.Group.Nat`: passes
# /private/tmp/t1r2/M3.lean — WITHOUT it, otherwise byte-identical: fails
example {p : Prop} : (¬Nonempty p ∧ True) ↔ (IsEmpty p ∧ True) := by
  explicit_rw [not_nonempty_iff at [0, 1, 0, 1]] then rfl
```
Failure: `explicit_rw: step 1: lemma `not_nonempty_iff` does not prove an equation or an iff;
its type is ?m.2`. Repro:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t1r2/M2.lean   # exit 0
lake env lean /private/tmp/t1r2/M3.lean   # the ?m.2 error
```
Reason: `elabEquation` (`T2 .../ExplicitRw/Tactic.lean`, the `Term.elabTerm stx none` /
`forallMetaTelescopeReducing` path) leaves the universe metavariable of a `Sort*`-polymorphic
lemma unresolved, and `asEquation` then sees a bare `?m` instead of an `Iff`. Writing the
universe explicitly does not help (`← @not_nonempty_iff.{0} p` fails the same way in the
failing import context), and ordinary `Eq`/`Iff` lemmas whose universes are pinned by their
arguments (`Nat.add_zero a`, `and_true p`) always succeed. Because `not_nonempty_iff` is the
first step of 15 of the 17 `IsEmpty` traces, T2 cannot replay most of that module in its own
import context.

**Reported to: T2.** T1 needs no change for this. Suggested fix for T2: elaborate the step
term with the expected type derived from the subterm at the position, or force pending
universe/synthetic metavariables (`Term.synthesizeSyntheticMVars`, then
`instantiateMVars`) before `asEquation`.

---

**Totals: 1 critical, 3 major, 2 minor (T1); 1 major (T2, reported above).**

Scratch files used by the repro commands are under `/private/tmp/t1r2/` and are not committed.
