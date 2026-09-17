# T1-trace-capture: adversarial review, round 1

Scope check passed: `git diff --stat $(git merge-base codex/search-free-mathlib-2026-08-31
task/T1-trace-capture) task/T1-trace-capture` lists 24 files, all inside
`ExplicitLean/SimpTrace.lean`, `ExplicitLean/SimpTrace/`, `test/SimpTrace/`,
`Experiment/check_simp_trace.py`, `tracking/tasks/T1-trace-capture/`.

All RESULT.md checks reproduce: build clean; 14 fixtures pass; `check_simp_trace.py`
prints `OK: 14`; `IsEmptyBasicTraced.lean` passes; the measurement is exactly 17 calls,
76 steps (70 `rw`, 6 `unfold`), mean 881 B, max 1127 B, 14 983 B total. The checker
does fail on a perturbed expected file (both a `pos` and a `dir` reported, exit 1).
Side sub-traces are positioned against the side goal, not the main goal (verified on
`conditional.json`). Dependent hypotheses (`at h` with `h' : h = h`), hypothesis
ordering after `at h`, `at *`, `at h ⊢`, `simp [*]`, `simp only [] at h`, `simp [h] at h`,
`failIfUnchanged`, hypotheses rewritten to `False`/`True`, metavariable goals, two
instantiations of one lemma, and duplicate/binder-crossing occurrences all match stock
`simp` or are recorded correctly. The defects below are what broke.

---

## 1. CRITICAL — every parenthesized simp argument form is a parse error

`ExplicitLean/SimpTrace/Tactic.lean:38`. The syntax puts the optional
`(" (" &"out" " := " str ")")?` clause before `optConfig`. Once the parser commits to
an open paren it demands the `out` keyword, so `simp`'s own parenthesized forms cannot
be written at all. `simp_trace` is therefore not substitutable for `simp` in a Mathlib
file, which is requirement (1).

Input (`scratch/A6.lean`): `example : (2:Nat) + 2 = 4 := by simp_trace (config := { decide := true })`
Observed: `error: unexpected identifier; expected 'out'` at the `config` token.
Expected: elaborates exactly as `simp (config := { decide := true })`, which succeeds.
Same failure for `(discharger := assumption)` and `(disch := assumption)`.
Repro: `cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture && lake env lean tracking/tasks/T1-trace-capture/scratch/A6.lean`

Note this also means RESULT.md's claim that the slots "are positionally identical to
`Parser.Tactic.simp`" is only true for the forms that parse; `optConfig` at `stx[2]` is
unreachable for any parenthesized config.

Fix: make the `out` clause unambiguous — e.g. require it to lead with its own token
(`simp_trace (out := "p") ...` parsed via a distinct `&"out"`-anchored atom that does
not compete with `optConfig`), or move it after the location.

## 2. CRITICAL — `+decide` (and `Simp.Config.decide`) aborts with "unattributed simp step"

`ExplicitLean/SimpTrace/Recorder.lean:112-124` and `Tactic.lean:124`. When
`config.decide` is on, simp closes a goal by decidability without registering anything
in `usedTheorems`, and `before != after`, so `classify` returns `.unattributed`;
`reattribute?` finds no theorem, and `toStep` throws. Stock `simp +decide` succeeds.

Input (`scratch/A7.lean`):
```
example : (2:Nat) + 2 = 4 := by simp +decide        -- succeeds
example : (2:Nat) + 2 = 4 := by simp_trace +decide  -- fails
```
Observed: `error: simp_trace: unattributed simp step (no recordable kind)` /
`before: 2 + 2 = 4` / `after:  True`.
Expected: same goal state as stock simp, with the firing recorded as an `eq` step with
`by: "decide"` (the spec already provides that kind).
Repro: `lake env lean tracking/tasks/T1-trace-capture/scratch/A7.lean`

Fix: in `classify`/`toStep`, treat an unattributed Prop-to-`True`/`False` change as a
`.proc none` firing so it goes through `mkEqStep` and `scratchCheckEq`, which already
returns `"decide"` for this case.

## 3. CRITICAL — shadowed nested binders: position solving fails on goals stock simp proves

`ExplicitLean/SimpTrace/Position.lean:137-148, 296-369`. `abstractSimpFVars` abstracts
simp-introduced fvars by declaration order against the *number of binders crossed*.
With two binders of the same user name, the running term and the recorded subterm
diverge and no occurrence is found, so the run aborts.

Input (`scratch/P1.lean`):
```
example (f : Nat → Nat → Nat) :
    (fun x => (fun x => f x (x + 0)) (x + 0)) = (fun x => f x x) := by
  simp_trace
```
Observed: `error: simp_trace: cannot locate recorded subterm in running term` /
`before: (fun x => f x x) = fun x => f x x` / `running: (fun x => (fun x => f x (x + 0)) x) = fun x => f x x`.
Expected: the goal is closed, as stock `simp` does (verified in `scratch/P3.lean`, exit 0).
Repro: `lake env lean tracking/tasks/T1-trace-capture/scratch/P1.lean` then
`lake env lean tracking/tasks/T1-trace-capture/scratch/P3.lean`

The running term shows the beta-redex was only partly bridged: `findBridge?` reduced the
outer argument but the inner `x + 0` under the shadowed binder was never located.

## 4. CRITICAL — `let` expressions: position solving fails on goals stock simp proves

Same code path. Zeta reduction happens in `reduceStep`, and `findBridge?`
(`Position.lean:227-240`) has no zeta case: `reduceHere?` handles beta, `proj` and delta
only, so a `letE` that simp zeta-reduced can never be bridged.

Input (`scratch/P2.lean`): `example (a : Nat) : (let y := a + 0; y + 0) = a := by simp_trace`
Observed: `error: simp_trace: cannot locate recorded subterm in running term` /
`before: a = a` / `running: (let y := a; y + 0) = a`.
Expected: goal closed, as stock `simp` does (`scratch/P3.lean`, exit 0).
Repro: `lake env lean tracking/tasks/T1-trace-capture/scratch/P2.lean`

Fix: add a zeta case to `reduceHere?` (`letE` → instantiate the body), and emit it as a
step kind the spec covers (`change`, since v1 has no `zeta`).

## 5. MAJOR — recorder changes simp's caching behaviour (`wellBehavedDischarge := false`)

`ExplicitLean/SimpTrace/Recorder.lean:248-249` hardcodes
`Simp.mkMethods simprocs (instrumentDischarge ref d) (wellBehavedDischarge := false)`.
Stock simp uses `true` when no custom discharger is given
(`Lean/Meta/Tactic/Simp/Rewrite.lean:655`, `mkDefaultMethods`) and `false` only for a
user discharger (`Main.lean:1089`). At `Main.lean:261-266` a `false` value forces
`withFreshCache do f` on every implication descent instead of reusing the cache.

So the default-discharger path runs simp with a materially different cache policy than
the call it is meant to mirror. This is not merely slower: resetting the cache under
binders changes which subterms simp revisits, so a recorded trace can diverge from what
the original `simp` call did, and the "runs stock simp" claim in RESULT.md and in
`Tactic.lean:4` is not accurate for this parameter.

Repro (reading): `sed -n '255,266p' <lean-src>/Lean/Meta/Tactic/Simp/Main.lean` and
`sed -n '645,656p' <lean-src>/Lean/Meta/Tactic/Simp/Rewrite.lean`.

Fix: thread the real value — `wellBehavedDischarge := discharge?.isNone`.

## 6. MAJOR — `out :=` writes anywhere on the filesystem

`ExplicitLean/SimpTrace/Tactic.lean:358-360`: `IO.FS.writeFile path json` with no
normalisation or containment check, and `outPath?` returns the string literal verbatim.

Input (`scratch/OUT.lean`):
`example (a : Nat) : a + 0 = a := by simp_trace (out := "/private/tmp/ESCAPED_OUTSIDE_REPO.json")`
Observed: `/private/tmp/ESCAPED_OUTSIDE_REPO.json` created (439 bytes).
Expected: a path outside the repository root is rejected with an error.
Repro: `rm -f /private/tmp/ESCAPED_OUTSIDE_REPO.json && lake env lean tracking/tasks/T1-trace-capture/scratch/OUT.lean && ls -la /private/tmp/ESCAPED_OUTSIDE_REPO.json`

A relative `../..` path reaches the same place. The task explicitly asked that out-file
handling not write outside the repo.

## 7. MAJOR — `close: {"by":"assumption:False"}` is not a spec value and names no hypothesis

`ExplicitLean/SimpTrace/Tactic.lean:258`. When a hypothesis simplifies to `False` the
location is recorded as `close: {"by": "assumption:False"}`. The spec
(`SIMP-TRACE-SPEC.md:12`) defines `assumption:<name>` as a hypothesis name; `False` is
not a hypothesis, and replay running `exact False` (or `assumption` looking for a local
called `False`) cannot work. The actual proof built at `Tactic.lean:310` is
`mkFalseElim ... (mkFVar fvarId)`, i.e. elimination of the *named* hypothesis.

Input (`scratch/CL.lean`): `example (a : Nat) (h : a ≠ a) : False := by simp_trace at h`
Observed: `"close": {"by": "assumption:False"}`.
Expected: `assumption:h`, or a distinct documented value for false-elimination.
Repro: `lake env lean tracking/tasks/T1-trace-capture/scratch/CL.lean && python3 -m json.tool tracking/tasks/T1-trace-capture/scratch/false_hyp.json | grep -A3 close`

Also at `Tactic.lean:255-260` the whole `close` is inferred from the shape of
`result.expr` rather than from what actually discharged the location, so `rfl` is
emitted as a fallback for any closed location that is neither `True` nor `False` without
ever checking that `rfl` proves it. Contrast `scratchCheckEq` (`Tactic.lean:77`), which
does verify its answer before recording it.

## 8. MAJOR — inaccessible hypotheses are recorded as `ctx:<index>`, which is unreplayable and collides

`ExplicitLean/SimpTrace/Tactic.lean:169-176`. Any local whose user name is inaccessible
or has macro scopes is named `ctx:{d.index}`. That branch was written for `+contextual`
antecedents, but it also catches ordinary inaccessible hypotheses, which are *not*
introduced by any `intro_ctx` step (RESULT.md states `intro_ctx` is not emitted in v1).
Replay has nothing to bind `ctx:3` to, and a genuine contextual hypothesis in the same
trace can receive the same label.

Input (`scratch/N1.lean`):
```
example (a b : Nat) : a = b → a + 0 = b := by
  intro _
  simp_trace [*]
```
Observed first step: `{"kind":"rw","name":"ctx:3","dir":"fwd","pos":[0,1,0,1]}`.
Expected: something replay can resolve — the fvar's user name plus a disambiguating
index, e.g. `{"name":"a✝","fvar_index":3}`, or an emitted `intro_ctx` step that binds
the label before it is used.
Repro: `lake env lean tracking/tasks/T1-trace-capture/scratch/N1.lean`

This is the defect item 7 of the attack list predicted; the proposed fix is to record
`d.userName` (including the `✝` form) alongside `d.index`, and to reserve `ctx:` strictly
for labels that a preceding `intro_ctx` step introduces.

## 9. MINOR — the 32-reduction bound does not fail loudly

`ExplicitLean/SimpTrace/Position.lean:281-284`: the docstring says the bound exists "so a
non-converging search fails loudly rather than hanging", but exhausting fuel does
`if fuel == 0 then return #[]` — a silent empty result. The caller
(`Position.lean:344-353`) then reports `cannot locate recorded subterm`, which
misattributes a bound exhaustion to a missing subterm and sends a fixer down the wrong
path. RESULT.md repeats the claim: "`findBridge?` is bounded at 32 reductions and fails
loudly rather than looping."

Expected: throw a distinct error naming the bound.

## 10. MINOR — side-trace `close` contradicts its own recorded steps

`ExplicitLean/SimpTrace/Recorder.lean:201-217`. `describeProof` reads the proof term,
while `steps` come from the recorder, and the two can describe different discharges. In
the committed `conditional.json` fixture the side trace carries a step rewriting
`n ≤ m` to `True` by hypothesis `h`, yet `close` is `assumption:h`. Replaying the steps
and then the `close` would discharge it twice; replaying only `close` makes the recorded
step dead. The spec does not say which wins.

Repro: `python3 -m json.tool test/SimpTrace/out/conditional.json`

Fix: make `close` and `steps` consistent — either record `close: null` when steps
already reduce the side goal to `True`, or drop the steps when the proof is a bare fvar.

## 11. MINOR — RESULT.md accuracy

Two claims are not reproducible as written:

- "Goal state matches stock simp ... verified by compiling identical goals under both"
  is contradicted by defects 1-4, where `simp_trace` cannot be written at all or hard-errors
  on goals stock `simp` proves.
- "`findBridge?` is bounded at 32 reductions and fails loudly" — see defect 9.

The "runs **stock simp**" framing is also qualified by defect 5. Everything else in
RESULT.md, including all timings, counts and the measurement, reproduced.

---

**Totals: 4 critical, 4 major, 3 minor.**

Scratch files used by the repro commands are under
`tracking/tasks/T1-trace-capture/scratch/` and are not committed.
