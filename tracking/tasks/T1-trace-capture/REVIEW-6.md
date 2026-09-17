# T1-trace-capture: adversarial review, round 6 (T1b forked traversal)

Scratch for this round is `/private/tmp/t1r6/`, not committed. Working tree clean before and
after; `git status --porcelain` empty. All Lean compiles run serially.

**All eight REVIEW-5 items reproduce as fixed or classified, with one exception.** Item 1 is
fixed only for ASCII hypothesis names — see defect 1. Item 2 is genuinely fixed: the real
Mathlib `existsAndEq` goal now emits an `eq` step with `by: "unresolved:simproc:…"` and one
classified line, not `rw [propext]` (`lake env lean /private/tmp/t1r6/G04c.lean`); the inner
lemma *is* recovered for the positive `propext (L …)` shape (`propext_lemma.json` names
`fixtureTag_iff`). Item 3 is fixed — the matcher `eq` trace exits 0. Item 4 is fixed and
observable: `withInDSimp` is entered at `Traversal.lean:630` and the `dreduce_ite` fixture
traces with goal state identical to stock (`h : True` under both). Item 5's table is now
generated. Items 7 and 8 are fixed (`procDepth` gone; `simp?` stated as an exclusion).

**The implementer's two flagged points.** (a) `simp [← h]` on a local **does** keep
`dir: "rev"` and carry `local`, and a fixture now pins it — `local_named_rev.json` asserts
both, and the checker catches the removal of `local` when the expected file has it (verified
by injecting the regression into `check_trace` directly). (b) The `dreduce_ite` fixture traces
and matches stock; I could not make the `instrumentD`/`logDStep` guard drop a step — a
dsimproc that fires unattributably (`/private/tmp/t1r6/DS.lean`) and one that runs a nested
`simp` first (`DS2.lean`) are both recorded, because `dsimproc_decl` always registers an origin
and `eventCount` reads the outer frame while the nested events go to a diverted one. But the
step it records is the **wrong kind** — defect 4.

---

## 1. CRITICAL — `simp [h]` loses `local` and `prop` for any non-ASCII hypothesis name

`ExplicitLean/SimpTrace/Recorder.lean:107-109` (`resolveStxOrigin`'s character whitelist).

REVIEW-5 defect 1 is fixed only for names the hand-rolled whitelist accepts:
`isAlphanum || '_' || '\'' || '!' || '?' || '₀' || '₁' || '₂'`. Every other identifier
character makes `resolveStxOrigin` `return o` unresolved, so the step carries **neither `local`
nor `prop`** — the exact failure REVIEW-5 raised, on names Mathlib uses constantly: Greek
(`hα`, `hε`), subscripts from `₃` up (`h₃`, `h₁₀`), and `«…»`-quoted names. `simp [*]` on the
identical rewrite records both, so the two forms still disagree.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r6 lake env lean /private/tmp/t1r6/Charset2.lean
```
Observed, same goal `p ∧ True` with `hα : p`:
```
simp_trace [hα]  ->  prop=None   local=None
simp_trace [*]   ->  prop='true' local={'userName':'hα','inaccessible':False,'ctxIndex':2}
```
and for `h₃ : a = b` on `a + 0 = b`: `[h₃]` → `local=None`, `[*]` → `local={…'ctxIndex':3}`.
A generator handed the `[hα]` trace elaborates `hα : p`, finds neither an `Eq` nor an `Iff`,
and fails — REVIEW-3's M5 again. The whitelist should not exist: the `Origin.stx` ref is a
`Syntax` and `ref.isIdent`/`getId` (after stripping a leading `←`) gives the name directly,
with no character test.

## 2. CRITICAL — an explicit class-typed argument is accepted but never recorded, so the step is unreplayable

`ExplicitLean/SimpTrace/Recorder.lean:224` (`classifyProof`'s `isClass?` arm), with
`Recorder.lean:274` (the emitted `rw` passes `#[]` for `args`).

`classifyProof` accepts an *explicit* argument whose type is a class ("or an instance"), but
`emitProcStep` records only `proofArgs` as `side`; the instance argument is dropped entirely
and `args` is always `#[]`. When more than one instance of that class exists, replay
synthesises a **different** one than simp used, or fails outright. The recorder reports
success — exit 0, no `unresolved` line — so nothing flags it.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r6 lake env lean /private/tmp/t1r6/CP5.lean   # exit 0
lake env lean /private/tmp/t1r6/CP5r.lean                                        # the replay
```
`CP5.lean` has `tagE_lem (w : Widget Nat) (n : Nat) : TagE n = True` and two instances
`instW1`/`instW2`; the simproc passes `instW2`. The recorded step is
```
{"kind":"rw","pos":[],"name":"CP5.tagE_lem","dir":"fwd","source":"CP5.tagEProc"}
```
with no `args`. Replaying it verbatim:
```
error: unsolved goals
case w
k : Nat
⊢ Widget Nat
```
The spec's own wording for this arm is "an instance argument (`instImplicit`, or a class-typed
argument)" — an `instImplicit` is safe because unification supplies it, but an *explicit*
class-typed argument is not. Either record it in `args` (the spec has the field, and nothing
currently ever emits it) or reject it, as the fourth arm already rejects a non-subterm.

## 3. MAJOR — `isPlumbingHead` is an incomplete allowlist: `Iff.symm` and `Iff.trans` are recorded as rewriting lemmas

`ExplicitLean/SimpTrace/Recorder.lean:186-190` (`isPlumbingHead`).

REVIEW-5 defect 2 was fixed by adding `propext` to a list of plumbing heads. The list still
omits `Iff.symm`, `Iff.trans`, `Iff.rfl`, `Eq.mpr'`, `Eq.substr`, `Iff.of_eq`, `trans` — and
the fix that unwraps one `propext` level hands the inner head straight to the generic walk, so
those now get *more* exposure than before, not less. `Iff.symm h` and `Iff.trans h₁ h₂` each
have only explicit proof arguments, so both classify as `.lemmaApp`, and the recorder emits
`rw [Iff.symm]` / `rw [Iff.trans]` — steps no replayer can execute — plus one bogus
`unresolved:condition proof not a hypothesis or a recorded discharge` side per proof argument.
This is the identical shape and identical consequence as REVIEW-5 2.

```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r6 lake env lean /private/tmp/t1r6/CP.lean    # Iff.symm
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r6 lake env lean /private/tmp/t1r6/CP3.lean   # Iff.trans
```
```
error: simp_trace unresolved: simproc:CP.tagAProc side condition
`True ↔ TagA k` proved by a term no close form describes
```
with the step `{"kind":"rw","name":"Iff.symm","dir":"fwd","source":"CP.tagAProc", …}`.
No stock or Mathlib simproc reaches this today (`grep` over
`Lean/Meta/Tactic/Simp/BuiltinSimprocs/` and Mathlib finds no `propext (Iff.symm …)`), so it is
latent rather than an observed break — but an allowlist that must be complete to be correct is
the wrong shape. Invert it: require the head to be an `Eq`/`Iff`-*concluding* lemma whose
explicit arguments are all accounted for, rather than enumerating the plumbing.

Related, and the same root cause, but only a missed opportunity: `Eq.symm (propext (L …))`
(`/private/tmp/t1r6/CP2.lean`, `tagBProc`) correctly falls to `.computed` and a classified
`unresolved:simproc:CP2.tagBProc`, so nothing is misrecorded — but the rewriting lemma
`tagB_iff` and the direction are both recoverable and both thrown away. Only `propext` is
unwrapped; `Eq.symm` and a `propext` under it are not.

## 4. MAJOR — a dsimproc firing is recorded as a propositional `eq`, not a definitional kind

`ExplicitLean/SimpTrace/Recorder.lean:459` (and the `rw` arms at :461-464).

`instrumentD` wraps `dpre`/`dpost` — the **definitional** layer — yet it emits `.eq` (the
spec's "simproc-computed equation … replay proves it with the named ordinary tactic") for any
attributable dsimproc, and `.rw` (a propositional rewrite) for a non-`decl` origin. A dsimproc
change is definitional by construction; the spec's `unfold`/`beta`/`zeta`/`iota`/`change`
kinds are what describe it, and `logDStep`'s `classifyDefChange` already does exactly that
classification for the unattributable case. The two paths disagree about the same layer.

This is not cosmetic. The committed `dreduce_ite` fixture records the `dreduceIte` firing as
`{"kind":"eq","pos":[0,1],"by":"rfl","source":"dreduceIte"}`, and position `[0,1]` is the
**domain of a dependent `∀`**. Replayed in T2 at its committed tip `16a2214`:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t1r6/T2rep.lean
error: explicit_rw: step 1: position [0] rewrites the domain of a dependent `∀`, whose body
mentions the bound variable; rebuilding that needs a cast of the body along the domain
equality, which `explicit_rw` does not build. Only definitional steps are supported there.
```
The same step written definitionally replays and closes the goal (`T2repB.lean`, exit 0). See
**Integration** for the attribution: the obstruction is T2-side in the sense that plain `rw`
manages it, but T1 is recording a definitional reduction in the one kind that forces a
propositional rewrite, and it is T1 that chooses the kind.

## 5. MAJOR — a side-condition close names an inaccessible hypothesis by its erased name

`ExplicitLean/SimpTrace/Recorder.lean:289` and `:488`
(`assumptionName?` / `describeProof`, both `s!"assumption:{n.eraseMacroScopes}"`).

REVIEW-2's hazard — `eraseMacroScopes` turning `a✝` into plain `a`, which in the same context
usually denotes a *different*, accessible local — was closed on `originName` (Tactic.lean:152-154
takes the display form and never erases) and on `intros`. It is still open on `close.by`.

The committed `user_congr_ite.json` proves it. Its `ite_congr` step's second side trace carries
`"intros": ["a✝"]` and, nested inside, a side whose close is `{"by": "assumption:a"}` — while
the fixture's own context (`Fixtures.lean:248-251`) has an ordinary `a : Nat`. A generator that
emits `exact a` picks the `Nat`.
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
python3 -c "import json;d=json.load(open('test/SimpTrace/out/user_congr_ite.json'));\
print(d['locations'][0]['steps'][0]['side'][1])"
```
```
'intros': ['a✝'], … 'side': [{'goal': 'q', 'steps': [], 'close': {'by': 'assumption:a'}}]
```
`intros` is a display name and `close.by` is an erased one, for the *same* hypothesis, in the
*same* step. Whatever the answer is, the two must agree; the display form is the one the rest
of the recorder already chose. (`/private/tmp/t1r6/AssumeA2.lean` also shows `intro a✝` is not
even parseable, so a generator must go through `rename_i` — which is what the spec says for
`local` and says nothing about for `close`.)

## 6. MINOR — a `zetaDelta` unfold is recorded as a nameless `zeta`, which the spec does not describe

`ExplicitLean/SimpTrace/Traversal.lean:585` (`dsimpReduceT`) and `:1355`.

The spec's `zeta` kind is "`let x := v; b` to `b[v/x]`" — a `letE` node. What
`reduceFVar'` performs is `zetaDelta`: an **fvar** replaced by its `let`-bound value. The
recorder emits `.defeq pos .zeta none` — no `name`, no `local` — so a replayer sees `zeta` at a
position whose subterm is an fvar and has nothing saying *which* local was unfolded. Note that
stock `reduceFVar'` itself calls `recordSimpTheorem (.fvar …)` at `Traversal.lean:349`, so the
identity is in hand and is dropped. The committed `zeta_delta_at_hyp.json` shows it
(`{"kind":"zeta","pos":[1,0],"before":"g","after":"fun s => s + 0"}`), as does
`/private/tmp/t1r6/out/L12.json` for `simp [y]` on a `let`-bound `y`. Either a `zetaDelta`
kind, or `zeta` carrying `name`/`local` — a spec question either way.

## 7. MINOR — three expected skeletons omit `local` where the trace carries it, so they pin nothing

`test/SimpTrace/expected/{reverse,chained,local_eq}.json`, with
`Experiment/check_simp_trace.py:93`.

The checker's "unexpected field" test covers only `("name","dir","source","prop")`; `local` and
`arg` are absent from it. So an expected file that omits `local` accepts a trace that has it —
and, symmetrically, would accept a trace that lost it. `reverse.json` is
`simp_trace [← h]` on a local hypothesis, the *same shape* as `local_named_rev.json`, and its
expected file has no `local`; the actual trace does. Verified against the checker's own
`check_trace` (`/private/tmp/t1r6/`): removing `local` from the trace is caught when expected
has it, and passes silently when expected does not. Refresh the three files, and add `local`
to the line-93 tuple.

## 8. MINOR — RESULT.md still carries the two stale claims round 5 reported as removed

`tracking/tasks/T1-trace-capture/RESULT.md:152` and `:158-160`.

RESULT.md:139-141 states, under "Round 5 fixes", that the stale claims were removed. They were
not. `:158-160` still reads "**User `@[congr]` transports are recorded as one `change`** (6 of
46 calls) … this is the largest remaining gap", superseded by the same file's Round 6 section
at `:100-102` and contradicted by the measurement table, in which no `change` step appears.
`:152` still says the checker prints `OK: 40`; it prints **`OK: 51`**. This is REVIEW-5 defect
5 recurring in the same file, one round later.

Separately, RESULT.md:39-41 says the table's "Counts, kinds and bytes below are **generated**
by … `--report`". True of those five columns; the `wall`, `peak RSS` and `unres.` columns are
not generated and are still hand-transcribed. They happen to be right this round (all five
modules exit 0, so `unres.` is 0), but the sentence overstates what is mechanised.

---

## Fidelity

**Differential battery: 20 new goals on the dsimp paths, plus the REVIEW-4/5 set.**
`/private/tmp/t1r6/Diff{S,T}.lean` run the same 20 goals under `simp` and `simp_trace`, each
followed by `trace_state`, and the two outputs are compared after normalising the tactic text:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r6/DiffS.lean > /private/tmp/t1r6/diffS.out 2>&1
SIMP_TRACE_OUT_ROOT=/private/tmp/t1r6 lake env lean /private/tmp/t1r6/DiffT.lean > /private/tmp/t1r6/diffT.out 2>&1
diff /private/tmp/t1r6/nS.txt /private/tmp/t1r6/nT.txt     # 0 lines
```
The 20 cover `zeta := false`, `decide := true`, `proj := false`, `iota := false`, `dite` in a
type, `etaStruct := .all` / `.none`, `ground := true`, `implicitDefEqProofs := false`,
`unfoldPartialApp := true`, a `Fin (if True then 3 else 4)` under a lambda and bare, `dsimp :=
false`, `List.length` literal reduction, `Nat.succ` literal, `zetaDelta := true`,
`beta := false`, `singlePass`, a `Fin` literal projection, and `decide` on a ground `ite`
condition. **Both exit 0, all 20 traces are written, zero `unresolved` lines in the traced
run, and the goal states are byte-identical.** Kind coverage across them: `rw`, `eq`, `unfold`,
`zeta`, `beta`. No divergence from stock was found anywhere this round — as in round 5, every
defect above is a trace-content defect, not a goal-state one.

**The `dreduce_ite` path specifically.** `withInDSimp` is entered (`Traversal.lean:630`), and
under it stock and fork both reduce `Fin (if True then 3 else 4)` to `Fin 3`: running
`simp at h` and `simp_trace at h` on the same hypothesis leaves `h : True` in both
(`/private/tmp/t1r6/DI_C.lean`). REVIEW-5 4 is fixed. What the fork records for that firing is
defect 4.

**The double-log guard — no drop found.** `Traversal.lean:641` and `:665` defer `logDStep` when
`eventCount` grew during the stock `dpre`/`dpost` call. The guard reads the *outer* frame
(`Traversal.lean:270-277`), and `instrumentD` pushes a `procEvents` frame for the duration of
the inner call and pops it before recording, so a nested `simp` inside a dsimproc cannot
inflate the count and steal the log. Two probes confirm: an unattributable-by-construction
dsimproc (`/private/tmp/t1r6/DS.lean`) and one that runs `Simp.simp` on a side term first
(`DS2.lean`) are both recorded, at the right position. I could not construct a silent drop.

**`classifyProof` after the `propext` change — three probes, two findings.** `propext (L …)`
positive: names the inner lemma (`propext_lemma.json` → `fixtureTag_iff`). `propext (Iff.intro
…)` negative control: present, in `UnresolvedFixtures.lean`, and the **real** Mathlib
`existsAndEq` goal now behaves the same way (`G04c.lean` → classified, goal state stock's).
`propext (Iff.symm …)` and `propext (Iff.trans …)`: defect 3. `Eq.symm (propext …)`: classified,
lossy, noted under defect 3. An explicit *type* argument that is not a subterm is correctly
rejected (`CP4.lean` → classified `unresolved`, not misrecorded); an explicit *class-typed*
argument is not: defect 2.

**Local-hypothesis origins, 13 shapes.** `/private/tmp/t1r6/Loc.lean`, all traced, exit 0:
`[h]`, `[← h]`, `[*]`, `[h] at h'`, `at h` self-rewrite, `+contextual`, inaccessible, `h : p`,
`h : ¬p`, `h : a ↔ b`, `h : ∀ x, f x = g x`, a `let`-bound local, and a shadowed name. Eleven
are correct: `local` present with the right `ctxIndex` and `inaccessible`, `name` the pp display
form, `prop` where applicable, the contextual one in the separate `{"contextual":…}` namespace.
The shadowing case is right and worth stating — `have h` over an existing `h` records
`ctxIndex: 4`, and `dumpctx` confirms the outer `h` is index 3, so the trace identifies the
*inner* one, which is also what `rw [h]` would pick. The `let`-bound case is defect 6.
**Against what a generator needs:** `rw [h]` and `rw [← h]` are fully determined (`name` +
`dir` + `local`); `rw [eq_true h]` is determined by `prop` — for ASCII names only (defect 1);
`rw [h x]` is **not**: `args` is in the spec and `#[]` in every trace the tree produces
(`grep '"args"'` over `out/` and `meas_out/` finds none), so `L11.json` records
`h : ∀ x, f x = g x` fired at `f c` as a bare `rw` with no instantiation. That is survivable
because `pos` pins the redex, but it is the same missing field defect 2 needs.

**Frame machinery.** Re-checked the `!`-indexing census from round 5; unchanged and still
guarded. `git diff` since round 5 touches `Recorder.lean`, `Traversal.lean`, `Tactic.lean`,
`Types.lean`, the fixtures and the checker; no new partial access was introduced.

---

## Report check

`python3 -B Experiment/check_simp_trace.py --report` reproduces RESULT.md:45-50 **exactly**,
line by line, after deleting `meas_out/` and `isempty_out/` and re-running all five measurement
modules — 46 calls, 229 steps, 44321 bytes, and every per-file kind tally. The five generated
columns are honest. The three hand-written ones are not generated; see defect 8.

**It does not silently under-count.** Perturbed two ways against the live tree and restored:
dropping one step from `ExistsUniqueTraced_01.json` moved the row to `8 | 28 | rw 22 …| 5573`,
and removing `ExistsUniqueTraced_02.json` entirely moved it to `7 | 18 | rw 15 … | 4206`. Both
changes surface immediately. What `--report` does *not* do is regenerate or validate the
traces: it tallies whatever sits in the two gitignored output directories, so a stale
`meas_out/` yields a stale table that looks generated. Running the modules first is a
convention, not a check the script enforces (`report()` at `:495` only errors when a directory
is missing or empty).

**Standard checks.** Scratch build with `.lake/build/lib/lean/ExplicitLean/SimpTrace{,.olean,
.ilean,.trace,.olean.hash,.ilean.hash}` deleted: `lake build ExplicitLean.SimpTrace` **clean,
no warnings**, exit 0, 9.45 s, 744 MB. `test/SimpTrace/Fixtures.lean`: **exit 0**, no errors.
`test/SimpTrace/UnresolvedFixtures.lean`: **exit 1 by design**, two classified lines (the
`have`-telescope `change`, and the `Iff.intro` negative control). `python3 -B
Experiment/check_simp_trace.py`: **`OK: 51`**, exit 0, 14.3 s, 1 517 MB. The five measurement
modules, regenerated from empty output directories, all exit 0:

| file | wall | peak RSS | exit |
| --- | --- | --- | --- |
| `IsEmptyBasicTraced.lean` | 2.42 s | 677 MB | 0 |
| `NontrivialDefsTraced.lean` | 2.39 s | 668 MB | 0 |
| `FunctionDefsTraced.lean` | 2.52 s | 677 MB | 0 |
| `ExistsUniqueTraced.lean` | 2.61 s | 682 MB | 0 |
| `FunctionBasicTraced.lean` | 2.94 s | 742 MB | 0 |

Nothing came near 30 minutes or 40 GB.

**Scope.** `git diff --name-only $(git merge-base codex/search-free-mathlib-2026-08-31
task/T1-trace-capture) task/T1-trace-capture` lists 75 files. Every one is under
`ExplicitLean/SimpTrace/`, `ExplicitLean/SimpTrace.lean`, `test/SimpTrace/`,
`Experiment/check_simp_trace.py` or `tracking/tasks/T1-trace-capture/`. `ExplicitLean.lean`,
`lakefile.toml` and `tracking/SIMP-TRACE-SPEC.md` are **not** in the list — the spec amendments
were made by the coordinator on the main branch, correctly. No tracked scratch: `git ls-files |
grep -E 'out/|scratch'` is empty, and `out/`, `isempty_out/`, `meas_out/` are gitignored.
Working tree clean.

---

## Integration

Replayed in the T2 worktree at its **committed tip `16a2214`** ("T2: RESULT.md at the 110-line
budget"), clean, after `lake build ExplicitLean.ExplicitRw.Tactic` (exit 0).

**(A) The `simp [← h]` local trace replays verbatim.** `/private/tmp/t1r6/out/L02.json` — the
newly fixed shape, `dir: "rev"` with a resolved `local` — hand-translates to
```
explicit_rw [← h at [0, 1, 0, 1], add_zero at [0, 1], eq_self at []] then exact True.intro
```
and is accepted with no error. Every position is copied unchanged from the JSON; T2 navigates
by raw child index with no search, so a wrong index fails loudly. T2's `← ` prefix on
`explicitRwRw` (`Tactic.lean:350`) maps one-to-one onto `dir`, and the `local` object is not
needed for an accessible name — it would be, through `rename_i`, for the inaccessible case.

**(B) The `dreduce`-path trace does not replay as recorded — defect 4.**
`test/SimpTrace/out/dreduce_ite.json`'s first step is
`{"kind":"eq","pos":[0,1],"lhs":"if True then 3 else 4","rhs":"3","by":"rfl","source":"dreduceIte"}`.
The faithful T2 translation is `eq (if True then 3 else 4) = 3 by rfl at [0, 1]`, and
`/private/tmp/t1r6/T2rep.lean` is rejected: position `[0]` is the domain of a dependent `∀`
whose body mentions the bound variable, and T2 will not build the cast. The same step written
as the definitional change it actually is — `change (3 : Nat) at [0, 1]` — replays and closes
the goal (`T2repB.lean`, exit 0), as does the full five-step trace with that one substitution
(`T2repC.lean`, exit 0). **Attribution is shared and the coordinator should split it.** Plain
Lean `rw [show (if True then 3 else 4) = (3:Nat) from rfl]` *does* succeed on that goal
(`/private/tmp/t1r6/PlainRw.lean`, exit 0) through `rw`'s motive fallback, so the obstruction
is not mathematical and T2 could support it. But T1 is the side that chose `eq` — a
propositional kind carrying a proof obligation — for a reduction the definitional layer
performed, and the spec has four named kinds plus `change` for exactly that. Fixing T1
(defect 4) makes the trace replayable on T2 as it stands today; fixing T2 alone leaves the
kind wrong.

**(C) No new T2-side syntax gap.** REVIEW-5's item (C) — the `congr` kind having no T2 form —
is **closed**: T2 now declares `explicitRwCongr` at `Tactic.lean:431-432` with exactly the
shape REVIEW-5 specified (`&"congr " num " [" explicitRwInnerStep,* "]" explicitRwPos`), a
non-recursing `explicitRwCongr0` for the inner level, and dispatch at `:1087`. Nothing in the
current T1 kind set is unexpressible in T2 syntax.

---

## Open question

**Should a side trace carry `pre`/`post` the way a location does?** Yes, and the argument is
stronger than "under-determined data". Eight of the 28 side traces in the tree still end at
`"close": null` (all six user-`@[congr]` traces plus `FunctionBasicTraced_08`/`_13`), and a
`close: null` on a `SideTrace` is not merely silent about *how* the goal closed — it is silent
about *whether* it closed and about what the residual is. A `LocationTrace` never has that
ambiguity because `post` carries the residual and `close` carries the finisher, and the
validator can check the pair. The implementer's reason for deferring — that T2 supplies the
terminal tactic from its own `with [...]` entry — is exactly the problem: it means the two
sides each decide independently what the side goal reduced to, with nothing in the trace to
reconcile them, and I had to supply `then rfl` / `then exact True.intro` by inspection in round
5 and again here. That is a silent-divergence channel between a recorder whose whole premise is
"no search, no reconstruction" and a replayer that is now reconstructing. I would add `post` to
`SideTrace` with the same `null`-means-closed convention, which costs one field and one spec
bump and makes `close: null` mean one thing (`post` is the residual, no finisher recorded)
instead of two. The cheaper alternative — always record a close form — is worse: it would force
the recorder to invent `rfl` where it did not observe one, which is the invention the round-3
fix for `eq` steps' `by` deliberately refused. **Coordinator decides; this is a schema bump
either way, so it belongs with whatever other amendment lands next rather than on its own.**

---

**Totals: 2 critical, 3 major, 3 minor; 0 T2-side gaps (REVIEW-5's `congr` gap is closed).**
Defects 1 and 3 are both incomplete fixes of round-5 criticals that were reported as done, and
defects 2, 3 and 5 share a shape: a recorder path that names something it did not fully capture
— an instance it dropped, a plumbing head it did not list, a hypothesis name it erased. Defect
8 is the round-5 measurement-drift defect recurring in the same file. **No goal-state divergence
from stock was found anywhere in this round**, across 20 new differential goals and the
regenerated five-module corpus.
