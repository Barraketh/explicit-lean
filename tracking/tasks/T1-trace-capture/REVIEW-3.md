# T1-trace-capture: adversarial review, round 3

Scope check passed: `git diff --stat $(git merge-base codex/search-free-mathlib-2026-08-31
task/T1-trace-capture) task/T1-trace-capture` lists 45 files, all inside
`ExplicitLean/SimpTrace.lean`, `ExplicitLean/SimpTrace/`, `test/SimpTrace/`,
`Experiment/check_simp_trace.py`, `tracking/tasks/T1-trace-capture/`. Working tree clean;
`scratch/` is gitignored and untracked, `test/SimpTrace/out/` and `isempty_out/` likewise.

**All committed checks reproduce.** `lake build ExplicitLean.SimpTrace` with oleans deleted:
clean, 7.5 s, 688 MB peak RSS. `test/SimpTrace/Fixtures.lean`: pass, 3.6 s. `python3 -B
Experiment/check_simp_trace.py`: `OK: 30 ... and out-of-root paths (including through
symlinks) are refused`, 6.2 s. `IsEmptyBasicTraced.lean`: pass, 2.8 s. The IsEmpty
measurement reproduces **exactly**: 17 calls, 76 steps, mean 4.5, range 2–6, kinds `rw` 70 /
`unfold` 6, total 15 017 B, mean 883.4 B, max 1129 B.

**All six REVIEW-2 defects re-verified fixed** by re-running each reproducing command with
the `=>trace` delimiter, not by reading the diff. 1 (2-deep `@[reducible]` chain): depths 2,
3 and 4 all trace, emitting one `unfold` per link. 2 (inaccessible name): `name` is now the
pp form `a✝`, `local.userName` the raw hygienic name, `ctxIndex` 3. 3 (symlink): refused,
error names the resolved `/private/tmp/SYMLINK_ESCAPE.json` and the file is not created.
4 (side `close: unknown`): now a hard error — **but see defect 3 below**. 5 (`with_trace`
token): `=>trace` reserves nothing; identifiers `with_trace` *and* `trace` both compile
under the import. 6: RESULT.md narrowed as described.

**REVIEW-1 spot-checks (2 requested, 6 run)** — all still fixed: parenthesized
`(config := { decide := true })`, `(discharger := assumption)`, `(disch := assumption)`;
`+decide` records `eq`/`by:decide`; shadowed binders emit `beta`; `let` emits `zeta`;
`absurd:h` names the hypothesis.

---

## 1. CRITICAL — an unattributed simproc firing aborts on goals stock `simp` proves

`ExplicitLean/SimpTrace/Tactic.lean:137-140` (`toStep`, the `.unattributed` arm), reached
from `Recorder.lean:173-182`. `classify` returns `.unattributed` when `usedTheorems` did not
grow; `reattribute?` then probes simp *theorems* only, and the `.proc none` rescue added in
round 1 fires only when `r.expr` is `True`/`False`. A ground arithmetic or matcher simproc
that produces an ordinary term satisfies neither, so `toStep` throws.

This is not an exotic path: it is ordinary literal arithmetic.

Input (`/private/tmp/t1r3/FINAL.lean`):
```
example : ([1,2,3] : List Nat).length + 0 = 3 := by simp_trace
```
Observed: `error: simp_trace: unattributed simp step (no recordable kind)` /
`before: 2 + 1` / `after:  3`.
Expected: the goal closes, as stock `simp` does, with the firing recorded as an `eq` step
(`by: "rfl"`, `source: "Nat.reduceAdd"` or similar) — the spec's `eq` kind already covers it.
Repro:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r3/FINALS.lean   # stock simp: exit 0, no output
lake env lean /private/tmp/t1r3/FINAL.lean    # simp_trace: the abort above
```

Two further instances of the same abort, each on a goal stock `simp [..]` proves:
- matcher/iota reduction — `before: match 0 with | 0 => 7 | n.succ => 9`, `after: 7`
  (`/private/tmp/t1r3/IOTA2.lean`, `def mtch : Nat → Nat | 0 => 7 | (_+1) => 9`,
  `example : mtch 0 + 0 = 7 := by simp_trace [mtch]`);
- `Option.getD` on a literal — `before: match some 3 with | some x => x | none => 0`,
  `after: 3` (`/private/tmp/t1r3/IOTA5.lean`).

Fix direction: widen the `.proc none` rescue at `Recorder.lean:178` from
`r.expr.isTrue || r.expr.isFalse` to any unattributable firing, and let `mkEqStep`'s
`scratchCheckEq` decide `rfl`/`decide`; that path already refuses to invent a `by` value.
This also answers task 2(a) for iota: **iota/matcher reduction is not emitted as any kind
at all** — it aborts before reaching `toStep`'s `.defeq` arm.

## 2. CRITICAL — `findBridgeChain?` cost is exponential; real goals time out where stock `simp` is flat

`ExplicitLean/SimpTrace/Position.lean:283-302`. The BFS expands *every* reducible site of
*every* frontier term at each of `fuel = 32` levels. `reducibleSites` (`Position.lean:252-270`)
walks the whole term and calls `withDefault <| unfoldDefinition?` at each constant-headed
node, so the frontier branches by the number of reducible sites and the work per level is
(frontier size) x (sites) x a `whnf`-class call. `seen` is an `Array Expr` scanned with
`contains` (`Position.lean:297`), so dedup is itself quadratic. The task-3 corpus hits this
(defect 4), and it is trivially reproducible:

Input (`/private/tmp/t1r3/D{4,6,8}.lean`, a chain `c0 n := n`, `cᵢ n := cᵢ₋₁ n`, goal
`c_{d-1} n + 0 = n`, `simp_trace [c_{d-1}, ..., c0]`, `maxHeartbeats 4000000`):

| chain depth | `simp_trace` | stock `simp` |
| --- | --- | --- |
| 4  | 6.8 s | 2.7 s |
| 6  | 219.4 s | 2.7 s |
| 8  | **timeout at `whnf`** (221 s) | 2.7 s |
| 12 | **timeout at `whnf`** (228 s) | 2.7 s |
| 30 | **timeout at `whnf`** (51.7 s, 1M heartbeats) | 2.5 s |

Stock `simp` is flat at ~2.7 s across every depth. Repro:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r3/S6.lean   # stock: real 2.72
lake env lean /private/tmp/t1r3/D6.lean   # traced: real 219.40
lake env lean /private/tmp/t1r3/D8.lean   # traced: deterministic timeout at `whnf`
```
A second, independent shape times out even at 10x heartbeats — a projection under a binder:
```
structure Q where q : Nat
example : (∀ w : Q, (Q.mk w.q).q + 0 = w.q) := by simp_trace   -- timeout, 101.6 s
example : (∀ w : Q, (Q.mk w.q).q + 0 = w.q) := by simp         -- 2.70 s
```
Repro: `lake env lean /private/tmp/t1r3/PROJ3.lean` (traced, `maxHeartbeats 2000000`) versus
`/private/tmp/t1r3/PROJ2.lean` (stock).

RESULT.md's limitation note says the search "is bounded at 32 reductions and throws past
that", which describes the *chain length* bound; it does not disclose that reaching that
bound costs exponential time, and the round-2 fix that made chains composable is what
introduced the blow-up. This is the answer to task 2(c): the cost does explode, on inputs
(stacked `@[reducible]`/`abbrev`, projections under binders) that RESULT.md itself names as
the reason the chain search exists.

Fix direction: bound the *frontier* as well as the depth, restrict `reducibleSites` to
positions on the path toward the target rather than the whole term, and replace the `seen`
array with a `HashSet`/`ExprStructEq` set.

## 3. MAJOR — `(disch := omega)` aborts on a call stock `simp` proves

`ExplicitLean/SimpTrace/Recorder.lean:242-244` (`describeProof`). REVIEW-2 defect 4 reported
that a side condition discharged by a proof outside the recognised shapes was silently
written as `close: {"by":"unknown"}`. The fix turned that into a `throwError`. The silent
wrong value is gone, but the call now **fails** where it previously compiled, and stock
`simp` with the same discharger succeeds.

Input (`/private/tmp/t1r3/UNK2.lean`, REVIEW-2's own repro):
```
example (m n k : Nat) (h1 : n ≤ k) (h2 : k ≤ m) : m - n + n = m := by
  simp_trace (disch := omega) [Nat.sub_add_cancel]
```
Observed: `error: simp_trace: side condition discharged by a proof whose closing form is not
one of the spec's (rfl, true_intro, assumption:<name>, absurd:<hyp>, decide)` /
`proof: Decidable.byContradiction fun a => _example._proof_1 m n k h1 h2 a`.
Expected: the same goal state stock `simp (disch := omega) [Nat.sub_add_cancel]` leaves
(exit 0, no output).
Repro:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture
lake env lean /private/tmp/t1r3/UNK3.lean   # stock: exit 0, no output
lake env lean /private/tmp/t1r3/UNK2.lean   # simp_trace: the abort above
```
Any non-trivial custom discharger (`omega`, `assumption <;> ...`, a `decide`-backed one) is
now unusable. The spec's close enumeration has no form for "discharged by an arbitrary
tactic", so this is arguably a spec gap rather than a coding error — but it is a
substitutability regression introduced by the round-2 fix and it must not merge silently.
The honest options are a spec amendment adding a `by:<tactic>` close form (a coordinator
decision), or recording the side goal with `close: null` plus the discharger syntax.

## 4. MAJOR — two of eleven real Mathlib calls fail; both are position-solver failures

Found by task 3 (see **Measurement**). Both files compile under stock `simp`.

**(a) `Mathlib/Logic/Function/Defs.lean:62` (`Function.prod_inj`).**
`ExplicitLean/SimpTrace/Position.lean:316-324` (`collectBridges`).
```
error: simp_trace: no sequence of at most 32 definitional reductions reaches the recorded subterm
target:  ∀ (x : ι), f x = f' x ∧ g x = g' x
running: (∀ (x : ι), (f x, g x).fst = (f' x, g' x).fst ∧ (f x, g x).snd = (f' x, g' x).snd) ↔ f = f' ∧ g = g'
```
Four independent `proj` reductions at four *different* positions must be composed before the
recorded subterm appears. `findBridgeChain?` can compose across positions in principle, but
with this branching it exhausts the bound (and, per defect 2, would be very slow if it did
not). Repro: `SIMP_TRACE_OUT_ROOT=/private/tmp/t1r3/meas/out lake env lean
/private/tmp/t1r3/meas/FunctionDefs.lean`.

**(b) `Mathlib/Logic/ExistsUnique.lean:115` (`existsUnique_eq`).** Same site.
```
error: simp_trace: no sequence of at most 32 definitional reductions reaches the recorded subterm
target:  _fvar.5713.109 = a'
running: ∃! a, a' = a
```
Note `_fvar.5713.109` in `target`: the recorded `before` still carries a simp-introduced free
variable that `abstractSimpFVars` (`Position.lean:137-148`) did not abstract, because the
bridge search runs *before* any binder has been crossed, so `depth` is 0 and the guard at
`Position.lean:138` returns the term unchanged. The search is therefore looking for a term
that cannot occur in the running term at any position.
Reproduced in isolation, independent of the file transcription (`/private/tmp/t1r3/ISO2.lean`):
```
example {α : Sort*} {a' : α} : ∃! a, a = a' := by
  simp_trace only [eq_comm, ExistsUnique, and_self, forall_eq', exists_eq']
```
Repro: `lake env lean /private/tmp/t1r3/ISO.lean` (stock, exit 0, no output) then
`lake env lean /private/tmp/t1r3/ISO2.lean` (the abort above).

A related third failure mode surfaced while narrowing (b): dropping `eq_comm` gives
`error: simp_trace: replayed term does not match simp's result` / `replayed: ∃! a, a = a'` /
`actual: ∃ x, x = a' ∧ ∀ (y : α), y = a' → y = x` — an `ExistsUnique` unfold that was never
recorded. Stock `simp only` leaves a goal on that variant too, so the validator is right to
complain, but the message misattributes a *missing recorded step* to a replay mismatch.

## 5. MAJOR — `rw` steps naming Prop-valued lemmas cannot be replayed by T2

`ExplicitLean/SimpTrace/Tactic.lean:129-132` (`toStep`, the `.thm` arm). Every theorem origin
becomes `kind: "rw"` with a `name`, regardless of the lemma's type. simp uses a Prop-valued
lemma `h : P` as the rewrite `P ↝ True` (via `eq_true`), but the trace records only the name,
so T2 elaborates it and finds neither an `Eq` nor an `Iff`.

This is not hypothetical: **T1's own headline IsEmpty corpus contains such steps.**
`test/SimpTrace/isempty_out/` records `leftTotal_empty` and `rightTotal_empty` as `rw`, and
`leftTotal_empty : LeftTotal R` is a plain proposition
(`.lake/packages/mathlib/Mathlib/Logic/IsEmpty/Basic.lean:101`).

Input (`/private/tmp/t1r3/PROPRW.lean`, in the T2 worktree):
```
example {α : Sort*} {a' : α} : (∃ a, a' = a) ↔ True := by
  explicit_rw [exists_eq' at [0]] then rfl
```
Observed: `explicit_rw: step 1: lemma `exists_eq'` does not prove an equation or an iff; its
type is ∃ a, ?m.6 = a`.
Expected: either T1 records these as `{"kind":"rw", ..., "dir":"fwd"}` *plus* a marker that
the lemma is a proposition used as `P ↝ True`, or it records them as `eq` steps with the
`True` right-hand side spelled out.
Repro:
```
cd /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw
lake env lean /private/tmp/t1r3/PROPRW.lean
```
Responsible side: **T1** (or the spec). The spec's `rw` bullet says `name` is "the equation or
iff `name`"; a Prop-valued lemma is neither, so T1 is emitting a step the spec does not
sanction and T2 correctly refuses it. Two of the three traces hand-translated for task 4 hit
this (see **Integration**).

## 6. MINOR — `before`/`after` debug fields print raw loose bvars as `#0`

`ExplicitLean/SimpTrace/Tactic.lean:118-119` (`ppIn` on `raw.before`/`raw.after` for bridge
steps built at `Position.lean:376-380`). A bridge's `before`/`after` come from the running
term, which still has loose bound variables, so the pretty-printer emits de Bruijn indices:
```
{"kind":"beta","pos":[0,1,1],"before":"(fun x => f x (x + 0)) #0","after":"f #0 (#0 + 0)"}
{"kind":"zeta","pos":[1,0,1],"before":"let y := #0;\ny + 0","after":"#0 + 0"}
```
The spec calls these debug fields that replay must not depend on, and the checker deliberately
ignores them, so this is cosmetic — but `#0` is not a term any reader can re-elaborate, and
RESULT.md presents `before`/`after` as "pretty-printed subterms ... used by validation".
Repro: `lake env lean /private/tmp/t1r3/R1.lean` (shadowed-binder and `let` examples) and
`/private/tmp/t1r3/PANIC.lean`.

## 7. MINOR — RESULT.md overstates substitutability and the fork rationale

- Line 10-12, "Goal state matches stock simp ... verified ... on the reviewer's 18-form
  corpus and every fixture": defects 1, 3 and 4 are five distinct goals stock `simp` proves
  and `simp_trace` hard-errors on, three of them from a 3-file Mathlib sample.
- The **Limitations** paragraph says the chain search "is bounded at 32 reductions and throws
  past that" without disclosing the exponential cost that bound hides (defect 2).
- The **Fork assessment**'s load-bearing claim is incorrect; see **Fork note**.

Every timing, count, kind tally and byte figure in RESULT.md reproduced exactly.

---

## Measurement (task 3)

Three Mathlib modules copied to `/private/tmp/t1r3/meas/`, `public meta import
ExplicitLean.SimpTrace` added, every executable `simp`/`simp only` replaced by
`simp_trace ... =>trace "<abs path>"` (11 calls total), compiled with `lake env lean` and
`SIMP_TRACE_OUT_ROOT=/private/tmp/t1r3/meas/out`. Bound not hit (total wall well under
20 min; peak RSS 679 MB, far under 30 GB). All three originals compile under stock `simp`.

| file | calls | traced | steps | kinds | bytes | wall | peak RSS |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Logic/Nontrivial/Defs.lean` | 1 | 1 | 6 | `rw` 6 | 1068 | 2.54 s | 669 MB |
| `Logic/Function/Defs.lean` | 1 | **0** | — | — | — | 3.72 s (errored) | 674 MB |
| `Logic/ExistsUnique.lean` | 9 | **7** | 19 | `rw` 16, `unfold` 1, `beta` 2 | 3899 | 2.67 s (errored) | 680 MB |
| **total** | **11** | **8** | **25** | `rw` 22, `unfold` 1, `beta` 2 | 4967 | — | — |

Bytes: total 4967, mean 620.9, max 1068 over the 8 successful traces.

**Errors on calls stock `simp` proves — 2 of 11 (18%).** Both are defect 4; exact error text
and per-call repro commands are there. The `Function/Defs.lean` abort also prevented its one
call from ever writing a trace, so the traced coverage of that file is zero.

For comparison the committed IsEmpty measurement (17 calls, 100% traced) reproduces exactly,
so the failure rate is a property of these modules, not of the harness.

## Integration (task 4)

Three traces hand-translated to `explicit_rw` per
`/Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw/ExplicitLean/ExplicitRw/Tactic.lean`
and replayed in the T2 worktree (`/private/tmp/t1r3/REPLAY*.lean`), importing the same Mathlib
module plus `ExplicitLean.ExplicitRw`.

**`nt01` (`Nontrivial/Defs.lean:98`, 6 `rw` steps, three binder-crossing positions) — replays
exactly.** All six positions, names and directions are accepted verbatim, including
`[0,1,1,1]` under two nested `∀` binders and the `Classical.not_not` step whose `before` is
`¬x✝ ≠ x`. Closing with `then exact True.intro` (the spec's `true_intro`, which T2 renders as
`exact <term>`) leaves no goal: `lake env lean /private/tmp/t1r3/REPLAY2.lean`, exit 0, no
output. My first attempt used `then rfl` and failed with `Tactic 'rfl' failed ... ⊢ True` —
**reviewer error, not a defect**: T2's documented rendering of `true_intro` is `exact`, not
`rfl`.

**`eu03` (`ExistsUnique.lean:119`, `unfold` + 2 `beta` + 3 `rw`) — fails at the last step.**
The `unfold ExistsUnique at []`, both `beta` steps and `forall_eq'`/`and_self` are all
accepted at the recorded positions; step 6 fails:
`explicit_rw: step 6: lemma `exists_eq'` does not prove an equation or an iff; its type is
∃ a, ?m.15 = a`. Responsible side: **T1** — defect 5. `exists_eq' : ∃ a, a' = a` is a
proposition, which T1 recorded as a `rw`.

**`eu08` (`ExistsUnique.lean:154`, 4 `rw`) — fails at the first step.**
`explicit_rw: step 1: lemma `List.not_mem_nil` does not prove an equation or an iff; its type
is False`. Same cause, same responsible side: `List.not_mem_nil : ¬a ∈ []` is a proposition.

So the **position convention, direction encoding, binder crossings, `unfold` and `beta`
kinds all agree between T1 and T2** — every step of that class replayed. The only mismatch is
defect 5, and it is on T1's side. No T2-side defect was found this round; REVIEW-2's T2
universe-metavariable defect did not recur in these traces (`not_nonempty_iff` was not
exercised here).

## Inaccessible-name handling (task 5)

Context `a b : Nat`, `a✝ : a = b` (from `intro _`), rewrite uses `a✝`
(`/private/tmp/t1r3/CTX.lean`, `CTX2.lean`, `REN.lean`). Observed:
```
{"kind":"rw","name":"a✝","dir":"fwd",
 "local":{"userName":"a._@._internal.0._stdin.2021293395._hygCtx._hyg.21",
          "inaccessible":true,"ctxIndex":3}, "before":"a","after":"b"}
```
- `name` **is** the pp form (`a✝`), matching the spec and fixing REVIEW-2 defect 2. With two
  inaccessibles the forms are `a✝¹`/`a✝` as the pretty-printer numbers them.
- `local.userName` **is** the raw user name (the full hygienic `a._@...._hyg.21`), not
  `eraseMacroScopes`'d — correct, and it cannot be confused with the accessible `a`.
- `local.ctxIndex` **is** correct, and it is exactly `LocalDecl.index`.

**What `ctxIndex` is** (verified by dumping `LocalDecl.index` beside the pp names,
`/private/tmp/t1r3/CTX2.lean`): a 0-based count from the **front** of the local context,
over *all* declarations including ones the user never sees — the auxiliary `_example`
recursion declaration and any section `variable`s. In the bare case `[_example, a, b, a✝]`
the hypothesis is index 3; adding `variable {G} (inst : Inhabited G)` to the section makes
the context `[G, inst, _example, a, b, a✝]` and the same hypothesis reports index 5. It is
**not** an index into the hypotheses a reader sees, and it is **not** stable across changes
to the surrounding section or to `intro` order (adding binders before the `intro` shifts it).
It is stable within one recorded call, which is all position solving needs.

**Can a generator `rename_i` from it? Only indirectly.** `rename_i` names the *trailing*
inaccessible hypotheses, right-to-left (`rename_i h1 h2` binds `a✝¹` then `a✝`), and it
counts only inaccessibles. `ctxIndex` counts every declaration from the front. A generator
must therefore compute "how many inaccessible hypotheses follow this one" from the full
recorded context, which the trace does not carry — the trace records only the one index. The
`name` field's pp form (`a✝¹`) actually carries the needed information more directly, since
its superscript *is* the right-to-left rank. Verified working: `/private/tmp/t1r3/REN.lean`,
exit 0. Recommend documenting `ctxIndex` as "`LocalDecl.index`, for disambiguation only, not
a `rename_i` argument" rather than the spec's current "the hypothesis's index in the local
context", which invites the wrong reading.

## Reduction kinds and the panic guard (task 2, a/b/d)

**(a) Kinds emitted.** `reduceHere?` (`Position.lean:227-248`) emits exactly four reduction
shapes — beta, zeta (`letE`), `reduceProj?`, and delta via `unfoldDefinition?` — which
`toStep`'s `.defeq` arm (`Tactic.lean:141-162`) maps to `beta`, `zeta`, `proj`, `unfold`, with
`change` as the fallback. All five are in the spec, and `eta` is reachable in principle
(`isEta`, `Tactic.lean:78-80`) though unexercised. **Iota/matcher reduction is emitted as no
kind at all**: it aborts earlier, in the `.unattributed` arm — defect 1. I could not
construct a case where the bridge emitted `change`, so the `pp.all` re-elaboration check
asked for in (a) had no input; instance-projection reductions went through ordinary `rw`
(`Nat.default_eq_zero`) or `unfold`+`proj` (`/private/tmp/t1r3/IOTA2.lean`,
`/private/tmp/t1r3/CHG.lean`), never `change`.

**(b) Chains that differ from what simp did.** `reduceHere?` calls `withDefault <|
unfoldDefinition?`, i.e. `.default` transparency, so it will **not** delta an
`@[irreducible]` constant — the emitted `unfold` kinds stay within what T2's `unfold` can
perform, and I could not construct a counterexample there (`/private/tmp/t1r3/IRR*.lean`;
`@[irreducible] def opq` went through its equation lemma as a `rw`, not a bridge). One
adjacent hazard: with `@[reducible] def wrap n := opq n`, simp closed
`wrap n + 0 = opq n` by `eq_self`, and the trace records `{"name":"eq_self","before":"wrap n =
opq n"}` — replaying that `rw` needs the same reducibility setting T1 ran under, which the
trace does not record. Nested positions with loose bvars did **not** produce a divergent
chain: the recorded `pos` values were correct in every bridge case I checked
(`/private/tmp/t1r3/PANIC.lean`), only their `before`/`after` strings are unreadable
(defect 6).

**(d) Panic guard.** Not triggerable through the paths tried. `reduceHere?`'s `loose` guard
(`Position.lean:231,238`) keeps `whnf`/`unfoldDefinition?`/`reduceProj?` off open terms, and
bridges under `lam`, `forallE` and `letE` binders all completed without a panic
(`/private/tmp/t1r3/PANIC.lean`). `scratchCheckEq` (`Tactic.lean:91-108`) calls `mkEq`/`whnf`
/`mkDecide` on recorded terms, but it runs under `withLCtx raw.lctx` where simp's binder
fvars are in scope, so those terms are closed; `reattribute?`'s `tryTheoremWithExtraArgs?`
likewise. What I found instead of a panic is the timeout of defect 2 — the projection-under-
binder case spends its budget inside `whnf` rather than crashing in it.

## Fork note (task 7)

**The Fork assessment's load-bearing claim is incorrect.** RESULT.md argues for
reconstruction over a fork because "the hard part survives: `simpAppUsingCongr` rebuilds
through congruence *lemmas*, so a fork still maps congruence-argument slots to child indices
— the same problem, moved." Reading the two functions in Lean 4.32.2
(`.../toolchains/leanprover--lean4---v4.32.2/src/lean/Lean/Meta/Tactic/Simp/Types.lean:732-765`
for `simpAppUsingCongr`, `:649-679` for `congrArgs`, `:807-860` for `tryAutoCongrTheorem?`),
the mapping is immediate in all three. `simpAppUsingCongr`'s inner `visit` destructures
`let .app f a := e` and recurses on `f` with `i-1` while simplifying `a` at that level —
which *is* the spec's `app f a ↦ 0 = f, 1 = a` convention, walked in exactly the order a
position tracker would want. `congrArgs` and `tryAutoCongrTheorem?` both iterate
`e.getAppArgs` with a plain counter `i` in argument order, and `argKinds` is indexed by that
same counter. A forked traversal would thread `SubExpr.Pos` by pushing `1` when descending
into `a` and `0` when recursing into `f`; no congruence-lemma slot ever needs to be mapped
back to a child index, because the traversal never leaves the spine. The congruence *lemma*
decides whether an argument is visited (`fixed`/`cast`/`subsingletonInst`/`eq`) and how the
proof is built, but the position of the argument it is visiting is already in hand.

That does not by itself make a fork the right call, and I am not recommending the rewrite as
a defect. The resync cost RESULT.md estimates (~600-700 lines per Lean bump) is real and is a
legitimate reason to prefer reconstruction. But the decision should rest on that cost alone,
because the technical obstacle offered as decisive does not exist — and defects 1, 2 and 4 of
this round are all failures of the reconstruction approach that an exact threaded position
would not have (defect 4(b)'s unabstracted `_fvar`, defect 4(a)'s four-way `proj` composition,
and defect 2's entire search). Three of the four critical/major position defects across three
review rounds now come from `Position.lean`. That trend, not the congruence argument, is the
case worth re-examining.

---

**Totals: 2 critical, 3 major, 2 minor. No T2-side defect this round.**

Scratch files used by the repro commands are under `/private/tmp/t1r3/` and are not committed.
