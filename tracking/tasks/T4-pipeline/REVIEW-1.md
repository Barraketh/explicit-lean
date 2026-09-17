# T4-pipeline adversarial review, round 1 (full)

Reviewed at T4 `1335f2b`. Re-ran everything below; RESULT.md was not trusted.
Driven worktrees **moved since the recorded run**: T1 `1d8ba00b`→`61f59e3e`,
T2 `7ccb98b2`→`6dc69322` (T2 now clean). Both tables are in §Reproducibility.
Scratch under `/private/tmp/t4rev`; nothing was written into T1 or T2, and
`git status` in both was clean before and after.

Verdict: **3 major, 4 minor.** No critical. The harness does not manufacture a
false `replayed`: the isolation argument holds and splice safety is proven. The
majors are one class of **hidden site**, one class of **false `compile_failed`**,
and an **unmarked retained `simp`** that defeats the lint gate.

---

## Defects

### 1. MAJOR — two executable `simp` sites are invisible to the harness
`Experiment/pipeline/sites.py:85` — `skip_line` drops **any line containing
`@[`**, to exclude `@[simp]` attributes. It also drops one-line declarations
that carry both an attribute and a tactic:

```
Mathlib/Logic/Function/Basic.lean:698  @[simp] lemma update_eq_self_iff : … := by simp [update_eq_iff]
Mathlib/Logic/Function/Basic.lean:700  @[simp] lemma eq_update_self_iff : … := by simp [eqComm]
```

Both are executable source `simp` calls — replacement targets under the
governing rule — and neither appears in the site list, the trace list, the
report or the totals. `Logic/Function/Basic.lean` has **25** sites, not 23; the
corpus has **84**, not 82. The two sites are not counted as failures; they are
absent, which is exactly the "hidden site" the brief calls critical. It is
scored major only because the miss is systematic and mechanical rather than
silently wrong per site — but the reported denominator is wrong, and so is the
`45/82` headline.

Independent count (comment/string-aware lint from the main checkout, compared
per line against the harness site list):

```
python3 -B /private/tmp/t4rev/sitecount.py
```

| module | harness | independent | delta |
| --- | --- | --- | --- |
| `Logic/IsEmpty/Basic.lean` | 17 | 17 | 0 |
| `Logic/Nontrivial/Defs.lean` | 1 | 1 | 0 |
| `Logic/Function/Defs.lean` | 2 | 2 | 0 |
| `Logic/ExistsUnique.lean` | 8 | 8 | 0 |
| `Logic/Function/Basic.lean` | **23** | **25** | **−2** |
| `Logic/Basic.lean` | 31 | 33 | −2 (both correct, see below) |

The two `Logic/Basic.lean` deltas (lines 55, 86) are
`withTraceNode … <| simp symmExpr` — the `Lean.Meta.Simp` *API* inside a
metaprogram, not a tactic site. Skipping those is right; the mechanism that
skips them (`Simp.simp` substring) is the correct one. `@[` is not.

Fix: restrict the attribute test to an attribute that is not followed by a
tactic on the same line — e.g. skip only the `@[…]` span itself, then scan the
remainder of the line, rather than discarding the whole line.

Note this also means the harness and `check_transcription.py` **agree with each
other and are both wrong the same way** (both use this rule, as `sites.py:24`
states). Agreement with T1 is therefore not evidence of completeness, and
RESULT.md's "site detection agrees with `check_transcription.py`" is a weaker
claim than it reads as.

### 2. MAJOR — a file-level error is charged to innocent sites as `compile_failed`
`Experiment/pipeline/replay_module.py:550-555` — on a failed per-site probe the
record takes `pdiags[0]`, the **first diagnostic anywhere in the file**, with no
check that it falls inside the site's replacement block. Any error that is not
the site's own (a header error, a stale `.olean`, an unrelated later
declaration) is attributed to the site and the site is counted non-replayed.

Observed live in my re-run, not hypothetically: T2 was mid-rebuild, so
`ExplicitRw.olean` was stale, and the module header error at **line 6** was
charged to two sites at lines 68 and 72:

```
Logic/IsEmpty/Basic.lean site 9  (line 68) → error_line 6, delta −62
Logic/IsEmpty/Basic.lean site 10 (line 72) → error_line 6, delta −66
```

Both were recorded `compile_failed`, dropping replayed from 15 to 13 for that
module and 45 to 43 overall. The attribution fell through to `harness`, which is
the right side but the wrong reason, and the sites are not actually broken.

This is a false negative, not a false `replayed` — but under the revised
protocol replay counts drive T1/T2 fixes, so a spurious `compile_failed` sends
work to the wrong place just as a spurious `replayed` hides it.

Fix: select the first diagnostic whose line falls within the spliced block for
that site; if none does, the probe failed for a reason outside the site and the
status should be a distinct `probe_inconclusive`, never `compile_failed`. A
non-zero exit with no in-block diagnostic must not be counted against the site.

Repro:
```
python3 -B Experiment/pipeline/replay_module.py --module all \
  --t1 …/T1-trace-capture --t2 …/T2-explicit-rw --out /private/tmp/t4rev/rerun
python3 -B -c "…"   # report.json: records with error_line far from rec['line']
```

### 3. MAJOR — retained originals at mid-line sites carry no marker, so the lint gate cannot pass
`Experiment/pipeline/replay_module.py:229-236` — `keep_original` emits the
`-- explicit_rw: unresolved: …` marker only when `site.alone_on_line`. All
**16** `multiple_invocations` sites but one are mid-line (after `<;>`), so the
marker is dropped (`marker_dropped: true` in all 16 records) and the original
`simp` is spliced back **bare**.

Running the main checkout's lint over the translated modules (brief item 6:
"every finding must be inside an `-- Original simp:` comment or an
`-- explicit_rw: unresolved:` retained call") gives **40 findings, 0 of which
satisfy either condition**:

```
python3 -B /private/tmp/t4rev/lintout.py
```

Most are legitimately retained originals at known non-replayed sites, and some
are `simpa`/metaprogram lines out of the current milestone. But as it stands
nothing distinguishes, mechanically, a deliberately retained call from a leaked
one. The acceptance criterion the brief names cannot be evaluated on this
output.

Fix: place the marker on the preceding line (its own line, at the enclosing
indentation) rather than dropping it — a `--` comment line above a `<;>` chain
is valid Lean and does not break the tactic sequence. Then the lint gate becomes
checkable.

### 4. MAJOR-adjacent, scored MINOR — the harness never runs the simp-family lint
`Experiment/pipeline/` contains no reference to `simp_family_lint`. Nothing in
the pipeline or in `check_pipeline.py`'s 179 checks verifies that a site marked
`replayed` actually stopped containing a simp-family token. The brief asks for
exactly this check.

Today the gap is not exploitable: `render_trace` emits only `explicit_rw`
tokens, so a rendered block cannot contain `simp`. I tried to construct the
attack and it only succeeds with hand-forged replacement lines, which the real
path never produces. So this is a missing defence, not a live false `replayed`.
It should still be closed, because `replayed` is the project's primary signal
and it currently rests on the renderer's good behaviour alone rather than on a
check:

```
python3 -B /private/tmp/t4rev/false_replay.py
# forged lines containing `simp only [foo]` splice in and are lint-detected,
# but the harness would have called the site replayed on a clean compile.
```

Fix: after splicing, run `simp_family_lint.findings` over each replacement block
and refuse `replayed` for any finding outside a comment.

### 5. MINOR — `(by simp : T)` silently loses its type ascription
`Experiment/pipeline/sites.py:call_end` stops at a bracket/comma/`;`, but not at
a `:` that closes a term-mode ascription, so the site text swallows it:

```
python3 -B -c "…"   # src = 'example : Nat := (by simp : Nat)'
captured call text: 'simp : Nat'
spliced:            'example : Nat := (by explicit_rw [x at []])'
```

The `: Nat` is consumed and does not come back. No such site exists in the six
modules (I checked), so nothing in the recorded run is wrong — but this is
silent source corruption outside the intended replacement range, and it would
not be caught by the byte-identity argument because the ascription is *inside*
the site range the harness believes it owns.

Fix: stop `call_end` at a top-level `:` as well, or refuse such a site.

### 6. MINOR — invocation grouping ignores the spec fields and dedups by content
`Experiment/pipeline/replay_module.py:145-170` infers multiple invocations from
**file names** (`_NN.k.json`) and then **deduplicates variants by content**,
treating identical runs as one invocation. The spec (as just amended) defines
`invocation`/`invocations` for exactly this, and the harness reads neither
(`grep invocation Experiment/pipeline/render.py` → no match).

The content dedup is unsound in principle: two branches that genuinely record
identical steps are two invocations, and collapsing them to one lets a single
`explicit_rw` be rendered and, if it compiles, marked `replayed` — the PLAN
rule says the site counts as replayed only when **every** execution replays. On
this corpus the risk does not materialise: I checked all 16 multi-file sites and
**none** dedups to one, so the reported 16 is correct here.

```
# all 16 multi-file sites keep >1 distinct variant; collapsed-to-one: 0
```

Fix: read `invocations` from the trace; treat `invocations > 1` as multiple
regardless of content equality. See §What T1/T2 must do.

### 7. MINOR — docstring describes a line-mapping that does not exist
`Experiment/pipeline/replay_module.py:21` and `:519` say errors are mapped back
to their site "by line" / "the site whose replacement block covers that line".
No such mapping is implemented; whole-module mode assigns nothing per site and
per-site mode uses `pdiags[0]` (defect 2). The comment describes the fix, not
the code. Correcting the comment alone is not enough — implement it.

---

## Things I attacked and found sound

- **Splice safety (brief 5).** Proven for all six modules: outside the replaced
  ranges, the translated module is byte-identical to the original apart from the
  single added import. Reverse-order application is correct; offsets are
  *character* indices consistently on both sides, so Unicode is safe (the
  docstrings' "byte offset" wording is inaccurate but harmless). Column 0,
  CRLF (`\r` preserved in `trailing`), `calc`-block `by simp`, nested
  `simp (disch := simp)` and trailing `<;>` all produce correct single sites.
- **Isolation argument for `replayed` (brief 1).** `whole_module` requires exit
  0 for the entire module; `per_site` reverts every other site to the original
  call, so a clean probe isolates one site. A site whose `explicit_rw` succeeds
  but leaves a different goal *does* fail, because the whole declaration is
  compiled, not the tactic alone — I confirmed the compile unit is the file.
  A render that left `simp` in place cannot arise from `render_trace` (defect 4
  is about the missing guard, not a live hole).
- **Renderer vs SPEC (brief 4).** Fixtures in `test/Pipeline/renderer_cases.json`
  cover every step kind (`rw` fwd/rev, `args`, `local`, `prop`, `side` with
  `intros`/`pre`/`post`, `unfold`, `beta`, `eta`, `proj`, `zeta`, `iota`,
  `change` with `to`/`source`, `eq` with `by`, `congr` nested, `intro_ctx`) and
  every close form (`rfl`, `true_intro`, `assumption:`, `absurd:`, `decide`,
  `nofun`, `omega` side close, `unresolved:`). My 5 adversarial traces rendered
  correctly and **parse** in T2 at `6dc69322` (only `Unknown identifier` for my
  placeholder lemma names, i.e. the grammar accepted every construct):
  two-level nested `intros`, `congr` inside a side trace, multi-location with
  the goal closed mid-way, `omega` side + `nofun`. The `←` prop-flagged
  inaccessible local is correctly *refused* (`inaccessible_name`, side `t1`) —
  the right call, since `h✝` does not lex.
- **`check_pipeline.py`** — `OK: 179 checks`, ~5 s, passes.
- **Scope** — merge-base diff touches only `Experiment/pipeline/`,
  `test/Pipeline/`, `tracking/tasks/T4-pipeline/` and `.gitignore`. The
  `.gitignore` addition is **acceptable**: a single anchored `/out/` with a
  comment, ignoring only the harness's output directory.
- **Read-only discipline** — `--out` inside either worktree is refused,
  `--regenerate` is refused, and both worktrees' `git status` are recorded
  before and after and were clean.

---

## Attribution audit

Ten non-replayed sites re-derived from the trace JSON, the rendered text and the
compiler error, independently of the harness's guess.

| # | site | harness | my verdict | evidence |
| --- | --- | --- | --- | --- |
| 1 | `FunctionBasic` 2 (316) `name_is_syntax` | t1 | **t1, correct** | `rw.name` = `'if_neg fun h ↦ hb ⟨a, h⟩'`; spec says `<lemma or hyp name>`. Refusal is right. |
| 2 | `FunctionBasic` 6 (528) `name_is_syntax` | t1 | **t1, correct** | `name` = `'dif_pos h'`, `args` = `None`. Syntax in a name field. |
| 3 | `LogicBasic` 7 (508) `name_is_syntax` | t1 | **t1, correct** | `name` = `'heq_comm (a := a)'`. Named-argument syntax, not a name. |
| 4 | `LogicBasic` 11 (597) `name_is_syntax` | t1 | **t1, correct + worse than reported** | `name` = `'@forall_eq _ p a'` **and** `args` = `['α','p','a']`: the same arguments twice. A spec-following generator would emit them both. |
| 5 | `FunctionBasic` 17 (934) `name_is_syntax` | t1 | **t1, correct + same duplication** | `name` = `'comp_assoc g _ f'`; a later step has `name` = `'(leftInverse_surjInv hf).comp_eq_id'` with 5 `args` — a projection application, also not a name. |
| 6 | `IsEmpty` 16 (119) `compile_failed` | t1 | **t1, correct** | `prop: true`, `name: leftTotal_empty`, `args: None`, `before: 'LeftTotal R'`. `eq_true` receives the ∀-statement, not the instance. Exactly the harness's stated reason. |
| 7 | `IsEmpty` 17 (122) `compile_failed` | t1 | **t1, correct** | Same shape, `rightTotal_empty`, `pos [0,1,1]`. |
| 8 | `LogicBasic` 6 (497) `compile_failed` | t1 | **t1, correct** | `prop: true`, `cast_heq`, `args: None`, `before: 'cast e b ≍ b'`, `pos []`. |
| 9 | `FunctionBasic` 8 (683) `unresolved:` | t1 | **t1, correct** | Trace literally carries `"unresolved:discharged by rewriting to True, steps not recorded"`; 12 steps and `close: true_intro`, so the recorder classified it, not the harness. |
| 10 | `IsEmpty` 9 (68) `compile_failed` | harness | **WRONG — not a site failure** | Error is the stale-`.olean` header error at line 6, 62 lines away. Defect 2. Site is not broken. |

The 16 `multiple_invocations` attributed `harness`: **the attribution is
correct** — one `explicit_rw` genuinely cannot carry a different step list per
branch, and PLAN step 3 assigns the per-branch rendering to the renderer, so the
work is the harness's. But the *label* is incomplete: T1 must also supply the
spec fields (below). I would report these as `harness` with a `t1`
prerequisite rather than `harness` alone.

Summary: 8 of 10 correct, 1 correct but understated (#4/#5 duplication), 1
wrong (#10). Excluding defect 2, attribution is honest and the reasoning in
`attribute()` matches what the traces actually contain. I found **no** case of
a failure being blamed on T2 to flatter the harness — `t2: 0` is genuine, and
my grammar probes confirm T2 accepts every construct the renderer emits.

---

## What T1/T2 must do for multiple invocations

The spec now defines `invocation` (`k`) and `invocations` (`n`); PLAN step 3
"Rendering" defines the output form. Neither side implements it yet.

**T1 must:**
1. **Emit the fields.** Today **zero** traces carry `invocation` or
   `invocations` (`grep -l '"invocation' meas_out/*.json` → 0 of 104). The
   harness is reduced to inferring multiplicity from file names
   (`_NN.k.json`), which is not an interface. Every trace for a site executed
   `n` times must carry `"invocations": n` and its own `"invocation": k`, in
   execution order.
2. **Make the invocations distinguishable.** Each trace must identify the goal
   its execution ran on (the existing `locations[].pre` is probably enough, but
   it must be guaranteed distinct per branch), so the renderer can emit the
   PLAN rule's per-goal comment naming which alternative belongs to which goal.
3. Keep writing one file per invocation, but the file name must stop being the
   carrier of meaning — the fields are.

**T4 (the harness/renderer) must:**
1. Read `invocations` from the trace instead of counting files, and drop the
   content-dedup (defect 6): `invocations: n` means n invocations even when two
   recorded identical steps.
2. Implement the PLAN rule, which is three cases, none of which needs simp:
   - all executions recorded **identical** steps → keep `<;> explicit_rw [...]`;
   - the site is the **last tactic of its block** → emit `t` followed by one
     focused bullet `· explicit_rw [...]` per goal in execution order;
   - otherwise → `<;> first | explicit_rw [...] | explicit_rw [...]`, with a
     comment naming the goal each alternative belongs to.
   Note the first case alone would clear a share of the 16 today if the dedup
   were re-expressed as "identical ⇒ single `<;>` form" rather than
   "identical ⇒ one invocation" — same observation, opposite and correct
   conclusion.
3. Count the site replayed **only when every execution replays**, per PLAN.
4. Fix defect 3 so these sites carry their marker while they remain unrendered.

**T2 must:** nothing new for the `<;>`/bullet forms — `first` and `·` are
ordinary Lean and the tactic is unchanged. T2 should confirm `explicit_rw` is
well-behaved as a `first` alternative (fails cleanly, no partial goal mutation
on failure), since `first` relies on backtracking. That is the one new demand
the rule places on the tactic.

---

## Reproducibility

`report.json`'s commits are no longer checked out, so both tables are given.

**Recorded run** — T1 `1d8ba00b`, T2 `7ccb98b2` (dirty), 140 s:

| module | sites | replayed | unresolved | render_failed | compile_failed | mode |
| --- | --- | --- | --- | --- | --- | --- |
| `Logic/IsEmpty/Basic.lean` | 17 | 15 | 0 | 0 | 2 | per_site |
| `Logic/Nontrivial/Defs.lean` | 1 | 1 | 0 | 0 | 0 | whole_module |
| `Logic/Function/Defs.lean` | 2 | 1 | 0 | 1 | 0 | whole_module |
| `Logic/ExistsUnique.lean` | 8 | 8 | 0 | 0 | 0 | whole_module |
| `Logic/Function/Basic.lean` | 23 | 9 | 1 | 8 | 5 | per_site |
| `Logic/Basic.lean` | 31 | 11 | 0 | 18 | 2 | per_site |
| **total** | **82** | **45** | **1** | **27** | **9** | |

**My re-run** — T1 `61f59e3e`, T2 `6dc69322` (both clean), 137 s:

| module | sites | replayed | unresolved | render_failed | compile_failed | mode |
| --- | --- | --- | --- | --- | --- | --- |
| `Logic/IsEmpty/Basic.lean` | 17 | 13 | 0 | 0 | 4 | per_site |
| `Logic/Nontrivial/Defs.lean` | 1 | 1 | 0 | 0 | 0 | whole_module |
| `Logic/Function/Defs.lean` | 2 | 1 | 0 | 1 | 0 | whole_module |
| `Logic/ExistsUnique.lean` | 8 | 8 | 0 | 0 | 0 | whole_module |
| `Logic/Function/Basic.lean` | 23 | 9 | 1 | 8 | 5 | per_site |
| `Logic/Basic.lean` | 31 | 11 | 0 | 18 | 2 | per_site |
| **total** | **82** | **43** | **1** | **27** | **11** | |

The whole −2 delta is defect 2 (stale `.olean` charged to IsEmpty sites 9 and
10), not a regression in T1 or T2. Every other cell is identical across the two
commit pairs, which is good evidence of reproducibility. Both runs' denominators
should be **84**, not 82 (defect 1).

## RESULT.md honesty

Accurate on the whole, and creditably self-incriminating: it volunteers the 16
multiple-invocation sites as "Known limitation, mine", reports the over-long
line rather than hiding it behind a `set_option`, records T2's dirty tree, and
its per-site failure list matches the traces I re-derived. Specific points:

- "82 of 82" and the per-module site counts are **wrong by 2** (defect 1), and
  the claim that site detection "agrees with `check_transcription.py`" is true
  but not evidence, since both share the defective rule.
- "`replayed` is never claimed without a clean compile covering the site" —
  **true**, and I could not break it.
- "No site failed because `explicit_rw` lacks a construct" (`t2: 0`) —
  **verified**, including against T2's current commit.
- The 101-line length is fine per the brief.
- The line-mapping claim in the module docstring is not implemented (defect 7).
