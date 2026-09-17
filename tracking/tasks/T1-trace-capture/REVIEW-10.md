# T1-trace-capture: incremental merge-gate review, round 10

Reviewed T1 at `a066bc1` (clean worktree). Verdict: **MAJOR DEFECT; not
merge-eligible**. The round-9 fixes below are confirmed, but nested side-step
classification is incomplete and produces an unreplayable trace that is not
marked in the JSON. T4 also does not consume the new step-level field.

## Checks and confirmed fixes

Commands run from the T1 worktree:

```
/usr/bin/time -p lake build ExplicitLean.SimpTrace
python3 -B test/SimpTrace/check_transcription.py
python3 -B Experiment/check_simp_trace.py
```

Results: build exit 0 (4.02 s); transcription 82/82 for the six modules;
fixture/safety checker `OK: 72 simp_trace fixture(s)`; no validation failure.
The report is 82 sites, 104 invocations, 583 steps, 29 classified steps.

Focused JSON checks:

```
python3 -B Experiment/check_simp_trace.py --report
```

All ordinary top-level `rw.name` values are bare names (524 `rw` steps;
zero non-inaccessible name-shape violations); all 32 recorded argument arrays
contain no elision or unbalanced delimiters. `.stx` origin resolution is
confirmed by the name/argument fixtures and by the absence of `name_is_syntax`
failures in the replay run. The resolved-origin validator correctly classifies
the remaining `hh`/`hf` and other unreadable-origin cases.

The expected `partial_app.json` and `partial_app_deep.json` positions are
`[0,1,0]` and `[0,1,0,0]`, respectively. `side_ite_cond_false.json` and
`side_dite_cond_false.json` both have side `pre` `P = False`, post
`False = False`, close `rfl`, and the nested `h` step at `[0,1]`. This confirms
the round-9 frame, close, and partial-application fixes for those shapes.

## Primary end-to-end evidence

```
python3 -B Experiment/pipeline/replay_module.py --module all \
  --t1 /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture \
  --t2 /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw \
  --out /private/tmp/t1-review10.nOOjJB
```

The current T4 harness reports 50/82 replayed in 163.11 s: 16 harness
`multiple_invocations`, 6 T2 failures, and 10 T1-attributed failures. The
remaining T1 families are: four quantified Prop rewrites with missing explicit
arguments (`leftTotal_empty`, `rightTotal_empty`, `cast_heq`, `Decidable.em`),
two unknown-free-variable/binder cases, one `Function.curry_uncurry` extra-arg
position, one `exists_apply_eq_apply` side step, one inaccessible-name case,
and one call-level unresolved `simpHave`/discharge case.

## Major T1 defect: nested side-step verdict is not serialized

Reproducer:

```
lake env lean test/SimpTrace/FunctionBasicTraced.lean
```

This exits 1 and reports `unapplied_quantified_prop:exists_apply_eq_apply` at
source line 848. The corresponding
`test/SimpTrace/meas_out/FunctionBasicTraced_11.json` contains a
`dite_congr` side step named `exists_apply_eq_apply`, with `prop: true` and no
`args` or `unresolved` field. T2 reproduces the real failure when compiling
the T4-rendered site:

```
lake env lean /private/tmp/t1-review10.nOOjJB/per_site/FunctionBasicTraced_11.lean
```

It rejects `eq_true exists_apply_eq_apply` because the lemma retains the
unassigned explicit `f` and `a` arguments. Thus side-goal position and `rfl`
close are correct here; argument fidelity is not. T1's validator logs the
reason at call level while walking nested side events, but `buildLocation`
only attaches the returned top-level reason array to top-level events. The
JSON therefore does not visibly mark the bad side step, violating the
step-level unresolved contract and allowing a consumer to emit known-bad code.
This is a T1 major defect, not a T2 limitation.

The same serialization gap is visible for validator reasons such as
`unreplayable_rw:ne_eq` reported during side discharge at lines 797/976: those
side steps likewise have no `unresolved` field. These are in multi-invocation
sites in this corpus, but the omission is general.

## T4 integration defect

T4's renderer does not inspect `step.unresolved`. Direct reproduction:

```
python3 - <<'PY'
import json, sys
sys.path.insert(0, 'Experiment/pipeline')
import render
p = '/Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture/test/SimpTrace/meas_out/LogicBasicTraced_16.json'
d = json.load(open(p)); s = d['locations'][0]['steps'][0]
print(s['unresolved'])
print(render.render_trace(d)[0][0])
PY
```

Output includes `unassigned_explicit_argument:Subsingleton.elim`, followed by
an emitted `explicit_rw [Subsingleton.elim ...]` line. The end-to-end report
accordingly counts this known-classified step as a T2 compile failure instead
of retaining the original call as unresolved. This is a separate T4 major
defect; T1 must still serialize every nested reason before integration can be
considered sound.

## Final disposition

Round-9 side frame/close behavior, `.stx` validation, ordinary names, argument
formatting, and partial-application positions pass their focused checks. But
the missing nested-side `unresolved` serialization is a major correctness and
fail-closedness defect. **T1 is not merge-eligible.** Fix nested side/congr
validation to return and attach verdicts to the exact nested `Step`, rerun the
end-to-end replay, then request round 11.
