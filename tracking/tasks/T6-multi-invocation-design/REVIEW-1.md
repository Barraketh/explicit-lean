# T6 structural multi-invocation rendering — review 1

Reviewed commit `4077d149cd08b51b5f69ec2dc1c42b1b1747d80d` read-only. The
implementation is structurally sound for the four designed branch families:
it maps sorted invocation ordinals to depth-first binary-spine leaves, retains
branch binders and scope, duplicates the existing non-tail suffix per leaf, and
uses authenticated replacement ranges. It emits no `first`, goal search,
fingerprint dispatch, or term/expression payload. Missing, duplicate, gapped,
unsupported, and count-mismatched metadata retain the original call and fail
closed. The structural fixture compiles in T2 and the focused suite passes all
261 checks; T1 and T2 remained clean before and after the gates.

## Six-module site accounting

The fresh T6 six-module run has 84 sites. Its exact record statuses are 54
`replayed`, 19 `compile_failed`, 2 ordinary `render_failed`, 4
`structurally_refused`, and 5 `unresolved`. Thus the RESULT headline's
`54 / 19 / 6 / 5` is a manual reconciliation treating the four structural
refusals as render outcomes. The recorded T4 baseline was an older, 82-site
run at different T1/T2 tips: 45 replayed, 1 unresolved, 27 render failures,
and 9 compile failures. The two additional sites are the corrected attribute
plus same-line tactic detections; the T6 renderer turns three complete branch
sites (139, 1007, and 1015) into replayed outputs, while the remaining target
sites are retained because of trace/T2 failures. There is no lost or falsely
replayed site.

The 16 target sites map as follows (line numbers are source lines):

| outcome | sites |
| --- | --- |
| replayed (3) | `Function/Defs.lean:139`; `Logic/Basic.lean:1007,1015` |
| compile_failed (5) | `Logic/Basic.lean:552,1011,1019,1051,1055` |
| render/structural refusal (4) | `Logic/Basic.lean:899,962,987,990` |
| unresolved (4) | `Function/Basic.lean:664,796,975`; `Logic/Basic.lean:973` |

The non-replayed outcomes are expected downstream evidence: the unresolved
sites have T1 traces with no recorded steps or an unplaceable nested side goal;
the four refusals have inaccessible/syntax-only names; and the five compile
failures expose T1 trace-field defects or current T2 dependent-`∀` limits. No
failure in this table is caused by ordinal order, binder scope, suffix copying,
or splice range selection.

## Seven-module gate

The harness does support the current main T1 Option paths. I ran all seven
modules with T1 main `9600009b4690667da52650b2c4a99df2022e54c5` (including
`OptionBasicTraced.lean`) and T2 `8b57c4a008fcef73859eedbcc95f7605a58d5e8c`:
91/91 identities accepted, with 59 replayed, 21 compile failures, 2 ordinary
render failures plus 4 structural refusals, and 5 unresolved. Both worktrees
were clean afterward. Therefore RESULT.md's statement that the seven-module
gate is blocked because the T1 task worktree lacks Option is stale; it is a
bounded integration/documentation discrepancy, not a structural-rendering
failure.

One reporting defect remains: `STATUS_ORDER`/`summarize` does not include
`structurally_refused`, so both summaries omit those records (the six-module
summary displays 80/84 sites and the seven-module summary displays 83/91).
This makes the recorded headline and machine summary disagree and undercounts
the refused sites. Add an explicit structural-refused column (or an explicit,
documented render bucket) before merge.

## Verdict

**Structural implementation: PASS. Merge eligibility: HOLD.** The hold is for
the status-accounting/report discrepancy and stale seven-gate claim, not for
the 16-site branch mapping or any downstream T1/T2 failures.

## Checks

- `python3 -B Experiment/pipeline/check_pipeline.py`: PASS, 261 checks.
- T2 `lake env lean` on `/private/tmp/t6-compile.lean`: PASS.
- Fresh six-module gate: 84 sites, 54 replayed, 19 compile_failed, 6 render
  outcomes when structural refusals are included, 5 unresolved.
- Fresh seven-module gate against current main T1: 91 sites, 59 replayed, 21
  compile_failed, 6 render outcomes when structural refusals are included, 5
  unresolved.
- `python3 -m py_compile` on changed Python files and `git diff --check`: PASS.
