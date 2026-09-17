# T4-pipeline adversarial review, round 2

Reviewed at `deeed5c`. Verdict: **CHANGES REQUIRED** — one major defect, no
critical defects; the REVIEW-1 fixes are not merge-eligible yet.

## Checks

- `python3 -B Experiment/pipeline/check_pipeline.py`: **PASS, 190 checks**,
  4.2s. The count is resolved: the current test registration has 151 checks
  before the end-to-end section and 39 end-to-end checks, hence 190. The
  `RESULT.md` value 189 is stale; 192 is not supported by the current code.
- Focused Python repros: **PASS** for attribute-plus-tactic detection (including
  the two `Function/Basic.lean` sites at lines 698 and 700), exclusion of
  `Simp.simp` API text, type-ascription preservation, in-block diagnostic
  selection/probe-inconclusive behavior, replacement lint gating, invocation
  metadata, and one retained mid-line marker. A temporary transcriber fixture
  confirmed identical trace files are retained as two invocations.
- The six-module harness was **not rerun**: T1 is not a stable external
  precondition (`task/T1-trace-capture` at `db97d8f`, with
  `ExplicitLean/SimpTrace/Tactic.lean` modified); T2 is clean at `8b57c4a`.
  The old six-module result must not be treated as this review's evidence.

## Major defect

### M1 — same-line retained mid-line markers corrupt each other

`S.splice` processes replacements right-to-left, but for a mid-line
multi-line replacement it recomputes `line_start` in the already-modified
string while still slicing with the original `site.start`/`site.end` offsets.
With two retained sites on one line, e.g.

```lean
  exact foo <;> simp [foo] <;> simp [bar]
```

the result contains a mangled comment such as
`-- explicit_rwsimp [foo]ed: ...`; one marker is no longer standalone or
recognizable. This violates the REVIEW-1 marker guarantee and makes the
retained-site lint evidence ambiguous. The six current modules have no line
with two sites, so this is a general pipeline defect rather than a failure of
the stale six-module run. Fix by making same-line marker insertion atomic (or
grouping markers before applying offset-based replacements), and add a fixture
with two retained sites on one line.

No other critical or major defect was found. After M1 is fixed, a fresh round
must rerun the full checks; the six-module harness should wait for a clean T1.
