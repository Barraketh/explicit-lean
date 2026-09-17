# T4-pipeline: end-to-end replay harness

`Experiment/pipeline/` (Python 3, stdlib only) transcribes, renders, splices,
compiles and reports per module; `--module all` runs the six traced ones.

    python3 -B Experiment/pipeline/replay_module.py \
      --module Mathlib/Logic/IsEmpty/Basic.lean --t1 <T1> --t2 <T2> --out <dir>

`render.py` translates every spec `STEP` kind and close form, raising a named
`RenderError` with a responsible side rather than mis-rendering a field the spec
does not admit; `sites.py` does site detection (T1's rule), splicing and line
breaking; `replay_module.py` drives and attributes. Both driven worktrees stay
read-only: `--out` inside either is refused, so is `--regenerate`
(`make_traced.py` writes into T1), and each report records both `git status`es
before and after — they matched on every run. `replayed` is never claimed
without a clean compile covering the site; `compile_mode` is `whole_module` when
the whole translated module compiled clean, `per_site` when it did not and each
site was retried alone, others reverted to stock.

## Six-module run (`runs/2026-09-16/`, numbers pasted from `summary.md`)

T1 `task/T1-trace-capture` at `1d8ba00b`, T2 `task/T2-explicit-rw` at `7ccb98b2`
(T2's tree dirty; that agent was mid-edit). 140 s total.

| module | sites | replayed | unresolved | render_failed | compile_failed | mode |
| --- | --- | --- | --- | --- | --- | --- |
| `Logic/IsEmpty/Basic.lean` | 17 | 15 | 0 | 0 | 2 | per_site |
| `Logic/Nontrivial/Defs.lean` | 1 | 1 | 0 | 0 | 0 | whole_module |
| `Logic/Function/Defs.lean` | 2 | 1 | 0 | 1 | 0 | whole_module |
| `Logic/ExistsUnique.lean` | 8 | 8 | 0 | 0 | 0 | whole_module |
| `Logic/Function/Basic.lean` | 23 | 9 | 1 | 8 | 5 | per_site |
| `Logic/Basic.lean` | 31 | 11 | 0 | 18 | 2 | per_site |
| **total** | **82** | **45** | **1** | **27** | **9** | |

`check_transcription.py` passes; one trace per site, 82 of 82.

### The 37 non-replayed sites

`render_failed:multiple_invocations` 16 (harness) · `render_failed:name_is_syntax`
11 (t1) · compile, `prop` step on a quantified lemma with no `args` 4 (t1) ·
compile, unknown free variable 3 (t1) · compile, wrong position / side-goal frame
1 (t1) · compile, `unfold Ne` where the head is `Iff` 1 (t1) · `unresolved:`
classified by the recorder 1 (t1).

**t1: 21, harness: 16, t2: 0.** No site failed because `explicit_rw` lacks a
construct or rejected spec-conformant syntax.

## T1 defects the renderer refuses to paper over

1. **`rw.name` carries written syntax, not a name** (11 sites): `dif_pos h`,
   `heq_comm (a := a)`, `@forall_eq _ p a`, `if_neg fun h ↦ hb ⟨a, h⟩`.
   Corpus-wide **19** `rw` steps, of which **2 also carry `args` repeating the
   same arguments** (`FunctionBasicTraced_17`, `LogicBasicTraced_11`), so a
   spec-following generator emits each argument twice. REVIEW-9 defect 2.
2. **A `prop` step on a quantified lemma records no `args`** (4 sites):
   `eq_true leftTotal_empty` gets `∀ (R) [IsEmpty _], LeftTotal R` where the
   subterm is `LeftTotal R`.
3. **Inaccessible / hygienic names** (1): `h✝` does not lex, `h._@…._hyg.71` does
   not resolve. `rename_i` is emitted here (stock Lean, before the tactic) but
   needs a nameable reference the trace lacks (REVIEW-9 3). And (1)
   **`unfold Ne` at a position whose head is `Iff`**.

Negative fixtures also cover, unexercised here: `change.to` with `have`,
newlines or `pp.all`; `⋯` in `args`; `zeta` with a `name`.

## Known limitation, mine

**16 sites run the call once per branch**, all mid-line after a
`by_cases`/`rcases … <;>` split — `by_cases hp : P <;> by_cases hq : Q <;>
simp [hp, hq]` runs simp in four branches with four goals. T1 records one trace
per invocation; one `explicit_rw` cannot carry a different step list per branch,
so the site keeps its original call plus a marker comment, and replaying these
needs the `<;>` split into explicit cases.

One rendered line exceeds 100 characters (`Logic/Function/Basic.lean` site 11,
112: one step with a `with [...]` clause, and the syntax breaks only between
steps). No `set_option linter.style.longLine false in` is emitted — that linter
is Mathlib CI's and does not fire under `lake env lean` — so the case is
reported. Every other line is within budget.

## Checks

- `python3 -B Experiment/pipeline/check_pipeline.py` — **OK: 179 checks**, 5 s:
  every spec step kind, field and close form; the refusals; layout and splice
  rules; diagnostic parsing and attribution; the six site counts; and one real
  end-to-end run asserting the report's structure, not its counts.
- Six-module run completes in 140 s, reproducible: two consecutive runs at the
  same commits gave identical per-module counts.
- Site detection agrees with `check_transcription.py` on all six modules
  (17/1/2/8/23/31); all 82 call texts round-trip against the recorder's `call`.

## Open questions

Both worktrees moved during the task (T1 `6e39c79`→`697f16b`→`1d8ba00`, whose
REVIEW-9 C1 fix removed 10 `prop`-frame compile failures mid-run); the table is
one consistent pair of commits, so re-run after both merge. Whether per-branch
rendering of `<;>` sites belongs here or to a later task is a coordinator call:
16 of 82 sites, the largest single block.

(98 lines: the 80-line budget could not hold both the per-module table and the
per-site attribution the brief requires as the primary test signal.)
