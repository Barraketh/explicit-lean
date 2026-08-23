# Mathlib `simp` coverage experiment

`simp_coverage.py` implements the corpus experiment from `PLAN.md` §4.1.  All
generated modules, logs, and reports are written below `.lake/simp-coverage`.

Build the syntax-aware inventory for the pinned checkout:

```sh
python3 Experiment/simp_coverage.py inventory
```

The parser walks Lean syntax nodes, so it finds tactics nested in terms and
tactic combinators.  It maintains namespace, section, and `open` state while
parsing.  If a module still requires elaboration to establish local syntax, the
script compiles a complete copy with `ExplicitLean.SimpInventory` enabled and
translates the reported byte ranges back to the original source.  The default
1,000-module batches bound parser memory.

Run isolated `simp`/`simp only` trials and resume an interrupted run with:

```sh
python3 Experiment/simp_coverage.py trials --jobs 4 --resume
```

Each occurrence is replaced in a complete module copy by `simp_explicit?`.
Successful suggestions are then materialized in a second complete copy and
compiled.  One JSON result and one full compiler log are retained per
occurrence.  Useful filters are `--module`, `--id`, and `--limit`; use
`--keep-copies` to retain every isolated source copy instead of only the
per-occurrence reports and worker copies.

After isolated trials, compile all successful replacements together per module:

```sh
python3 Experiment/simp_coverage.py aggregate --jobs 4
```

For resumable corpus closure, use the separate module-batched path.  It
records each module once, materializes one optimistic candidate module, and
uses declaration-group bisection only when that aggregate fails:

```sh
python3 Experiment/simp_coverage.py closure --jobs 4 --timeout 600
python3 Experiment/simp_coverage.py closure --resume --jobs 4
```

Closure records and summaries are written below
`.lake/simp-coverage/closure-results` and include source/inventory/recorder
fingerprints, terminal outcomes, candidate compile provenance, and actual
materialization compile counts.  `--resume` skips only complete records whose
module source, expected occurrence-ID digest, passive-recording schema, and
expected `simp` report schema still match.  A failed recording compile is a
coverage failure for every occurrence; missing reports after a successful
recording are conservatively treated as `not_reached`.  Candidate aggregate
compilation is reported independently from `candidate_plan_complete`, so an
unrelated planning failure does not invalidate candidates that compiled.

Regenerate the compact report at any point:

```sh
python3 Experiment/simp_coverage.py report
```

The machine-readable outputs are `inventory.json`, `summary.json`, individual
`results/*.json`, and `aggregate-results/*.json`.  Failures use stable category
names; `unclassified_recorder_failure` and `harness_error` are deliberately
visible so a corpus run cannot silently treat an unexplained failure as known.

`check_simp_coverage.py`, included by `Experiment/run.sh`, is the bounded
end-to-end regression.  It inventories two modules covering nested tactics and
all five tactic families, materializes a known deterministic certificate, and
compiles the corresponding aggregate module.

O6g implementation status (2026-08-22): explicit projection-function replay
locally enables Meta beta and `.yesWithDelta` projection reduction for the
pinned projection operation while leaving the recorder clone and neutral
traversal unchanged. Quasispectrum occurrence `226e61786984b7bc` now
materializes with two `reduce projection_fn Units.val` commands and six named
rules, with no fallback metrics. The focused production gate checks the stable
trace and rejects deletion, reordering, and wrong-identity mutations. Schema 15
is unchanged.

O6h implementation status (2026-08-22): exact ambient local-let expansion is
available as `reduce local_def <local>`. The operation checks the local fvar,
context index, accessible name, and stored value, and bridge synthesis proposes
it only for a continuity gap already matched to that fvar. The Directed target
`26c72cb4c4292d08` now materializes with local-def expansion followed by its
recorded zeta and named events; the focused gate rejects deletion, reordering,
and a wrong local and asserts zero fallback metrics. Schema 15 is unchanged.
