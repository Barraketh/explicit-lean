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
