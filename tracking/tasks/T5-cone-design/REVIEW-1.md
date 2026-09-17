# T5 cone preflight review 1

Reviewed commit `7432defc96e750bbbc98d1345605a139d12872e3` independently. Verdict:
**not ready** pending the major closure-manifest correction below.

## Findings

### Major

1. The stated “908 distinct Mathlib source modules” closure is not reproducible
   from the pinned Mathlib source. An independent header/import walk over
   `/Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture/.lake/packages/mathlib/Mathlib`,
   with nested block comments and line comments removed, reaches **61 distinct
   Mathlib source modules** from the seven targets (including the seven targets
   and `Mathlib.Logic.Relator`). The existing static cone report likewise has
   69 modules only because it includes additional runtime/driver modules. In
   the actual source closure, the only non-target module directly importing a
   target is **`Mathlib.Logic.Relator -> Mathlib.Logic.Function.Defs`**. The
   staging strategy (exact `--deps` closure or a hash-checked full stock copy)
   remains sound, but the 908 claim and any manifest sizing based on it must be
   corrected before implementation; otherwise “exact closure” evidence is
   ambiguous.

### Minor

2. The acceptance section delegates the final oracle invocation to the T7
   source-pair adapter without giving a concrete T5 runner command or required
   per-module manifest fields. T7 specifies the adapter contract, so this is
   implementable, but T5 acceptance should explicitly require the bridge
   invocation and record the adapter/source-pair hashes.

## Independent verification

- Comment/string/attribute-aware scan: `Logic/Basic` 31 (33 lexical minus the
  two `withTraceNode \`Meta.Tactic.simp` API calls), `ExistsUnique` 8,
  `Function/Basic` 25, `Function/Defs` 2, `IsEmpty/Basic` 17,
  `Nontrivial/Defs` 1, `Data/Option/Basic` 7; total **91**. The Function.Basic
  hits include lines **698 and 700** after `@[simp]`.
- The seven Option shapes at lines **48, 56, 59, 96, 195, 198, 234** match the
  design; line 96 is term-mode under `<| by`, and line 234 follows `ext`.
- Source imports independently confirm the listed target DAG and order; the
  first four are independent, then Function.Basic, IsEmpty.Basic, Option.Basic,
  with Relator rebuilt after Function.Defs and before IsEmpty.Basic.
- Focused checks passed: `check_translated_imports.py` and T4's
  `check_pipeline.py` (194 checks). The full lint sweep was started but not
  completed within the bounded review window.

