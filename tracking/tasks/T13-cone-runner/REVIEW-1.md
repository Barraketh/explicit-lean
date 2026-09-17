# T13 strict readable-cone runner review 1

Reviewed commit `7b51fcce2f0802039a0ad3aab1c0f5ffbab48cea` independently. Verdict:
**major — not ready for the cone acceptance gate**.

## Finding

### Major: successful compile does not prove a fresh output

`_compile_module` stages the stock target `.olean` before compiling it, then
only checks the compiler return code and that the output path exists. It does
not remove the pre-existing stock output or verify that the invocation
rewrote it. A successful launcher that emits no output (or leaves a truncated
old output) is therefore reported as `status: passed`, and the report's
`family` can consist of stale staged artifacts. This is easy to reproduce
without Lean by replacing `run_pinned_lean` with a zero-returning no-op while
pre-populating `translated-oleans/Mathlib/Logic/Basic.olean`; `_compile_module`
returns passed and the bytes remain unchanged. Remove/rename the target family
before each compile (or record and compare output freshness/content) and
require the full expected emitted family after success. Keep a failed module's
status/diagnostic in the JSON report.

## Verification

- The lexer fixture passed all six supported header forms (`import`, `meta`,
  `public`, `public meta`, `private`, `private meta`) while ignoring nested
  comments, strings and attributes. The real pinned source walk produced
  **69 modules / 134 edges** with kinds `public import` 96, `public meta import`
  30 and plain `import` 8.
- Independent closure checks passed. Target-to-target edges match the reviewed
  DAG; the only non-target-to-target edge is
  `Mathlib.Logic.Relator -> Mathlib.Logic.Function.Defs`, and the runner's
  order rebuilds Relator at position 5 before Function.Basic, IsEmpty.Basic
  and Option.Basic.
- Real staging/preflight against the pinned T1 Mathlib cache passed: all 69
  modules staged with **483 regular artifact-family files**, all requested
  modules resolved from the translated root, and every stock Mathlib search
  root was excluded. A one-module real pinned compile emitted the expected
  seven-file family. The stock-fallback/symlink guards in
  `check_translated_imports.py` were inspected but not run here because this
  worktree has no Lake cache and invoking Lake would clone Mathlib.
- `python3 -B Experiment/check_readable_cone.py` passed 3 tests;
  `python3 -B Experiment/check_simp_family_lint.py` passed 46 tests (3 opt-in
  corpus tests skipped); `py_compile` passed. `git diff --check HEAD^ HEAD`
  reports one pre-existing extra blank line at EOF in `check_readable_cone.py`.
- JSON outcome reporting works for missing modules inside an existing source
  root, but a missing `--source-root` is rejected before the `try/finally` and
  produces no manifest; this is a minor robustness gap outside the major above.

