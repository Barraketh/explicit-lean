# T5 cone preflight review 2

Reviewed commit `c3276480b95b916691ea1807807d573f05022a9a` independently.
Verdict: **major — not ready**.

## Findings

### Major

1. The corrected closure command is syntactically valid Python and reproduces
   its stated restricted walk (`source_closure_modules=61` and the sole
   non-target-to-target edge is
   `Mathlib.Logic.Relator -> Mathlib.Logic.Function.Defs`), but it is not a
   complete Lean source-import closure. Its regex accepts only `public import`
   and `public meta import`, while pinned sources contain plain imports that
   are still compilation inputs. In particular, `Logic/Function/Defs.lean:10`
   and `Logic/Function/Basic.lean:17` both plain-import
   `Mathlib.Tactic.Attr.Register`. A lexer accepting plain, public, meta and
   private forms reaches **69** Mathlib modules, not 61; the omitted plain
   edges also include `Mathlib.Tactic.ToDual` and
   `Mathlib.Tactic.Linter.Header`. Thus the design's 61-vs-69 distinction is
   not accurate as written: 61 is the public-only export closure, while 69 is
   the complete header/source closure needed for compilation (and happens to
   equal the historical runtime/driver count). The manifest requirement to
   record every source edge is inconsistent with the supplied command.

## Verified

- The seven-module count command reports `31, 8, 25, 2, 17, 1, 7`, total
  **91**; the Function.Basic hits include lines 698 and 700.
- Recomputing all header forms gives **69** modules and still exactly the
  Relator-to-Function.Defs cross edge.
- The runner/oracle fields address review 1's provenance minor and are
  compatible as a manifest-level superset of T7's source-pair wrapper, if the
  canonical T7 payload is retained and `oracle_binary` is mapped to its
  runtime identity. No separate semantic comparator is introduced.
- `git diff --check c327648^ c327648` passes; the commit is scoped to DESIGN.md.

The design is therefore not implementation-ready until the closure definition,
command, 61/69 labels, and staging/manifest contract are corrected to include
all compilation-relevant import forms (or explicitly and defensibly document a
separate public-export closure from the complete source closure).
