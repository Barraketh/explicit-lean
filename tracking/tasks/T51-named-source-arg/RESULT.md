# T51 named source argument replay

Implemented generic replay of a T22 source argument whose exact authenticated
span is `heq_comm (a := a)` (Logic.Basic occurrence
`c28dd19f3d6d3d67`). The renderer continues to select the argument by direct
`argId`, slice its Unicode-scalar span, and check its recorded direction. It
now permits only the parenthesized named-argument form through the narrow
ExplicitRw term grammar. ExplicitRw lowers that node to Lean's native
`namedArgument` syntax and recursively lowers only the value; no call-text
parsing, source-name inference, proof inspection, or general term
serialization was added.

## Checks

From the isolated worktree `/private/tmp/explicit-lean-t51-named-source` at
base `5c153cf6560e3fc1707b8140808770986c71cf69`:

* `lake build ExplicitLean.ExplicitRw` — pass.
* `lake env lean test/ExplicitRw/NamedArgs.lean` — pass with the shared
  prebuilt Mathlib package search path.
* `python3 -B Experiment/pipeline/check_pipeline.py` — `OK: 332 checks`.
* `python3 -B Experiment/check_explicit_rw.py` — PASS (14 positive/negative
  fixtures, 14 rejected-syntax fixtures, 108 escape probes, 42 benign probes,
  and 137-theorem axiom audit; 104 escapes rejected by the parser and 4 at
  elaboration).
* `python3 -B Experiment/check_no_simp_family.py` — PASS (all four
  ExplicitRw product files scanned).
* Actual Logic.Basic site 7 (source occurrence `c28dd19f3d6d3d67`) compiled
  with its manual override table disabled. The direct T22 span rendered as
  `heq_comm (a := a) at [0, 1]`; the translated Mathlib/Logic/Basic.lean
  exited 0 with no diagnostics.

The generated replacement retains the adjacent original simp comment and
contains no simp-family tactic.
