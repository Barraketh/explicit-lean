# Explicit Lean

Explicit Lean is a source-to-source translator for proof bodies. Its current
target is every source `simp` and `simp only` tactic occurrence in the pinned
Mathlib corpus. The translator replaces each occurrence with generated
`simp_engine_apply` source while leaving the surrounding tactic script intact.

The active correctness rule is:

> Reproduce the externally visible proof state after each `simp` call, without
> reproducing the internal simplifier execution.

The original `simp` may run while the translator records its result. The
generated replacement must apply checked result expressions, proofs, and
continuation-visible state changes without running `simp`, a simproc, or a
discharger.

## Start here

Read these documents in order:

1. [PLAN.md](PLAN.md) is the authoritative goal, correctness contract, current
   status, prototype specification, and roadmap.
2. [simprocs.md](simprocs.md) explains the few simproc-related boundary risks
   that the prototype must test.
3. [REPORTS.md](REPORTS.md) describes durable validation-report storage.
4. [SIMP_ENGINE_COVERAGE.md](SIMP_ENGINE_COVERAGE.md) is the frozen contract for
   the existing schema-27 operational-replay implementation. It is historical
   engineering evidence, not the active product specification.

If these documents conflict, `PLAN.md` controls the boundary-state project.

## Current state

This branch is the project restart and its own engineering lineage. Do not use
`main` as a baseline for scope, completeness, or project decisions.

The repository currently implements schema-27 operational recording and replay.
That implementation has a passing focused gate, but it does **not** implement
the active boundary-state design. In particular, the existing
`simp_engine_apply` parser in `ExplicitLean/SimpEngine/Source.lean` still accepts
schema-27 certificates and invokes the replay engine. The shared name must not
be mistaken for completion of the new tactic.

The next engineering milestone is the focused boundary prototype described in
`PLAN.md`. Until that prototype adds its own test entry point, there is no test
command that demonstrates the active goal.

## Pinned environment and basic checks

The project uses Mathlib `v4.32.2`, resolved in `lake-manifest.json` to
`905b95818eb32af7874a58b427f50c1711a5e96c`, and Lean 4.32.2 commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`.

From the repository root:

```sh
lake build ExplicitLean ExplicitLeanMathlibAudit
python3 Experiment/check_simp_engine_review.py
```

The Python command checks the reviewed schema-27 implementation and its frozen
legacy contract. `Experiment/run.sh` runs the complete legacy schema-27 focused
gate. Both are regression protection for reusable code and historical evidence;
neither is the acceptance gate for the boundary-state translator.

## Repository map

- `ExplicitLean/SimpEngine/Inventory.lean` and
  `Experiment/simp_engine_inventory.py`: syntax-aware occurrence inventory,
  stable source ranges, occurrence IDs, and compositional head rewriting. The
  current inventory deliberately over-approximates: it does not yet prove that
  an occurrence belongs to a Prop-valued proof body or distinguish executable
  tactic syntax from every quotation. The boundary harness must add that scope
  classification.
- `ExplicitLean/SimpEngine/Recording.lean`: stock `Meta.simpGoal` oracle and
  goal/hypothesis transport patterns. Its current recorder is coupled to schema
  27 and should be mined, not adopted as the new artifact format.
- `ExplicitLean/SimpEngine/Fingerprint.lean`: reusable expression, proof-state,
  and options fingerprint components; the combined boundary selector still
  needs its own reviewed definition.
- `ExplicitLean/SimpEngine/Source.lean` and
  `ExplicitLean/SimpEngine/Replay.lean`: current schema-27 materialization and
  replay. These are legacy implementation, not the target apply path.
- `Experiment/check_simp_engine_source.py` and
  `Experiment/simp_engine_cloud.py`: complete-module materialization and corpus
  harnesses that can be adapted after the focused prototype works.
- `ExplicitLean/SimpEngine.lean`, `IR.lean`, `Runtime.lean`, and
  `SemanticSimproc.lean`: operational-replay research. Extend them only if a
  measured effect escapes the `simp` boundary and cannot be represented by a
  generic boundary transformation.

## Terminology

- **Source occurrence:** one parsed, in-scope `simp` or `simp only` tactic node,
  identified by module and stable source range.
- **Dynamic execution:** one elaboration-time execution of a source occurrence;
  an occurrence may execute zero, one, or several times.
- **Boundary state:** the continuation-visible tactic/elaboration state
  immediately before or after one dynamic execution.
- **Boundary variant:** the transformation recorded for one distinguishable
  pre-call boundary state and outcome.
- **Boundary artifact:** the closed generated data/source containing all
  variants for one occurrence. Older documents call the schema-27 equivalent a
  *certificate*; new code should prefer boundary terminology.
- **Recording:** running stock `simp` during translation to capture an oracle
  result and boundary delta.
- **Materialization:** rewriting source occurrences to `simp_engine_apply` and
  compiling the copied module with the original continuation unchanged.
- **Closed-world closure:** successful translation and compilation of every
  in-scope occurrence under the pinned corpus, toolchain, and build procedure.
