# T7: smallest fail-closed declaration-oracle integration

## Decision

Use the existing declaration oracle in **source-pair mode** immediately after a
successful T4 compile.  T4 needs a thin adapter, not a second semantic
comparator: create a temporary stock companion with the same
`ExplicitLean.ExplicitRw` import that T4 adds to the translated file, invoke the
cached `simpEngineDeclarationOracle`, validate its canonical marker, and gate
the `replayed` status on both compiler and oracle success.

Do not pass the unmodified stock source directly against T4 output.  Their
direct-import lists differ (`ExplicitLean.ExplicitRw` is present only in the
translated module), so the existing oracle correctly rejects that pair.  The
companion is an adapter input, not a change to Mathlib or to the oracle's
comparison policy.

The source-pair mode is the smallest safe post-compile check for the current
T4 driver: T4's `lake env lean` compile does not publish an olean family, while
the oracle independently elaborates both source inputs with the pinned
frontend and performs the exact declaration/environment checks.  If a future
acceptance requirement is specifically about emitted olean bytes, use the
oracle's existing `--bridge-oleans` mode with fresh `-o` outputs; that is a
stronger, more expensive mode and is not needed for this integration.

## Inputs and header adapter

For each module/scope the adapter receives:

| input | provenance and invariant |
| --- | --- |
| module path and compiled module name | T4's `mathlib_rel` and canonical dotted name; both are recorded and checked |
| stock source bytes | pinned Mathlib source, never modified in place; hash before and after staging |
| translated source bytes | T4's already-spliced output, including its added `ExplicitLean.ExplicitRw` import; hash the exact file passed to the compiler |
| run directory | fresh directory outside T1/T2/package roots; all companion, logs and reports live here |
| oracle executable | `lean_toolchain_cache.py oracle`'s content-addressed binary; record path and SHA-256 |

The adapter calls T4's existing `sites.add_import` once on the stock source and
writes the result as `stock-with-explicit-rw.lean` under the run directory.  It
must verify that the translated file has exactly the original import list plus
the same import spelling/module (and no other adapter-added imports).  A
header mismatch, missing companion, source-hash mismatch, or module-name
mismatch is `oracle_adapter` failure and is never silently normalized.  The
original stock file remains available as evidence and is not the oracle input
because it would make a legitimate translated run fail on the tool import.

Both source inputs then go to the same fresh oracle process, with the same
module name.  Equalizing the direct imports also equalizes the product tactic's
meta-only declarations and extension state; the oracle still checks every
observable module declaration and environment delta rather than allowlisting
the product.

## What is reused verbatim

From `Experiment/SimpEngineDeclarationOracle.lean`:

- `checkDeclarationSets`: public declaration-name equality; same-name kind and
  metadata; definitionally equal declaration types; recursor-rule checks; and
  the explicit private/generated proof-only omission policy.
- `checkAppliedExpressions`: rejects unresolved metavariables/fvars and
  `sorryAx` in applied declarations.
- `checkAxiomSubset`: checks the transitive axiom set of every applied
  non-private/non-generated declaration is a subset of the stock set.
- `compareEnvironment`: exact direct-import order (after the adapter), LCNF
  declaration extensions, module docs, persistent extensions and
  `extraModUses`, including the existing narrowly scoped generated-proof and
  tooling filters.
- `resultJson`/`failureJson`: schema-1 canonical result and stable categories
  (`declaration_set_mismatch`, `declaration_metadata_mismatch`,
  `declaration_type_mismatch`, `declaration_value_mismatch`,
  `axiom_subset_mismatch`, `environment_delta_mismatch`, and
  `unresolved_or_sorry`).

From the existing Python protocol in
`Experiment/boundary_materialize_shard.py`:

- `_oracle_command` and the `lean_toolchain_cache.py oracle` launcher;
- `DECLARATION_ORACLE_FIELDS`/count validation and
  `_parse_declaration_oracle` (exactly one marker, schema/kind/module checks,
  success/failure count invariants);
- the log/report path-and-hash convention and the rule that a malformed
  protocol result is a failure, not a successful empty report.

T4 reuses its current `compile_in_t2`, diagnostic parser, source splicing,
simp-family lint and worktree-dirtiness checks.  The adapter only adds the
oracle gate and wrapper fields; it does not duplicate declaration comparison or
change compiler diagnostics.

## Compile and oracle flow

1. T4 renders/splices/lints exactly as today.  A render failure or unresolved
   trace has no oracle attempt and cannot become `replayed`.
2. Compile the complete translated module.  If it exits zero, run one oracle
   attempt against `(stock-with-explicit-rw, translated)` and mark every
   rendered site `replayed` only after a validated oracle `success`.
3. If the complete compile fails, do not run an oracle against the failed
   module.  Preserve T4's isolated per-site probes.  For each rendered site
   whose probe exits zero, run the oracle against the same immutable stock
   companion and that probe's exact source.  Only a successful per-site oracle
   changes that record to `replayed`; a compile failure or inconclusive probe
   remains its existing status.
4. A whole-module oracle failure is module-scoped: no individual site is
   blamed because the declaration/environment delta may have several causes.
   Every otherwise-rendered site is therefore `oracle_failed:<category>` (or
   `oracle_protocol_failed`) and the module record carries the single exact
   oracle detail.  A per-site oracle failure is attributable to that site and
   gets the same category/detail.  Never convert an oracle failure into
   `compile_failed` or claim partial replay.
5. The oracle runs after the relevant compiler success, but its source pair is
   independently elaborated in a fresh process.  Imported Mathlib oleans are
   immutable shared inputs; no package or T1/T2 worktree is written.

The existing whole-module/per-site distinction remains meaningful:
`oracle.scope = "whole_module"` means one oracle gates the complete successful
compile; `oracle.scope = "per_site"` means each clean isolated probe has its
own oracle result.  A module with no clean probe has `oracle.status =
"not_run"`, with the reason retained from T4.

## Result schema

Add this wrapper to each module report (without changing the canonical oracle
payload):

```json
"declaration_oracle": {
  "status": "success | failure | not_run",
  "scope": "whole_module | per_site | none",
  "mode": "source_pair_v1",
  "module": "Mathlib.Logic.Nontrivial.Defs",
  "stock_source": {"path": "...", "sha256": "..."},
  "applied_source": {"path": "...", "sha256": "..."},
  "runtime": {"path": "...", "sha256": "..."},
  "log": {"path": "...", "sha256": "..."},
  "report": {"kind": "simp_engine_declaration_oracle", "schema": 1},
  "failure_category": null,
  "failure_detail": null,
  "seconds": 0.0
}
```

The real `report` object must contain every canonical schema-1 field; the
abbreviated object above only shows its shape.  Each site record gets
`oracle_status`, `oracle_category`, `oracle_detail`, and `oracle_scope`; a
whole-module success may refer to the module report rather than duplicate it.
For a per-site attempt, also record the applied probe path/hash and site index.
`status` remains the primary site outcome, with these additions to its
enumeration: `oracle_failed:<canonical category>` and
`oracle_protocol_failed`.  `oracle_adapter` is reserved for pre-invocation
input/header failures.  The summary must count these separately from
`compile_failed`, `render_failed`, and `probe_inconclusive`.

Attribution is exact and intentionally conservative:

- `oracle` + canonical category for a site-scoped comparison failure;
- `oracle:module` + category for a whole-module comparison failure;
- `oracle:protocol` for missing/multiple/malformed markers, nonzero launcher
  exit without a valid failure payload, or count/schema violations;
- `oracle:adapter` for unequal headers, wrong module, stale/missing hashes or
  unsafe paths.

The canonical detail is preserved verbatim (bounded only for human summary);
the durable JSON keeps the complete validated string.  A failed oracle has
zero canonical counts by the existing protocol, and a successful report must
pass all existing count consistency checks.

## Cache and isolation rules

- Allocate a fresh run directory per T4 run and a fresh applied source path per
  per-site probe.  Never reuse an old oracle report, log, nonce or olean output.
- Build/locate the oracle only through `lean_toolchain_cache.py`; hash the
  executable after the cache check and record that hash in the wrapper.
- Reuse the immutable stock companion within one run, but include its content
  hash, translated/probe hash, module name and oracle binary hash in the
  invocation identity.  A cache hit is valid only for the exact tuple.
- Run one process per oracle comparison.  The Lean process may reuse pinned
  imported Mathlib oleans, but it must not use a previous source-pair result or
  a shared generated output family.
- Do not add a full rebuild.  Whole-module mode adds one source-pair oracle;
  per-site mode adds one only for each already-clean probe.  The optional
  bridge-olean mode, if later required, must place both `-o` families under a
  fresh scope directory and retain them until comparison completes.

## Exact focused checks

Existing positive oracle/protocol coverage (no T4 changes) is:

```sh
python3 -B Experiment/check_simp_manual_overrides.py
python3 -B Experiment/lean_toolchain_cache.py oracle \
  Mathlib.Logic.Nontrivial.Defs \
  /path/to/stock-with-explicit-rw.lean /path/to/translated.lean
```

After T4's adapter is implemented, the smallest end-to-end smoke is:

```sh
python3 -B /Users/ptsier/projects/explicit-lean-worktrees/T4-pipeline/Experiment/pipeline/replay_module.py \
  --module Mathlib/Logic/Nontrivial/Defs.lean \
  --t1 /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture \
  --t2 /Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw \
  --out /private/tmp/t7-oracle-smoke
python3 -B /Users/ptsier/projects/explicit-lean-worktrees/T4-pipeline/Experiment/pipeline/check_pipeline.py
```

The smoke must assert a module-level `declaration_oracle.status == "success"`
and that the site is `replayed` only with that gate.  A focused negative should
pass a translated file to the oracle with the *raw* stock source; it must fail
`environment_delta_mismatch` for the unequal direct imports.  Repeating the
same negative with the adapter's stock companion must reach the declaration
comparison and either succeed or report a precise semantic category.  The
existing manual-overlay check and the six-module T4 harness remain the
regression commands; neither requires a whole-tree rebuild.

## Safety conclusion and escalation

The existing oracle can safely validate T4 translated modules once the header
companion adapter is used.  Its source-pair mode does not certify exact emitted
olean serialization; that is a documented boundary, not a weakened semantic
check.  If policy later requires compiler-artifact identity, escalate to the
existing bridge-olean path rather than treating source-pair success as that
stronger claim.  No oracle category, axiom check, private-proof policy or
environment comparison may be relaxed to make a translated module pass.

