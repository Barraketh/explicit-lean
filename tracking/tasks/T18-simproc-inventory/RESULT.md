# T18 simproc inventory (91-site corpus)

## Evidence and reconciliation

The acceptance authority is the fresh T6 report
`/private/tmp/t6-seven-review2/report.json` (SHA-256
`5b8e385d38aa7fb117ffa6deb5d3c9f4438016e1fd3078937bf92af4d9bd60cd`), with
113 final and 113 raw invocation JSONs.  Raw/final source counts agree exactly.
T4's committed report is the older 82-site baseline (45 replayed, 16
`multiple_invocations`, 11 `name_is_syntax`, 9 compile failures, 1 unresolved),
so it supplies history/status only, not a second trace population.  T16's v1
`test/SimpTrace/meas_out` has 111 invocation JSONs and independently counts
16/16/1; its two extra branch-selector firings are duplicate Function.Basic
invocations (sites 13 and 17), and are not added to T6's 91-site totals.

## Counts (T6, deduplicated by site; nested side traces included)

| source | steps | sites | modules | site replay status | failure depends on source |
|---|---:|---:|---:|---|---|
| `reduceIte` | 15 | 6 | 2 | 2 replayed; 1 unresolved; 3 render-failed | yes, 4/6 sites (T1 side-trace metadata) |
| `reduceDIte` | 15 | 8 | 2 | 1 replayed; 1 unresolved; 2 render-failed; 4 compile-failed | yes, 7/8 sites (T1/T2 side/proposition replay) |
| `eqComm` | 1 | 1 | 1 | 1 render-failed (`bad_eq_by`) | yes; its `eq` step is unresolved |

`reduceIte` sites are Logic.Basic 21, 22, 23, 25 and Function.Basic 6, 17.
`reduceDIte` sites are Logic.Basic 17, 19, 20, 24, 26, 27, 28 and
Function.Basic 13.  `eqComm` is Function.Basic 10.  T6's 91 status records
reconcile to 59 replayed, 5 unresolved, 6 render-failed, 0 structurally
refused, and 21 compile-failed.

The current failures are not evidence of a wrong branch-selection operation:
the failures are recorded as inaccessible/syntax side names, omitted nested
side steps, a `prop` mismatch, or explicit-rw rejection.  `eqComm` fails because
its replay proof is `unresolved:simproc:eqComm` rather than `rfl`/`decide`.

## Implementation classification and recommendation

* **A — recommend `reduceIte` and `reduceDIte`.** Lean 4.32.2
  `Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean:14-40` simplifies the
  condition, then selects an ordinary `ite_cond_eq_true/false` or
  `dite_cond_eq_true/false` theorem (the dependent case applies
  `of_eq_true/false` and beta-reduces).  Both are common in these sites and
  fit the existing fixed-redex + proposition/defeq/decide language; no new
  operation is needed.
* **C — defer `eqComm`.** The corpus fixture's custom simproc
  (`test/SimpTrace/LogicBasicTraced.lean:44-79`) recursively runs `simp` on a
  swapped equality and composes `eq_comm_eq`; it is neither a fixed-redex
  operation nor common (one site).  Do not add a generic operation for it.

Checks: JSON walk/reconciliation of T6 raw/final and T16 `meas_out` (PASS,
<1 s); source inspection above (PASS); `git diff --check` (PASS).
