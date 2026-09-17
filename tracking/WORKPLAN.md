# Work plan and task board

Governing rule: `AGENTS.md`. Plan: `PLAN.md` direction change section.
Protocol: `tracking/COORDINATION.md`. Interface: `tracking/SIMP-TRACE-SPEC.md`.

| Task | Scope | Depends on | Status | Branch | Review |
| --- | --- | --- | --- | --- | --- |
| T0-remote-host | On demand only: Scaleway GP1-L (32 vCPU, 128 GB, $0.89/hr). Provision only when a local job fails on resources; delete when idle for an extended period and re-provision later | a local resource failure | deferred (user decision 2026-09-16) | | |
| T1-trace-capture | `simp_trace` tactic: run stock simp with instrumented methods, emit spec-v1 JSON; fixtures + Python validator | spec | implemented, review round 1 running | task/T1-trace-capture | R1 pending |
| T2-explicit-rw | `explicit_rw` positional replay tactic per spec, no simp machinery; fixtures with hand-written traces; conv reference | spec | implemented, review round 1 running | task/T2-explicit-rw | R1 pending |
| T3-compliance | Rewrite two `dsimp` overrides; simp-family lint for overrides and generated regions | none | dispatched | task/T3-compliance | |
| T4-pipeline | Per-module driver: capture traces for a module, render `explicit_rw` source with original comment, build, oracle | T1, T2 | planned | | |
| T5-cone | Run T4 on the seven-module cone (91 calls); record per-call outcomes | T0, T4 | planned | | |
| T6-readability-pass | Collapse top-level steps to `rw`/`exact`/`change` when re-elaboration matches | T2 | planned | | |

Log (newest first):

- 2026-09-16: T1 implemented (7 commits). Positions via post-hoc localisation with in-tactic validation; definitional steps recovered by `findBridge?` since simp performs them outside `pre`/`post`. Measurement on IsEmpty.Basic: 17/17 calls traced, 76 steps, 15 KB total (~0.9 KB/call) versus the rejected 7,113-line DAG. `intro_ctx`/`eta` not emitted in v1. Review round 1 dispatched.

- 2026-09-16: T2 implemented (6 commits, direct Expr navigation, dependent positions refused with error, `at *` and `intro_ctx` not implemented). Open question raised: `explicit_rw` matches up to reducible defeq, so the readability post-pass must re-verify before collapsing to `rw`. Review round 1 dispatched.

- 2026-09-16: user chose Scaleway GP1-L as the remote worker, but only if local work fails on resources; AWS ruled out (not cheaper). Pricing in tracking/tasks/research-cloud-pricing.md.
- 2026-09-16: protocol, spec and board created; T1, T2, T3 dispatched in parallel on the Mac; cloud worker pending user choice.
