# Work plan and task board

Governing rule: `AGENTS.md`. Plan: `PLAN.md` direction change section.
Protocol: `tracking/COORDINATION.md`. Interface: `tracking/SIMP-TRACE-SPEC.md`.

| Task | Scope | Depends on | Status | Branch | Review |
| --- | --- | --- | --- | --- | --- |
| T0-remote-host | Provision one high-RAM Linux worker (provider per user decision), install toolchain + Mathlib cache, rsync-based `remote_lake.sh` helper | user authorization | awaiting user decision | | |
| T1-trace-capture | `simp_trace` tactic: run stock simp with instrumented methods, emit spec-v1 JSON; fixtures + Python validator | spec | dispatched | task/T1-trace-capture | |
| T2-explicit-rw | `explicit_rw` positional replay tactic per spec, no simp machinery; fixtures with hand-written traces; conv reference | spec | dispatched | task/T2-explicit-rw | |
| T3-compliance | Rewrite two `dsimp` overrides; simp-family lint for overrides and generated regions | none | dispatched | task/T3-compliance | |
| T4-pipeline | Per-module driver: capture traces for a module, render `explicit_rw` source with original comment, build, oracle | T1, T2 | planned | | |
| T5-cone | Run T4 on the seven-module cone (91 calls); record per-call outcomes | T0, T4 | planned | | |
| T6-readability-pass | Collapse top-level steps to `rw`/`exact`/`change` when re-elaboration matches | T2 | planned | | |

Log (newest first):

- 2026-09-16: protocol, spec and board created; T1, T2, T3 dispatched in parallel on the Mac; cloud worker pending user choice.
