# Coordination protocol (from September 16, 2026)

The coordinator does no implementation. Implementers and reviewers are
separate agents. The coordinator reads only the compact files named here,
never agent transcripts.

## Worktrees and branches

- Main checkout: `/Users/ptsier/projects/explicit-lean`, branch
  `codex/search-free-mathlib-2026-08-31`. Only the coordinator commits here.
- Each task `T<n>-<slug>` gets a worktree
  `/Users/ptsier/projects/explicit-lean-worktrees/T<n>-<slug>` on branch
  `task/T<n>-<slug>`, created from the main branch head:
  `git -C /Users/ptsier/projects/explicit-lean worktree add -b task/T<n>-<slug> /Users/ptsier/projects/explicit-lean-worktrees/T<n>-<slug>`
- Build cache: in the worktree run
  `mkdir -p .lake && ln -s /Users/ptsier/projects/explicit-lean/.lake/packages .lake/packages`
  so prebuilt Mathlib is shared read-only. Never write into `.lake/packages`.
  The worktree's own `.lake/build` is private. Build only named modules,
  e.g. `lake build ExplicitLean.SimpTrace`; never `lake build` with no target
  and never `lake update`.
- Do not edit `ExplicitLean.lean` or `lakefile.toml`; the coordinator wires
  new modules at merge. Build your modules by explicit name.

## File ownership

Each task prompt lists the files and directories the task owns. Touching
anything else is an escalation, not a judgment call.

## Deliverables per task

Directory `tracking/tasks/T<n>-<slug>/` in the task worktree, committed on the
task branch:

- `RESULT.md` (at most 60 lines): what was built; files changed; exact check
  commands with pass/fail and runtime; known limitations; open questions.
- `ESCALATION.md` if stopped early: the blocker, what was tried, options.
- `REVIEW-<n>.md` written by the reviewer for round n.

Commit granularity: one commit per coherent step, last commit message
`T<n>: <summary>`. Final agent message to the coordinator: at most 15 lines,
status plus the RESULT.md path. No code, no logs.

## Adversarial review cycle

After RESULT.md exists the coordinator dispatches a fresh reviewer for round
n. The reviewer re-runs checks, writes `REVIEW-<n>.md`. If it is not
`NO DEFECTS`, the implementer fixes every item, updates RESULT.md, commits,
and the coordinator dispatches round n+1 with a fresh reviewer. Merge happens
only after a clean round.

## Escalation conditions (stop, write ESCALATION.md, report)

- The task needs files outside its ownership or a change to the interface
  spec in `tracking/SIMP-TRACE-SPEC.md`.
- A single Lean build or check exceeds 30 minutes or 40 GB RSS on the Mac.
- A required check still fails after three distinct fix attempts.
- The only path forward is forking or copying Lean's simp traversal, or
  calling simp machinery from product code.
- Anything else surprising that changes the plan.

## Product rule reminder

Product code (anything a translated Mathlib file will run) must not use
`simp`, `dsimp`, `simpa`, `simp_all`, `simp_rw`, `norm_num`, `field_simp`,
`push_cast`, `norm_cast`, or anything built on `Lean.Meta.Simp`. The recorder
is not product code and runs stock simp on purpose. See `AGENTS.md`.
