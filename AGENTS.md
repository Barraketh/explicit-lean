# Search-free Mathlib campaign

Start with `HANDOFF.md`, then `tracking/campaign.json`. They contain the current
September 10 direction and evidence. `WEEKLY.md` preserves the original
acceptance criteria; its September 8 schedule and launch sequence are historical.
`tracking/archive/` and the implementation sections of `PLAN.md` are history,
not current work assignments. Later explicit user instructions take precedence.

- Prepare the agreed bounded AWS/Linux pilot locally. No cloud resources have
  been provisioned or a cloud spending/runtime cap recorded. Do not acquire
  paid resources until the concrete launch is authorized; do not use
  explicit-lean-cloud implicitly. Never buy or redeem credits.
- Prefer Luna for bounded implementation and review; escalate unexpected Lean,
  semantic, or architectural complexity to the coordinating Sol agent.
- Perform fix-review cycles: implement, run focused meaningful checks, review
  the diff for correctness and scope, fix findings, and repeat before offering
  a change for commit. Do not claim that unrun checks passed.
- Agents share this checkout. Respect assigned file ownership. Do not revert
  other agents' edits. The coordinator stages and commits named files.
- Keep iteration fast: cache immutable inputs/results, compile affected modules
  and required dependents, and reserve full rebuilds for acceptance milestones.
- Preserve original replaced tactics as comments. No sorry/admit, new axioms,
  hidden simplifier replay, or mislabelled unobserved coverage.
- Preserve kernel-checked theorem statements and computational semantics.
  Existing architecture may change; validation must not be weakened merely to
  make a failing case pass.
- Before a new work batch, read fresh usage telemetry. The allowance following
  the September 7 reset is capped at 25%, with dispatch stopping at 22% for
  headroom. Unknown usage means no costly dispatch. No extension of this budget
  has been agreed for later windows.
- The original deadline is still enforced: `campaign_budget.py check` returns
  `deadline_reached`. Prepare an explicit bounded continuation policy before
  production dispatch; do not silently extend the date or bypass the guard.
- Count the 529 archived-v10 module reports separately from whole-tree
  acceptance (still zero). The 62 v10 cached failures are queued and therefore
  missing from `campaign_failures.py`'s queue-state-only report; use the handoff
  snapshot's failure catalog for the current baseline.
- Record completed work, reproducible checks, blockers, and next actions in the
  tracker; keep large generated trees and logs under `.lake`.
- When assigned a new private snapshot, create it and verify its absolute path
  and HEAD before editing. Existing frozen evidence snapshots are read-only,
  even if filesystem permissions permit writes. Never reuse an old invocation
  nonce or receipt for a new run. Do not alter evidence to repair a failed check.
