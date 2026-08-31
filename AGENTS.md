# Search-free Mathlib campaign

Read `WEEKLY.md` and `tracking/campaign.json` before choosing work. The user's
August 31 instructions, recorded there, supersede earlier roadmap choices.

- Work locally only. Do not use explicit-lean-cloud or acquire paid resources.
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
- Before starting a new work batch, check the campaign budget policy. The
  user allows all remaining usage before the September 7 reset, and at most
  25% of the next weekly allowance. After the reset, stop dispatching work at
  the conservative configured threshold; if fresh usage cannot be measured,
  do not assume permission to continue spending. Never buy or redeem credits.
- Record completed work, reproducible checks, blockers, and next actions in the
  tracker; keep large generated trees and logs under `.lake`.

- When assigned a new private snapshot, create it and verify its absolute path
  and HEAD before editing. Existing frozen evidence snapshots are read-only,
  even if filesystem permissions permit writes. Never reuse an old invocation
  nonce or receipt for a new run. Do not alter evidence to repair a failed check.
