# Search-free Mathlib campaign

Read the governing rule below, then `HANDOFF.md`, then
`tracking/campaign.json`. `WEEKLY.md` holds the acceptance criteria (criteria 3
and 6 were rewritten on September 16, 2026); its September 8 schedule and launch
sequence are historical. `tracking/archive/` and the implementation sections of
`PLAN.md` are history, not current work assignments. Later explicit user
instructions take precedence.

## Governing rule (September 16, 2026)

The deliverable removes the **simp family** from pinned Mathlib. It does not
remove elaboration. This rule supersedes every earlier reading of "search-free"
that forbade the elaborator, implicit arguments or instance synthesis.

- **Generated and override code must be ordinary Lean** that a Mathlib reviewer
  would accept: `rw`, `exact`, `refine`, `apply`, `change`, `show`, `unfold`,
  `intro`, `rintro`, `constructor`, `rcases`, `obtain`, `calc`, explicit lemma
  applications, and so on. Implicit arguments, unification, coercions and
  typeclass synthesis are handled by the elaborator as in any Mathlib proof.
  The 21 entries in `Experiment/simp_manual_overrides.json` are the model.
- **Forbidden in generated or override code:** `simp`, `simp only`, `simp?`,
  `simpa`, `simp_all`, `simp_rw`, `simp_arith`, `dsimp`, `dsimp only`,
  `field_simp`, `norm_num`, `push_cast`, `norm_cast`, and any other tactic or
  term elaborator implemented on top of `Lean.Meta.Simp`. `dsimp` is the same
  engine restricted to definitional steps; use `unfold`, `change` or `show`
  instead. Other tactics (`ring`, `omega`, `decide`, ...) are neither targets nor
  forbidden unless they invoke the simplifier.
- **Replacement targets:** every executable source `simp` / `simp only` remains
  the first milestone. The rest of the family (`simpa`, `simp_all`, `simp_rw`,
  `dsimp`, ...) is the eventual target set under the same rule.
- **Readability is part of the deliverable, not a later phase.** Do not ship
  pre-elaborated expression DAGs, encoded payloads or opaque replay artifacts
  as translated source. The boundary recorder (`simp_engine_boundary_select`,
  `ExplicitLean/SimpEngine/Boundary*`) is retained only as internal machinery:
  an oracle for the pre/post state of each call and a source of the ordered
  rewrites simp used.
- Original calls stay as adjacent comments. No `sorry`/`admit`, no new axioms,
  no weakened validation. Unresolved calls stay visibly unresolved.


- Prepare the agreed bounded AWS/Linux pilot. The user authorized only one
  `r7i.4xlarge`-class host in account 538639825139/us-west-1, within a $20
  all-in cap, 12-hour instance lifetime and 10-hour worker runtime. Do not add a
  second host or long campaign without new authorization; do not use
  explicit-lean-cloud implicitly. Never buy or redeem credits.
- Delegate substantial coverage batches to Luna at max reasoning with explicit,
  non-overlapping module/file ownership. Optimize for throughput: the worker
  writes principled ordinary Lean, self-reviews its diff, runs focused checks,
  and uses certification compilation as the primary oracle. Escalate only
  unexpected semantic or architectural complexity before broadening scope.
- Routine coverage batches do **not** require a separate adversarial reviewer
  or speculative security analysis. Fix observed compiler/test failures at the
  most general sound mechanism, rerun the affected modules and required
  dependents, and integrate when the mechanical gates pass. Do not claim that
  unrun checks passed.
- Reserve independent focused review for changes to trust boundaries: the
  patched compiler/driver, recorder semantics, source-site accounting,
  translated-import isolation, axiom checking, and acceptance gates. The
  coordinator may directly triage, fix, test, and integrate ordinary failures.
- Certification compilation uses `Toolchain/SimpDisabled/run.py`: every target
  must emit one fresh olean with stock `simp`/`dsimp` execution disabled and
  `-E hasSorry`. Keep the separate no-new-axiom comparison; compilation does
  not replace source-site accounting, adjacent original-call comments, strict
  translated-root import checks, or the remaining-call audit.
- Agents share this checkout. Respect assigned file ownership. Do not revert
  other agents' edits. The coordinator stages and commits named files.
- Keep iteration fast: cache immutable inputs/results, compile affected modules
  and required dependents, and reserve full rebuilds for acceptance milestones.
- Preserve original replaced tactics as comments. No sorry/admit, new axioms,
  hidden simplifier replay, simp-family tactics in generated code, or
  mislabelled unobserved coverage.
- Preserve kernel-checked theorem statements and computational semantics.
  Existing architecture may change; validation must not be weakened merely to
  make a failing case pass.
- Before a new work batch, read fresh usage telemetry to confirm ordinary Codex
  work is available. The former September 7 campaign-specific 25% cap and 22%
  dispatch stop are obsolete; parallel work elsewhere does not consume a local
  campaign allocation. Unknown availability or an actual rate-limit/spend stop
  still means no costly dispatch. Never buy or redeem credits.
- The original deadline is historical. The exact top-level tracker
  `deadline`/`notAfter` boundary remains immutable for the one authorized AWS
  pilot; do not extend it, bypass its guard, or dispatch from an unpublished
  authorization checkout. That closed cloud boundary does not prohibit the
  later explicitly requested local, no-cost implementation batches.
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
