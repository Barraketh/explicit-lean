# T57 result

Status: partial, fail-closed. The accepted broader overlay now contains 14 safe
ordinary-Lean proof replacements. The two metadata-only Logic.Basic changes are
not accepted: `@[grind =] xor_def` and `grind_pattern Exists.choose_spec =>
P.choose` remain visibly unresolved in the source. Full Logic.Basic
certification is not claimed.

## Trust-boundary fixes

- `broader_simp_family_overrides.json` no longer has a shared source hash.
  Every entry carries and authenticates its exact `moduleSourceSha256`.
- Occurrence values are canonical `occurrence_id(module, startByte, endByte)`
  values, replacing all T57 labels. The loader rejects mismatched identities.
- Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c` and Lean
  `4.32.2/f3b06c705e6c85f5314019d5d3baab0fec5b580c` are required exactly;
  wrong-but-well-formed environment fixtures are rejected.
- Rendering preserves the source line's indentation and checks exact original
  text line by line. A synthetic UTF-8 fixture covers byte ranges, rendered
  character offsets, non-ASCII prefixes, indented multi-line calls, and
  rejection of a range splitting a code point.
- A two-module synthetic fixture authenticates different source hashes in one
  database. It adds no real second-module override.

## Counts and validation

Before this round the overlay had 16 entries. After it has 14 accepted proof
replacements and 2 unresolved metadata entries. The prior fresh generator
reproduction still has 31 direct `simp` sites unresolved; no whole-module or
whole-tree coverage claim is made.

- `python3 -B Experiment/pipeline/check_pipeline.py` — PASS, 341 checks.
- `python3 -B Experiment/check_simp_family_lint.py` — PASS, 46 tests (2
  opt-in corpus sweeps skipped).
- `python3 -m py_compile Experiment/pipeline/broader_overlay.py
  Experiment/pipeline/check_pipeline.py Experiment/pipeline/replay_module.py` —
  PASS.
- `git diff --check` — PASS.
- Fresh certification round 3, with the two metadata declarations restored,
  failed closed exactly at those two Grind metadata operations (`simpDisabled`),
  so no invalid preservation claim is made.
- A separate metadata-excluded diagnostic copy containing the 14 proof
  replacements emitted a fresh olean under the pinned simp-disabled driver:
  `.lake/private/T57-overlay-cert-round4-20260919T092058Z/Mathlib/Logic/Basic.olean`.
  Independent static lint on that copy returned rc1 with exactly two findings:
  the dormant Meta `simp symmExpr` bodies at source lines 56 and 87. These are
  source findings, not metadata findings; omitting the two unresolved Grind
  metadata operations was intentional for the diagnostic certification. The
  copy is therefore not static-clean and is not Logic.Basic acceptance
  evidence.
- The real overlay leaves all four findings unresolved and distinct: the two
  unchanged Grind metadata operations (`@[grind =] theorem xor_def` and
  `grind_pattern Exists.choose_spec => P.choose`) plus the two dormant Meta
  `simp symmExpr` bodies at lines 56 and 87. Full Logic.Basic acceptance is not
  claimed.
- Fresh no-new-axiom comparison for the same 14 proof declarations passed:
  `.lake/private/T57-no-new-axiom-round2-20260919T092119Z/no-new-axiom.json`.
  The overlay axiom sets introduced no axioms beyond stock.

Frozen evidence was only copied/read; no frozen source or receipt was modified.
