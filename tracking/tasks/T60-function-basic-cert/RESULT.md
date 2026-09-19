# T60 result

Status: completed as a strict dependent-probe review. No owned product-code
fix was needed; the earlier dependent `rc245` was not reproduced after fresh
exact-cone staging and complete-family replacement. No cloud, package cache,
frozen evidence, or compiler build was changed.

## Existing slice

- The branch's 13 authenticated `Mathlib/Logic/Function/Basic.lean` overlay
  entries and `ExplicitLean.Grind.Metadata` `Function.update` registration
  remain unchanged.
- The prior Function.Basic source/replay, pipeline, lint, and no-new-axiom
  evidence remains represented by the preceding T60 implementation commit.
  This review did not broaden proof scope or alter those files.

## Strict dependent review

A fresh private source tree was made from the reviewed 69-module/134-edge
closure. The two generated roots were produced by the accepted main replay
path, with `/Users/ptsier/projects/explicit-lean` supplied as both T1 and T2;
Logic.Basic replay reported 31/31, while Function.Basic's replay diagnostics
were retained without being used as strict-pass evidence. Stock artifacts were
staged only from
`/Users/ptsier/projects/explicit-lean/.lake/packages/mathlib/.lake/build/lib/lean`.
The staging contained 483 files for the complete 69-module closure. No hard
links or full Mathlib build tree were copied.

Before each replacement, every stale Logic.Basic, Function.Basic, and chosen
dependent family member (`.olean`, `.ir`, `.olean.private`,
`.olean.server`, and hashes/siblings) was removed. Fresh outputs were then
built with the read-only accepted driver:

```text
python3 -B /Users/ptsier/projects/explicit-lean/Toolchain/SimpDisabled/run.py -- -R /tmp/T60-strict-review-20260919T062636/source -o /tmp/T60-strict-review-20260919T062636/translated-root/Mathlib/Logic/Basic.olean /tmp/T60-strict-review-20260919T062636/source/Mathlib/Logic/Basic.lean
python3 -B /Users/ptsier/projects/explicit-lean/Toolchain/SimpDisabled/run.py -- -R /tmp/T60-strict-review-20260919T062636/source -o /tmp/T60-strict-review-20260919T062636/translated-root/Mathlib/Logic/Function/Basic.olean /tmp/T60-strict-review-20260919T062636/source/Mathlib/Logic/Function/Basic.lean
python3 -B /Users/ptsier/projects/explicit-lean/Toolchain/SimpDisabled/run.py -- -R /tmp/T60-strict-review-20260919T062636/source -o /tmp/T60-strict-review-20260919T062636/translated-root/Mathlib/Logic/IsEmpty/Basic.olean /tmp/T60-strict-review-20260919T062636/source/Mathlib/Logic/IsEmpty/Basic.lean
```

All three returned **0** (1.34s, 1.21s, 0.74s respectively), with fresh
four-file output families and empty diagnostics. `IsEmpty.Basic` is the
reviewed cone dependent that directly imports Function.Basic; its fresh strict
compile therefore passed without a segfault. The first-match audit over all
69 modules found 69/69 resolved from the translated root. The retained compact
evidence is under `.lake/private/T60-review/evidence/`.

As a bounded diagnostic control, the next build-order module was attempted
with the same exact command shape:

```text
python3 -B /Users/ptsier/projects/explicit-lean/Toolchain/SimpDisabled/run.py -- -R /tmp/T60-strict-review-20260919T062636/source -o /tmp/T60-strict-review-20260919T062636/translated-root/Mathlib/Logic/ExistsUnique.olean /tmp/T60-strict-review-20260919T062636/source/Mathlib/Logic/ExistsUnique.lean
```

It returned **1**, not 245, with the expected unresolved broader-family guard
at source line 172 (`explicitLean.simpDisabled: stock simp engine execution is
forbidden`). It was not counted as a cone pass and was not fixed here.

## Diagnosis and cleanup

The prior failing root contained 90,965 files / 5,972,959,216 bytes, rather
than the reviewed closure's 483 staged artifact files / 73,260,152 bytes. It
was removed before this run; a compact removal manifest is
`.lake/private/T60-review/removed-root.json`. The fresh exact closure, translated-root-first audit, complete family cleanup,
and successful direct dependent probe support stale/mixed and overbroad output
staging as the cause of the old `rc245` (with incompatible artifact-family
state a contributing possibility). No Function.Basic module defect was
observed, and no incompatible compiler identity was used in this run. This is
a diagnosis, not a claim that the whole cone or whole tree is accepted.

Disk availability was about 30 GiB after cleanup. All new generated source and
outputs were kept below the fresh `/tmp/T60-strict-review-20260919T062636`
path; only compact manifests and diagnostics were retained under the worktree
`.lake/private` path.

## Checks

- Fresh strict Logic.Basic, Function.Basic, and direct IsEmpty.Basic dependent:
  **rc 0**, exact commands and diagnostics recorded above.
- First-match translated-root resolution: **69/69**.
- Next build-order control ExistsUnique: **rc 1**, expected unresolved simp
  diagnostic; no segfault claimed.
- `git diff --check`: run before commit below.
