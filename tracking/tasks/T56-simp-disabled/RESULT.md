# T56 result

Status: completed; whole-tree acceptance is not claimed.

Implementation:
- `Toolchain/SimpDisabled/Main.lean.patch` guards pinned Lean 4.32.2's
  stock `simpImpl` and `dsimpImpl` boundaries with an uncatchable interrupt
  diagnostic, and forces the `hasSorry` warning path in `Lean.AddDecl`.
- `build.py` clones the exact pinned source into `.lake/SimpDisabled`, applies
  the reviewed patch, builds a private stage-1 compiler/runtime, and attests
  source, binary, runtime, and compiler identity hashes.
- `run.py` fails closed on missing/stale artifacts and incremental snapshots,
  forces the guard plus process-start certification snapshots, and always adds
  only `-E hasSorry`; output paths must be fresh.
- Controls cover off-mode simp, on-mode simp/dsimp, direct Meta simp/dsimp,
  `try simp`, environment mutation, `norm_num`, rw/exact/change/unfold/rfl,
  source-local option and `warn.sorry` weakening, sorry, sorryAx, and the
  documented arbitrary-axiom limitation.

Checks (fresh, 2026-09-19):
- `python3 -B Toolchain/SimpDisabled/build.py --json`: passed, warm 0.38s.
  Initial private CMake/stage-1 build completed successfully under 30 minutes.
- `python3 -B Experiment/check_simp_disabled.py`: passed, 29.41s.
- `python3 -m py_compile Toolchain/SimpDisabled/*.py Experiment/check_simp_disabled.py`:
  passed; `git diff --check`: passed.

Limitations: `-E hasSorry` rejects source `sorry` and `sorryAx`, but not an
arbitrary new `axiom`; no-new-axiom comparison remains a separate acceptance
requirement. The readable cone default path is unchanged and whole-tree
acceptance remains zero.

Commit: final commit hash is intentionally not self-recorded; its parent is
`d09d67dc83add3c5c315e25a75ff5a3132e34ae7`.
