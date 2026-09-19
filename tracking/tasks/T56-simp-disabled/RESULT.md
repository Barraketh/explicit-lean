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
  only `-E hasSorry`; certification requires exactly one explicit fresh `-o`
  output and rejects attempts to override any guard.
- Controls cover off-mode simp, on-mode simp/dsimp, direct Meta simp/dsimp,
  `try simp`, explicit Meta exception catching, environment mutation, `norm_num`,
  `simpa`, `simp_all`, `simp_rw`,
  `field_simp`, `norm_cast`, `push_cast`, rw/exact/change/unfold/rfl, Mathlib
  import compatibility, source-local option and `warn.sorry` weakening, sorry,
  sorryAx, output/incremental/override rejection, manifest-path tampering, and
  the documented arbitrary-axiom limitation.

Checks (fresh, 2026-09-19):
- `python3 -B Toolchain/SimpDisabled/build.py --json`: passed, warm 0.38s.
  Initial private CMake/stage-1 build completed successfully under 30 minutes.
- `python3 -B Experiment/check_simp_disabled.py`: passed after coordinator
  review fixes, 91.16s.
- `python3 -m py_compile Toolchain/SimpDisabled/*.py Experiment/check_simp_disabled.py`:
  passed; `git diff --check`: passed.

Limitations: `-E hasSorry` rejects source `sorry` and `sorryAx`, but not an
arbitrary new `axiom`; no-new-axiom comparison remains a separate acceptance
requirement. A coordinator control compiled the prior T55 generated
`Mathlib.Logic.Basic` through this driver: certification correctly failed on
executed simplifier calls (including calls reached through `grind`) and emitted
no olean. This is expected failure discovery, not accepted coverage. The
readable cone default path is unchanged and whole-tree acceptance remains zero.

Commit: final commit hash is intentionally not self-recorded; its parent is
`d09d67dc83add3c5c315e25a75ff5a3132e34ae7`.
