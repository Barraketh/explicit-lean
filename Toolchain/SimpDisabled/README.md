# Private stock-simp-disabled toolchain overlay

This directory contains the reviewable source patch for the pinned Lean
4.32.2 simplifier. `build.py` copies the pinned `Main.lean` into `.lake`,
applies `Main.lean.patch`, compiles the pinned stage-1 compiler and shared
runtime, and writes a manifest. It never writes to elan or package paths.
The manifest attests the exact clean-source patch result, compiler, and shared
runtime hashes. The patch also makes certification force the `hasSorry`
warning path in `Lean.AddDecl`, so a local `warn.sorry false` cannot suppress
`-E hasSorry`.

The normal compiler remains stock. `run.py` is the fail-closed driver for
certification controls: it verifies the manifest, pinned Lean identity, option
state, `EXPLICIT_LEAN_SIMP_DISABLED=1`,
`EXPLICIT_LEAN_CERTIFICATION=1`, and `-E hasSorry`, then invokes only
the private stage-1 binary. Private process-start snapshots defeat source-local
option/warning changes and metaprograms that mutate the environment; a missing
or stale artifact is an error, not a fallback. Certification output paths must
be fresh, and incremental-load snapshots are rejected.
