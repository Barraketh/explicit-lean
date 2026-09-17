# T21 congruence-only integration

Integrated onto main `3953012ca54634beb2e8b63fec0f5d84925edd2c` in the isolated
worktree `/Users/ptsier/projects/explicit-lean-worktrees/T21-integration`.
Cherry-picked implementation/fixture commits `8c35b7c` and `0ab98c3` only;
review documents were excluded. The integration preserves main's T20
`reduceIte`/`reduceDIte` implementation without overlap. No
`simpMatchOperational` wrapper or duplicate `recordTriedSimpTheorem` path is
present.

Checks:

- `lake build ExplicitLean.SimpTrace` — pass.
- `lake env lean test/SimpTrace/T21MissingRulePaths.lean` — pass; exactly two
  fresh T21 outputs.
- `python3 -B Experiment/check_simp_trace.py` — pass; 76 skeletons and path
  containment.
- T21 recursive payload scan — pass; 7/7 `rw` derivations, 2/2 user
  congruence records with `source: "congr"`, no forbidden payload keys.
- `lake env lean test/SimpTrace/T20IteSimproc.lean` — pass.
- `python3 -m py_compile Experiment/check_simp_trace.py` — pass.
- `git diff --check 3953012..HEAD` — pass.
