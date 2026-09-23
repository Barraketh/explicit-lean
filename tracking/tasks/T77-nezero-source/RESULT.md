# T77 NeZero source-proposition replay

Status: implemented in private worktree `task/T77-nezero-source`, based on
`03190f9045d8459c4657c2eab045460a903a0e9f`. This is a recorder and replay
semantics fix; it has not been integrated.

## Diagnosis and change

The `NeZero.ne _` source argument is authenticated and recorded as the
`prop:false` rewrite `n = 0 → False`. Its source value is eta-expanded over the
theorem telescope, and the elaborated proof type is already `(n = 0) = False`
because simp's proposition conversion has been incorporated into that value.
The validator previously read the unapplied function type and interpreted the
whole equality proposition as the input to `prop:false`, so it could not match
the recorded redex. Proposition replay also forced typeclass synthesis before
the target had fixed the placeholder in `[NeZero ?n]`.

`rwStatementFromValue?` now applies the captured telescope before reading the
proof type and preserves an already converted `= False` or `= True` relation.
`elabProposition` now keeps synthetic arguments open through position matching,
then uses the existing instance synthesis and `closeLemmaMVars` checks. Explicit
arguments that remain undetermined still fail closed.

## Focused evidence

- `lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw`: passed.
- `python3 -B test/SimpTrace/check_t77_nezero_source_evidence.py`: passed.
  It records the exact `NeZero.ne _` shape and `Nat.zero_le _` control, checks
  authenticated source identities and polarity, renders both traces, and
  compiles both ordinary-Lean replays. The fail-closed controls reject a
  mismatched proposition and an unfilled ordinary explicit argument.
- `python3 -B test/SimpTrace/check_source_applied_arguments.py`: passed.
- `python3 -B test/SimpTrace/check_quantified_prop_replay.py`: passed.
- `lake env lean test/ExplicitRw/Provenance.lean`: passed.
- `lake env lean test/ExplicitRw/Negative.lean`: passed.
- `lake env lean test/ExplicitRw/LocalHandlesNegative.lean`: passed.
- Simp-disabled driver on the generated replay fixture, targeting a fresh
  private olean: exit 0.
- `git diff --check`: passed.

`lake env lean test/SimpTrace/EventMVarSnapshot.lean` fails alone at line 75
with `temporary-depth event gate rejected a valid outer metavariable`. The
changed functions do not touch event snapshot logic; this failure is recorded
as untriaged and no pass is claimed for that regression.

Independent focused review is required before integration because the change
updates recorder validation semantics.
