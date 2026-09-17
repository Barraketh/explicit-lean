# T2-explicit-rw — adversarial review, round 9

Verdict: **NO CRITICAL OR MAJOR DEFECTS in the round-8 fixes.** The four
requested merge-gate points are independently verified below. Two minor,
non-tactic items remain for coordinator disposition: the known T1/T2 `zeta`
schema mismatch and the RESULT.md length cap.

## Round-8 verification

1. **Axiom audit: fixed.** `Experiment/check_explicit_rw.py` parses every
   `#print axioms` report, requires exactly one report per discovered theorem,
   and rejects anything outside `{propext, Quot.sound, Classical.choice}`.
   I created a scratch fixture with
   `namespace ExplicitRwTest.Injected`, a named
   `axiom named_injected_axiom : (1 : Nat) = 2`, and a theorem using it. Calling
   `run_axiom_check` returned exit 1 and named
   `ExplicitRwTest.Injected.named_injected_axiom`; this is an in-namespace
   injection, not the invalid-after-`end` injection from round 7.

2. **Structured sweep slots: fixed.** `probes.json` gives `sideproof` and
   `congrnest` goals the application structure required by `[0, 1]`; the
   generated step is last, so no trailing tactic can be absorbed as an
   argument. I compiled both post-parse escapes (`admit`, `$x`) in all six
   slots (12 probes). All 12 exited nonzero and had either an `explicit_rw:`
   diagnostic or the expected unknown-identifier diagnostic. In particular,
   both previously-vacuous slots now report the probe's own rejection:
   `admit` is named by `elabStrict`, and `$x` is named by the antiquotation
   guard. The classifier also now requires nonzero exit plus attribution.

3. **`rename_i`: fixed.** `Tactic.lean` documents that `rename_i` names the
   last *n* inaccessible hypotheses in context order, and the `Lemmas.lean`
   fixture introduces two and uses the earlier one after `rename_i h₁ h₂`.
   The fixture passes in the focused checker.

4. **Step-forms documentation: fixed.** The module's complete table now
   covers every spec step kind (`rw` directions/args/side/prop, `unfold`, all
   reductions including one-step `iota`, `change`, `eq`, and `congr`), location
   and close rendering, recursive `with`/`then` side proofs, inaccessible-name
   convention, and the deliberate `intro_ctx`/`at *` refusals. I compared it
   against `tracking/SIMP-TRACE-SPEC.md` and the parser declarations.

## Minor findings (non-blocking for this T2 gate)

### M1 — T1 emits a `zeta` name that the spec and T2 do not define

The raw T1 trace `zeta_delta_at_hyp.json` contains
`{"kind":"zeta", "pos":[1,0], "name":"g"}`. The v1 spec has no `name`
field for `zeta`, and T2's `zeta at [...]` syntax cannot consume one. This is
the previously recorded coordinator decision, not a T2 implementation defect;
reconcile the schema or T1 emission before T4 consumes such traces.

Reproducer/inspection:

    rg -n '"kind":"zeta".*"name"' /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture/test/SimpTrace/out/zeta_delta_at_hyp.json
    rg -n 'syntax explicitRwRed|"zeta"' ExplicitLean/ExplicitRw/Tactic.lean tracking/SIMP-TRACE-SPEC.md

### M2 — RESULT.md still exceeds the protocol's 60-line cap

`wc -l tracking/tasks/T2-explicit-rw/RESULT.md` reports 119 lines. This is
documentation/process only and does not affect tactic soundness or the checks.

## Checks run

    lake build ExplicitLean.ExplicitRw                         PASS (1.4 s)
    python3 -B Experiment/check_explicit_rw.py                 PASS (7 fixtures, 13 rejected cases; 274.0 s)
    python3 -B Experiment/check_no_simp_family.py              PASS (3 files; 0.04 s)
    git diff --check                                           PASS

The focused checker reported 112 theorem reports within the axiom allowlist,
and its default 2/6-slot sweep reported 110/110 escape probes rejected and
40/40 benign probes parsed. The independent 12-probe all-slot post-parse sweep
and the named in-namespace axiom injection were also run as described above.
