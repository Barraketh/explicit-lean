# T20 review 2 — PASS

## Verdict

**PASS for the bounded `reduceIte`/`reduceDIte` fix.** The applied-redex
regression from REVIEW-1 is fixed. The semantic record is rooted at the
conditional core, while every shared trailing application argument contributes
one trailing `0` position and is reported in both `RuleDerivation.extraArgs`
and `SimprocDerivation.extraArgs`. No whole-corpus coverage credit is claimed.

## Checks

- `lake build ExplicitLean.SimpTrace`: **PASS**.
- `lake env lean test/SimpTrace/T20IteSimproc.lean`: **PASS**.
- Focused probes `check_simp_engine_ite.py`, `check_simp_engine_dite.py`,
  `check_simp_engine_simproc.py`, and `check_simp_engine_replay.py`: **PASS**.
- Clean-output `python3 -B Experiment/check_simp_trace.py`: **PASS**, 74/74
  fixture skeletons and containment checks. The first invocation was
  intentionally discarded because ignored stale `.1`/T20 outputs are treated
  as extra traces by this checker.
- `python3 -B test/SimpTrace/check_transcription.py`: **PASS**, 91/91 source
  sites across the seven traced modules.
- `git diff --check`: **PASS**.

## Applied and nested semantics

Fresh T20 output has the applied `ite` and `dite` records at `[0,1,0]`, with
`before`/`after` equal to the conditional core (`if p then f else g` → `f` and
`dite p f g` → `f ⋯`). Both derivation layers report `extraArgs: 1`. The
two-argument nested `dite` corpus fixture records `[0,1,0,1]`; its conditional
firings have no trailing application, so `extraArgs: 0` is correct. The
trimming helper compares each peeled `beforeArg` and `afterArg` structurally;
the committed changed-tail `#guard` fails closed. Non-conditional cores,
non-branch `ite` results, missing condition traces, condition placement
failures, and non-`True`/`False` closures all call `markUnresolved` before any
semantic record is emitted.

The fresh nine T20 traces cover 6/15 inventoried `reduceIte` steps and 3/15
inventoried `reduceDIte` steps (the accepted T18 baseline is 15+15). This is
focused observed coverage only; no fresh 91-site inventory or corpus replay
credit is asserted.

## Payload, stock parity, and cache behavior

The nine fresh JSON traces contain the stock `before`/`after` expressions and
no proof, term, encoded-payload, or DAG fields. The bounded emitter uses the
stock `Simp.Result.expr` for parity but deliberately does not inspect
`Simp.Result.proof?`; ordinary generic simproc classification remains
unchanged, and the generic simproc/replay probes pass. The nested-occurrence
fixture exercises a cached-origin firing: the inner occurrence remains a
normal `rw` with its assumption side close, while source attribution is absent
when the cache supplies no origin. Missing or malformed cached condition
evidence follows the existing fail-closed unresolved path rather than being
invented as a successful bounded record.

No source files outside the T20 recorder/types/fixture and result evidence are
changed by the reviewed commit.

