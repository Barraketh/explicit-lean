# T16 theorem-rule derivations

## Result

The recorder now captures theorem rewrites at the fork-side matcher boundary.
The new `derivation` object is term-free and retains the existing step fields.
It records source/origin and source-argument ordinal, preprocessing operations,
the fixed redex and extra-argument count, binder classifications, and discharge
provenance.  Nested discharger frames remain ordinary side traces.

## Coverage observed

Across the current `test/SimpTrace/meas_out` inventory: 111 JSON files, 593 rw
steps, and 530 derivations.  Their operation counts are: direct Eq 277, Iff /
propext 146, Not-to-False 50, Prop-to-True 43, reverse 29, and source fallback
14 (historical traces).  There are 98 source-argument ordinals, 1,016 matched
binders, 23 instance binders, and 23 discharge binders.  Fresh numbered outputs
from the IsEmpty, Function, and Logic fixtures contain no source fallback.

The fresh named cases include `leftTotal_empty` (`prop_to_true` and matched R),
`Decidable.em` (`prop_to_true` and `instance`), source `if_neg`, source/local
`Function.IsPartialInv.eq` via `H.eq`, reverse/Iff/direct Eq, and failed
discharge classifications.

## Checks

- `lake build ExplicitLean.SimpTrace` — passed (7 jobs).
- Fresh IsEmpty, Function, and Logic fixture runs — completed; expected existing
  unresolved classifications remain (the commands exit nonzero by design).
- JSON payload scan — 111 files / 593 rw steps; zero forbidden proof, term,
  expr, hash, fingerprint, DAG, or payload keys under `derivation`.
- `python3 -B Experiment/check_simp_trace.py` — 72 traces checked; 4 bounded
  user-congru side step-count differences, caused by retained nested theorem
  events.  No kernel/type mismatch was observed.
- `git diff --check` — passed.

## Bounded gap

The checker’s four side-trace count differences need a follow-up decision about
whether those nested operational events should be represented in its skeleton;
they are retained here because T16 requires nested discharge provenance.  No
generic simproc matcher or proof/term serialization was added.
