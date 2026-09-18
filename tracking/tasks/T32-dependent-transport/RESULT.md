# T32 — dependent-forall transport primitive

Implemented a narrow, term-free recorder-facing operation in
`ExplicitLean/ExplicitRw`:

```text
transport forall <introduced-handle> [<domain steps>]
  body [<body steps>] at [<exact position>]
```

The domain steps produce the recorded equality.  The operation constructs the
new dependent body by an explicit `Eq.rec` cast, then applies ordinary forall
congruence to the body steps.  The binder is introduced with the supplied
stable handle; body terms can use the existing `introduced_ref` form.  There is
no goal search, lemma search, name recovery, simplifier call, or serialized
term/proof input.

Focused reduced forms cover both domain polarities, a body rewrite through an
`introduced_ref`, a false branch, a true branch, and an application-valued
membership body in `test/ExplicitRw/DependentTransport.lean`.

Checks:

- `lake build ExplicitLean.ExplicitRw` — PASS
- `lake env lean test/ExplicitRw/DependentTransport.lean` — PASS
- `python3 -B Experiment/check_no_simp_family.py` — PASS (4 files)
- `python3 -B Experiment/check_explicit_rw.py` — PASS (11 fixtures, 14
  rejected-syntax cases; 135-theorem axiom audit; 110 escape probes and 40
  benign probes)

This primitive is intentionally only for dependent-forall domains/bodies.  The
existing `congr` operation remains the separate primitive for dependent
application arguments (including the Function.Basic cast shape).  Recorder
metadata and renderer wiring are out of scope for this change.
