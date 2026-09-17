# T17 consumer-side proposition provenance

Implemented positional `prop_true` and `prop_false` rule applications in
`ExplicitLean/ExplicitRw/Tactic.lean`.  The selected redex is navigated first;
then leading ordinary binders are opened, the resulting proof type is unified
with that proposition (or its negation), class instances are synthesized, and
remaining proof binders are closed through the existing ordered `with [...]`
side-proof machinery.  The replacement is built with `eq_true`/`eq_false`.
No serialized terms, proof fallback, search, `let` primitive, or simp metadata
is used.

Focused coverage is in `test/ExplicitRw/Provenance.lean` (14 examples): the
five requested quantified proposition rules (`leftTotal_empty`,
`rightTotal_empty`, `exists_apply_eq_apply`, `cast_heq`, `Decidable.em`), a
false proposition, exact and recursive side evidence, and the six requested
fixed-redex rules (`if_neg`, `dif_pos`, `IsPartialInv.eq`, both `extend_apply`
forms, and `Subsingleton.elim`).  Missing proposition proof evidence is pinned
in `test/ExplicitRw/Negative.lean`.

Checks (all pass):

* `lake build ExplicitLean.ExplicitRw` (clean, ~4 s)
* `python3 -B Experiment/check_explicit_rw.py` (8 fixtures, 13 rejected cases;
  ~300 s, including the default escape sweep)
* `python3 -B Experiment/check_no_simp_family.py`
* `git diff --check`

Before → after: 0 dedicated T17 provenance fixtures → 14 focused provenance
examples (11 requested sites plus false/side/instance coverage).
