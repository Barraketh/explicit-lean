Each `.lean` file here uses a form that `explicit_rw` must reject. Most are
parser-level refusals for tactic slots and legacy term forms. `lean_term_by.lean`
exercises the delimited ordinary-term form: it parses as Lean, then the
macro-expanded tactic-block guard rejects it before elaboration. The harness
compiles each file and requires a nonzero exit with the expected message
fragment recorded in `expected.json`.
