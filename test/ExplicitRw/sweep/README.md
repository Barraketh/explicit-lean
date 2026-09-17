Escape sweep for the `explicit_rw` whitelist grammar.

`probes.json` lists terms and the slots they are spliced into.
`Experiment/check_explicit_rw.py` generates one Lean file per (term, slot) pair,
compiles it, and classifies the outcome:

- an **escape** term must be rejected by the *parser* — Lean reports
  `unexpected token`/`unexpected identifier`/`expected token`. The whitelist is
  a parser-level fence, so a term that merely fails to elaborate would not
  demonstrate it.
- a **benign** term must reach elaboration, i.e. produce no parse error. Whether
  it then type-checks is not the sweep's business; the probe templates put terms
  in slots where most of them are ill-typed on purpose.

The sweep is the artefact behind RESULT.md's escape-count claim. Earlier rounds
reported counts from ad-hoc scratch runs, two of which turned out to be
classifier errors rather than grammar defects; committing the driver is what
makes those numbers checkable by the next reviewer.
