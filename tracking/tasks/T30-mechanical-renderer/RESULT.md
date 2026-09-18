# T30 mechanical rule renderer

## Result

Ported the useful T19 renderer path onto direct T22/T16/T17 metadata. Fresh
operational rewrites now select `sourceArgs[argId]` and slice its authenticated
Unicode source span, validate recorded direction and derivation provenance,
map T17 proposition preprocessing to `prop_true`/`prop_false`, and accept the
recorded T20 ite/dite operational metadata mechanically. Local evidence uses
T23 `local_ref`; side introductions and closes use deterministic
`intro_ref`/`introduced_ref` handles. No call-text argument parser, theorem
ordinal inference, proof inspection, hashes, payloads, or search remains in
the renderer. Original simp calls remain adjacent comments.

## Checks

- `lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw` — PASS.
- `python3 -B Experiment/pipeline/check_pipeline.py` — PASS, 293 checks.
- `python3 -m py_compile Experiment/pipeline/render.py Experiment/pipeline/replay_module.py Experiment/pipeline/check_pipeline.py` — PASS.
- `git diff --check` — PASS.

## Fresh seven-module gate

Report: `/private/tmp/t30-fresh-seven-final2.qsIEMt/report.json`.

| module | sites | replayed | compile-failed | render-failed |
| --- | ---: | ---: | ---: | ---: |
| `Data/Option/Basic.lean` | 7 | 7 | 0 | 0 |
| `Logic/IsEmpty/Basic.lean` | 17 | 17 | 0 | 0 |
| `Logic/Nontrivial/Defs.lean` | 1 | 1 | 0 | 0 |
| `Logic/Function/Defs.lean` | 2 | 1 | 1 | 0 |
| `Logic/ExistsUnique.lean` | 8 | 8 | 0 | 0 |
| `Logic/Function/Basic.lean` | 25 | 13 | 9 | 3 |
| `Logic/Basic.lean` | 31 | 20 | 6 | 5 |
| **total** | **91** | **67** | **16** | **8** |

Remaining render roots are one unimplemented `intro_ctx`, one deferred
`eqComm` simproc, four cache-hit records with missing derivations, and one
named-argument source span rejected by ExplicitRw's closed term grammar.
Compile roots are missing recorder scope/introduced binders, dependent forall
transport, ExplicitRw theorem application/side-frame mismatches, and a
source lambda containing an anonymous constructor (not admitted by the term
grammar). No recorder or ExplicitRw implementation file was changed.
