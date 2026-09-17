Each `.lean` file here uses a form that `explicit_rw` must reject at the
**parser**, before elaboration: a forbidden tactic in the `then` closer or in
`eq ... by`. Parse errors cannot be pinned with `#guard_msgs`, because parsing
fails before the command elaborates, so `Experiment/check_explicit_rw.py`
compiles each file and requires it to fail with the expected message fragment
recorded in `expected.json`.
