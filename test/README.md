# Test suite

Run the complete local suite with:

```bash
lake exe explicit-lean-test
```

or equivalently `./test/run.sh`, which builds first and then runs the same
harness.

The harness drives the built `explicit-lean` executable as a subprocess so that
what is tested is the command's real observable behavior: exit status, the exact
diagnostic bytes on standard error, and the artifact bytes it publishes.

## Layout

```text
test/
  cases/            one directory per case
    <case>/
      cmd           command-line arguments, one per line (see below)
      pkg/          source package root, when the case needs one
      expected/
        exit        expected exit status
        stderr      expected standard error bytes
        artifacts/  expected published tree, when the case succeeds
```

`cmd` holds one argument per line with blank lines and `#` comments ignored.
Two placeholders are substituted at run time:

- `@PKG@` — the case's `pkg` directory
- `@OUT@` — a fresh empty output directory for the case

Both are absolute paths that differ per run, so `expected/stderr` must not
contain them. This is also what the diagnostic contract requires: diagnostics
carry package-relative paths and no absolute paths.

## Case kinds

A case is **positive** exactly when its `expected/exit` is `0`, and **negative**
otherwise. The kind is taken from the expectation, not from what the command
actually did, so a positive case that regresses into failing still runs every
check a positive case owes rather than quietly becoming a negative one.

For a positive case the harness compares the published tree against
`expected/artifacts` byte for byte, then runs the command a second time into a
separate clean output directory and requires the two published trees to be
byte-identical, which is the determinism requirement from
[PLAN.md](../PLAN.md#deterministic-compilation).

For a negative case the harness requires the expected nonzero exit status, the
expected diagnostics, and that nothing at all was published.

## Updating expectations

`./test/run.sh --accept` rewrites every case's `expected/exit`, `expected/stderr`,
and `expected/artifacts` from the current behavior. Review the resulting diff
before committing: accepting is how a real regression becomes a golden file.
