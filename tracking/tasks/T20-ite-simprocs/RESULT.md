# T20 bounded `reduceIte`/`reduceDIte` slice

This worktree is based at `850021a` and is intentionally bounded to the two
common built-in conditional simprocs.  `SimprocDerivation` is a small,
term-free schema record containing only the source name, fixed redex position,
selected branch, and semantic constructor.  The recorder builds it from the
redex and the diverted nested-condition events; it does not inspect
`Simp.Result.proof?`.  Existing `side` entries retain the condition
simplification/discharge trace.

The focused Lean fixture is
`test/SimpTrace/T20IteSimproc.lean`.  Plain `reduceIte` true/false, dependent
`reduceDIte` true/false, a nested condition, a nested occurrence, a source
theorem condition, and applied function redexes all compile.  Applied records
trim the exact shared tail, move the semantic position to `[0,1,0]`, and
record `extraArgs: 1`; dependent records intentionally carry no branch/proof
`args`.  The fixture also asserts refusal of a changed application tail.

Focused check run:

```text
lake build ExplicitLean.SimpTrace        PASS
lake env lean test/SimpTrace/T20IteSimproc.lean   PASS
git diff --check                          PASS
```

T18's accepted inventory remains the baseline: 15 `reduceIte` steps at 6
sites and 15 `reduceDIte` steps at 8 sites.  No fresh 91-site inventory was
run in this bounded checkpoint, so no corpus coverage credit is claimed.  The
focused observed fixtures cover 6/15 `reduceIte` and 3/15 `reduceDIte` steps;
cached-origin nested occurrences still expose a recorder attribution gap and
require a follow-up review before claiming all 30 steps.  Unknown simprocs
retain the existing generic classification path.
