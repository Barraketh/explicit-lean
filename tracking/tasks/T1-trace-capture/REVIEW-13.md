# T1-trace-capture: merge-gate review, round 13

Reviewed commit `4e1953dfefccd8b8741dc32b02f895f1d7362248` in a clean
worktree. Verdict: **MAJOR DEFECT; not merge-eligible**.

## Checks

- `lake build ExplicitLean.SimpTrace`: PASS (7 jobs; only existing linter and
  deprecation warnings).
- `python3 -B test/SimpTrace/test_trace_identity.py`: PASS. Independent probes
  also pass for top-level `--`, nested `/- ... -/`, strings, nested terms, and
  trailing comma/semicolon/`<;>` punctuation; markers precede comments.
- `python3 -B test/SimpTrace/check_transcription.py`: PASS (84/84;
  `FunctionBasicTraced` 25/25).
- Fresh `lake env lean` runs emitted the expected classified unresolved
  diagnostics; finalization succeeded for all six modules. The resulting raw
  records were converted to v2 and independently checked for complete
  invocation ordinals: 106 records over 84 sites, with `FunctionBasicTraced`
  at 30 records over 25 sites.
- `python3 -B Experiment/check_simp_trace.py`: PASS (72 fixtures).
- `python3 -B Experiment/check_simp_trace.py --report`: PASS (84 sites, 106
  records, 592 steps). `git diff --check`: PASS.

## Major defect: syntax-quotation comment breaks conversion accounting

`trace_clause_ordinals` masks comments with `_mask_comments`, but that scanner
does not track backtick syntax quotations. Reproducer:

```python
from trace_identity import find_sites, transform, trace_clause_ordinals
source = "example : True := by simp [show Syntax from `(foo -- data)] -- tail\\n"
assert find_sites(source)[0].callText.endswith("-- data)]")
generated = transform(source, "BoundaryFixture")
assert trace_clause_ordinals(generated, "BoundaryFixture") == [0]  # currently []
```

The site boundary is found correctly and `transform` inserts `=>trace` before
the actual trailing comment, but `_mask_comments` treats the `-- data` inside
the syntax quotation as a line comment and masks the generated clause too.
Consequently `make_traced.py` rejects this otherwise valid source with a
conversion mismatch. The current regression only checks `find_sites` for this
shape; it does not check parser-visible clause counting after transformation.
This violates the round-13 requirement that delimiters inside syntax
quotations not be misclassified and must be fixed before merge.
