# T13 strict readable-cone runner review 2

Reviewed commit `298755b` as a fresh pass after REVIEW-1. Verdict:
**pass — REVIEW-1 major finding is fixed.**

The runner removes the complete per-module output family (`.olean`, `.ir`,
and `.olean.*`) before invoking pinned Lean, rejects a zero-exit/no-output
invocation, and records `beforeFamily`, `removedFamily`, `afterFamily` and
`freshOlean` as ordinary JSON values. A failed module is retained in the
manifest before failure propagates. The focused regression covers stale
`.olean`/`.ir`/`.olean.server` plus a no-op (failed), then a writer emitting a
fresh `.olean` and server artifact (passed). A real pinned one-module compile
emitted `.ir`, `.olean`, `.olean.private`, and `.olean.server`, resolved from
the private translated root, and passed.

## Verification

Commands run in this worktree:

```text
python3 -B Experiment/check_readable_cone.py
....
Ran 4 tests ... OK

python3 -m py_compile Experiment/run_readable_cone.py Experiment/check_readable_cone.py
git diff --check HEAD^ HEAD
both passed (no output)

python3 -B Experiment/check_simp_family_lint.py
Ran 46 tests ... OK (skipped=2)

python3 -B Experiment/check_no_simp_family.py
check_no_simp_family: PASS (3 file(s) scanned)

python3 -B - <<'PY'
import sys
from pathlib import Path
sys.path.insert(0, 'Experiment')
import run_readable_cone as c
closure = c.discover_closure(Path('.lake/packages/mathlib'))
print('closure modules', len(closure.modules), 'edges', len(closure.edges))
print('kinds', {k: sum(e.kind == k for e in closure.edges) for k in sorted({e.kind for e in closure.edges})})
c.verify_reviewed_closure(closure); c.verify_build_order(closure)
print('cross', sorted((e.source, e.module) for e in closure.edges if e.source not in c.TARGETS and e.module in c.TARGETS))
print('closure/order: passed')
PY
closure modules 69 edges 134
kinds {'import': 8, 'public import': 96, 'public meta import': 30}
cross [('Mathlib.Logic.Relator', 'Mathlib.Logic.Function.Defs')]
closure/order: passed

python3 -B Experiment/check_translated_imports.py
JSON status: passed; conflicting stock compiler returnCode: 1 (expected);
missing audit: rejected (expected)
```

The real preflight used `build_import_environment` and `_compile_module` with
a temporary source containing `def answer : Nat := 1`; it printed
`real one-module compile: passed` and reported `returnCode: 0`,
`status: "passed"`, `freshOlean: true`, and translated-root resolution.

The failure-propagation preflight patched only the compiler to return zero
without writing output. The runner raised `ConeFailure` and its manifest was
valid plain JSON with top-level `status: "failed"`, module `status: "failed"`,
`returnCode: 0`, `afterFamily: []`, and `freshOlean: false`.

No full Mathlib build was run. No implementation files were modified.
