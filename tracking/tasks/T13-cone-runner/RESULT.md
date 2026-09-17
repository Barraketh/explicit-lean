# T13 strict readable-cone runner

## Result

Implemented `Experiment/run_readable_cone.py` and focused checks in
`Experiment/check_readable_cone.py`.  The runner:

* walks the complete Mathlib source-import closure from the seven targets,
  accepting `import`, `meta import`, `public`/`private` and their meta forms;
* requires the reviewed 69-module/134-edge closure and the reviewed target DAG;
* stages each pinned `.olean` artifact family into a fresh private translated
  root, excluding every stock Mathlib search root;
* compiles the four independent roots, rebuilds `Logic.Relator` before its
  dependents, then compiles Function.Basic, IsEmpty.Basic and Option.Basic;
* checks translated-root resolution after staging and after every build;
* removes a module's complete old output family before each compile, then
  requires a newly emitted `.olean` and records before/removed/after freshness
  evidence; and
* runs the remaining executable simp-family lint over the seven generated
  target sources; and
* records plain JSON closure, staging, resolution, build, lint, log and
  recorder/renderer/toolchain version outcomes.

The runner intentionally does not use cryptographic hashes, nonces or a
mandatory declaration oracle.  It does not generate replacements or traces;
the supplied source root must already contain all 69 source files, including
the Relator bridge.  A fresh run directory is required, and no full Mathlib
rebuild is performed.

## Checks

```sh
python3 -B Experiment/check_readable_cone.py
python3 -m py_compile Experiment/run_readable_cone.py Experiment/check_readable_cone.py
git diff --check
python3 -B - <<'PY'
from pathlib import Path
import sys, tempfile
sys.path.insert(0, 'Experiment')
import run_readable_cone as cone
from translated_imports import build_import_environment
with tempfile.TemporaryDirectory(prefix='t13-real-') as raw:
    root = Path(raw); source = root/'source'; translated = root/'translated'; run = root/'run'
    path = source/'Mathlib'/'A.lean'; path.parent.mkdir(parents=True)
    path.write_text('module\n\ndef answer : Nat := 1\n', encoding='utf-8')
    translated.mkdir()
    env = build_import_environment(source, translated)
    result = cone._compile_module(env, run, 'Mathlib.A')
    assert result['status'] == 'passed' and result['freshness']['freshOlean']
    print('real one-module compile: passed')
PY
```

All focused checks and the real one-module pinned Lean compile passed.  A real
seven-module cone compilation was not run in this worktree because it has no
completed Mathlib artifact cache and the task explicitly excludes a full
Mathlib rebuild.
