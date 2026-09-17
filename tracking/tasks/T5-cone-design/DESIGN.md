# T5 seven-module cone preflight

## Result

The seven-module headline of **91 executable `simp`/`simp only` sites is
correct**. The old six-module headline was not: an independent
comment/string-aware scan gives **84**, because `Logic/Function/Basic.lean` has
25 (not 23); the two sites on lines 698 and 700 follow `@[simp]` on the same
line. `Data/Option/Basic.lean` contributes the remaining 7. Thus
`84 + 7 = 91`; there is no unexplained count discrepancy, but any six-module
report still saying 82 is stale and must not be used as a denominator.

## Dependency order

Use this deterministic topological order. The first four are independent and
could run in parallel, but serial order makes the translated-root manifest and
oracle evidence easier to audit.

1. `Mathlib.Logic.Basic`
2. `Mathlib.Logic.ExistsUnique`
3. `Mathlib.Logic.Function.Defs`
4. `Mathlib.Logic.Nontrivial.Defs`
5. `Mathlib.Logic.Function.Basic` (imports all four predecessors)
6. `Mathlib.Logic.IsEmpty.Basic` (imports `Function.Basic`)
7. `Mathlib.Data.Option.Basic` (imports `IsEmpty.Basic`)

The direct target-to-target edges are:

```text
Function.Basic -> Logic.Basic, Logic.ExistsUnique,
                  Logic.Function.Defs, Logic.Nontrivial.Defs
IsEmpty.Basic  -> Logic.Function.Basic
Data.Option.Basic -> Logic.IsEmpty.Basic
```

Direct non-target imports that must be present in the root are:

| target | non-target imports |
| --- | --- |
| `Logic.Basic` | `Mathlib.Lean.Meta.Simp`, `Batteries.Logic`, `Batteries.Util.LibraryNote`, `Mathlib.Tactic.Attr.Register` |
| `Logic.ExistsUnique` | `Mathlib.Init` |
| `Logic.Function.Defs` | `Mathlib.Init`, `Mathlib.Tactic.Attr.Register` |
| `Logic.Nontrivial.Defs` | `Mathlib.Tactic.Push.Attr` |
| `Logic.Function.Basic` | `Mathlib.Data.Set.Defs`, `Mathlib.Logic.Nonempty`, `Batteries.Tactic.Init`, `Mathlib.Order.Defs.Unbundled`, `Mathlib.Tactic.Attr.Register` |
| `Logic.IsEmpty.Basic` | `Mathlib.Logic.IsEmpty.Defs`, `Mathlib.Logic.Relator` |
| `Data.Option.Basic` | `Mathlib.Control.Combinators`, `Mathlib.Data.Option.Defs`, `Mathlib.Logic.Relator`, `Mathlib.Util.CompileInductive`, `Aesop`, `Batteries.Tactic.Lint.Simp` |

`Mathlib.Logic.Relator` is a required **bridge**: its source imports
`Mathlib.Logic.Function.Defs`, which is a translated target. Recompile the
bridge after step 3 into the translated root, before step 6; using the stock
Relator olean would bind it to the stock Function.Defs dependency. The other
listed Mathlib imports may remain byte-identical stock dependency families, but
must be staged under the translated root rather than resolved from a stock
Mathlib search root.

`Mathlib.Init` is a broad root. A comment-stripped source import walk from
these targets reaches 908 distinct Mathlib source modules (including the seven
targets), so the direct table is not a complete artifact manifest. The
preflight must either stage the exact `--deps` closure or, more simply, copy the
pinned stock Mathlib artifact families into the translated root and overwrite
the seven targets plus the Relator bridge. Do not put a stock directory that
contains `Mathlib/` later in `LEAN_PATH`: that is a fallback and violates the
strict import contract. Record every staged non-target family and hash; the
bridge's output is the only non-target family rebuilt for this cone.

## Independent site counts

The scan used a standalone lexer: nested `/- ... -/` and `--` comments,
double-quoted strings, and `@[...]` spans were blanked while retaining source
offsets; then standalone `simp`/`simp only` tokens were counted. It excluded
the two `withTraceNode \`Meta.Tactic.simp ... <| simp` calls inside the
`simproc_decl` implementations in `Logic/Basic.lean`: those are the
metaprogram's `Lean.Meta.Simp` API, not executable source tactic sites. The
attribute spans themselves were masked, but tactics after an attribute on the
same line were retained.

| module | executable sites | evidence lines / note |
| --- | ---: | --- |
| `Logic/Basic.lean` | 31 | 330,331,424,428,430,497,508,552,589,593,597,655,658,663,683,752,888,899,917,962,973,987,990,1007,1011,1015,1019,1051,1055,1071,1087; lexical total 33 minus the two Meta API calls |
| `Logic/ExistsUnique.lean` | 8 | 112,115,119,121,131,138,148,154 |
| `Logic/Function/Basic.lean` | 25 | 190,316,390,410,428,528,664,683,688,698,700,796,847,859,884,895,923,928,934,975,982,1057,1130,1137,1156 |
| `Logic/Function/Defs.lean` | 2 | 62,139 |
| `Logic/IsEmpty/Basic.lean` | 17 | 30,34,45,49,52,56,60,64,68,72,76,102,105,109,112,119,122 |
| `Logic/Nontrivial/Defs.lean` | 1 | 98 |
| `Data/Option/Basic.lean` | 7 | 48,56,59,96,195,198,234 |
| **total** | **91** | **84 in the corrected six-module set; +7 Option sites** |

Exact reproduction against the pinned package is:

```sh
python3 -B - <<'PY'
from pathlib import Path
import re
root = Path('/Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture/.lake/packages/mathlib/Mathlib')
mods = ['Logic/Basic.lean','Logic/ExistsUnique.lean','Logic/Function/Basic.lean',
        'Logic/Function/Defs.lean','Logic/IsEmpty/Basic.lean',
        'Logic/Nontrivial/Defs.lean','Data/Option/Basic.lean']
token = re.compile(r'(?<![\w?.])simp(?: only)?(?![_?\w])')
def mask(s):
    # Standalone preflight: blank nested block/line comments, strings, and @[...].
    out=list(s); i=0; depth=0
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; out[i:i+2]=[' ']*2; i += 2; continue
            if s.startswith('-/', i): depth -= 1; out[i:i+2]=[' ']*2; i += 2; continue
            out[i]=' '; i += 1; continue
        if s.startswith('--', i):
            j=s.find('\n', i); j=len(s) if j < 0 else j; out[i:j]=[' ']*(j-i); i=j; continue
        if s.startswith('/-', i): depth=1; out[i:i+2]=[' ']*2; i += 2; continue
        if s[i]=='"':
            out[i]=' '; i += 1
            while i < len(s):
                if s[i]=='\\': out[i]=' '; i += 1
                if i < len(s) and s[i-1]=='\\': out[i]=' '; i += 1; continue
                if i < len(s) and s[i]=='"': out[i]=' '; i += 1; break
                if i < len(s): out[i]=' '; i += 1
            continue
        if s.startswith('@[', i):
            j=i+2; d=1; quoted=False
            while j < len(s) and d:
                if quoted:
                    if s[j]=='\\': j += 2; continue
                    if s[j]=='"': quoted=False
                elif s[j]=='"': quoted=True
                elif s[j]=='[': d += 1
                elif s[j]==']': d -= 1
                j += 1
            out[i:j]=[' ']*(j-i); i=j; continue
        i += 1
    return ''.join(out)
total=0
for rel in mods:
    src=(root/rel).read_text(); lines=src.splitlines(); hits=[]
    for m in token.finditer(mask(src)):
        line=src.count('\n',0,m.start())+1
        if 'withTraceNode `Meta.Tactic.simp' in lines[line-1]: continue
        hits.append(line)
    print(f'{rel}: {len(hits)}')
    total += len(hits)
print('TOTAL', total)
PY
```

Expected output is `31, 8, 25, 2, 17, 1, 7` and `TOTAL 91` in the order
above. This method intentionally catches the two same-line attributed
declarations at Function/Basic lines 698 and 700.

## Every `Data.Option.Basic` site

T1 has no traced Option fixture yet; these seven sites must be captured before
T4 renders the cone. Their exact source shapes are:

| line | source shape |
| ---: | --- |
| 48 | one-line theorem `mem_map ... := by simp` |
| 56 | multiline theorem `forall_mem_map ... := by simp` |
| 59 | multiline theorem `exists_mem_map ... := by simp` |
| 96 | nested term proof `some_injective _ <| by simp only [← map_some, h]` inside `map_injective'` |
| 195 | indented tail `simp` in `orElse_eq_some` after a multiline theorem statement |
| 198 | indented tail `simp` in `orElse_eq_none` |
| 234 | tail after a preceding tactic: `ext` then `simp only [Function.comp_apply, getD_some, id_eq]` |

The exact reproducer is:

```sh
nl -ba /Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture/.lake/packages/mathlib/Mathlib/Data/Option/Basic.lean \
  | sed -n '45,60p;94,98p;193,199p;231,235p'
```

The renderer must retain the original call as an adjacent comment in each
shape. In particular, line 96 is term-mode under `<| by`, while line 234 is
the ordinary two-tactic block; treating both as a whole-line replacement can
drop the surrounding term or `ext` continuation.

## Minimal translated-import-root layout

Use two distinct roots outside all worktrees:

```text
<run>/source/Mathlib/<seven target .lean files + Relator bridge .lean>
<run>/translated-oleans/Mathlib/<required .olean families>
<run>/manifest.json                 # source/artifact hashes and dependency edges
```

`translated-oleans/Mathlib` contains the complete pinned stock dependency
families selected by the exact `--deps` closure (or a hash-checked full stock
family copy), then receives target outputs in the order above. For every
module output retain `.olean`, `.olean.server`, `.olean.private`, and `.ir`
when the pinned compiler emits them. Do not use symlinks to stock files.

Construct the search environment with the existing
`Experiment/translated_imports.py` helpers. Its `LEAN_PATH` must be exactly:

```text
translated-oleans : non-Mathlib package roots from `lake env printenv` : Lean core
```

The helper must report the seven target modules and the Relator bridge as
resolved from the first root, and must reject every stock root containing a
`Mathlib/` directory. Compile each source with the pinned binary, `-R
<run>/source`, and `-o translated-oleans/Mathlib/<module>.olean`; refresh and
hash the dependency resolution after each step. This ensures IsEmpty and
Option consume translated Function/IsEmpty/Relator artifacts rather than
silently loading package oleans.

## Focused acceptance commands

Run the cheap gates first:

```sh
python3 -B Experiment/check_translated_imports.py
python3 -B Experiment/check_simp_family_lint.py --sweep
python3 -B /Users/ptsier/projects/explicit-lean-worktrees/T4-pipeline/Experiment/pipeline/check_pipeline.py
```

The cone runner should then compile the seven modules in the order above with
`translated_imports.run_pinned_lean`, and assert after every output:

```sh
python3 -B - <<'PY'
# `root` is the translated source tree and `out` its olean root.
from pathlib import Path
import sys
sys.path.insert(0, 'Experiment')
from translated_imports import build_import_environment
root = Path('/private/tmp/t5-cone/source')
out = Path('/private/tmp/t5-cone/translated-oleans')
env = build_import_environment(root, out)
print(env.resolve_mathlib([
  'Mathlib.Logic.Basic', 'Mathlib.Logic.ExistsUnique',
  'Mathlib.Logic.Function.Defs', 'Mathlib.Logic.Nontrivial.Defs',
  'Mathlib.Logic.Function.Basic', 'Mathlib.Logic.IsEmpty.Basic',
  'Mathlib.Data.Option.Basic', 'Mathlib.Logic.Relator']))
PY
```

After source generation, run a target-only remaining-call check against the
seven translated `.lean` files. It must report zero executable findings; a
retained original is allowed only inside its adjacent comment:

```sh
python3 -B - <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, '/Users/ptsier/projects/explicit-lean-worktrees/T4-pipeline/Experiment/pipeline')
import simp_family_lint
root=Path('/private/tmp/t5-cone/source/Mathlib')
files=['Logic/Basic.lean','Logic/ExistsUnique.lean','Logic/Function/Basic.lean',
       'Logic/Function/Defs.lean','Logic/IsEmpty/Basic.lean',
       'Logic/Nontrivial/Defs.lean','Data/Option/Basic.lean']
bad=[]
for rel in files:
    for finding in simp_family_lint.findings((root/rel).read_text()):
        bad.append(f'{rel}:{finding.line}: {finding.describe()}')
if bad: raise SystemExit('\n'.join(bad))
print('translated cone remaining executable simp-family sites: 0')
PY
```

Finally invoke the existing declaration oracle for each successfully compiled
target (and the bridge where it was rebuilt), using its canonical dotted module
name and the exact stock/applied source pair. The oracle must pass after
compile, with no weakened axiom or environment checks. The T7 design's
source-pair adapter equalizes the `ExplicitRw` import in the stock companion;
use that adapter rather than passing raw stock source against translated
source. A failed whole-module build is not oracle-eligible; clean isolated
per-site probes are oracle-eligible independently and must each pass before a
site is reported replayed.

## Acceptance boundary

The cone is accepted only if all 91 sites are inventoried, every Data.Option
site has a trace or an explicit classified unresolved result, every translated
module resolves all Mathlib imports from the translated root, remaining-call
lint is zero for generated executable regions, and each clean module/probe
passes the declaration/environment/axiom oracle. Any missing Option trace,
stock-root resolution, stale dependency family, or oracle failure is a
fail-closed blocker, not a reason to lower the denominator.

