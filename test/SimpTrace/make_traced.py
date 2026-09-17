#!/usr/bin/env python3
"""Generate a traced copy of a pinned Mathlib module.

The source manifest is derived before instrumentation and written beside the
generated copy. Finalization adds the diagnostic generated occurrence and
invocation ordinals to each ``simp-trace-v2`` record.

    python3 -B test/SimpTrace/make_traced.py Logic/Basic.lean LogicBasicTraced
"""

from __future__ import annotations

import json
import pathlib
import sys

from trace_identity import find_sites, manifest, trace_clause_ordinals, transform

ROOT = pathlib.Path(__file__).resolve().parents[2]
MATHLIB = ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"
OUT = ROOT / "test" / "SimpTrace"


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 1
    source_rel, name = sys.argv[1], sys.argv[2]
    source_path = MATHLIB / source_rel
    source = source_path.read_text(encoding="utf-8")
    sites = find_sites(source)
    text = transform(source, name)
    clause_sites = trace_clause_ordinals(text, name)
    if sorted(clause_sites) != list(range(len(sites))):
        raise SystemExit(f"conversion mismatch: manifest={len(sites)} generated trace clauses differ")
    manifest_value = manifest("Mathlib/" + source_rel.replace("\\", "/"), source, sites)
    (OUT / f"{name}.lean").write_text(text, encoding="utf-8")
    (OUT / f"{name}.manifest.json").write_text(
        json.dumps(manifest_value, ensure_ascii=False, sort_keys=True,
                   separators=(",", ":")), encoding="utf-8")
    print(f"{name}: converted {len(sites)} site(s); manifest {name}.manifest.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
