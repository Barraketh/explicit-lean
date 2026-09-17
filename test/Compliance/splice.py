#!/usr/bin/env python3
"""Build compliance copies of pinned Mathlib modules for the manual overrides.

For each override entry named on the command line (or all entries touched by
this task by default) this writes two files under ``test/Compliance``:

* ``<name>_control.lean``   -- the pinned Mathlib source verbatim, and
* ``<name>_replacement.lean`` -- the same source with the entry's byte range
  replaced by the override's ``replacement`` text.

Both copies keep the original module header and imports, so they elaborate
against the prebuilt Mathlib oleans with ``lake env lean <copy>``.

The module source SHA-256 recorded in the database is checked before splicing;
a mismatch is a hard error.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DATABASE = ROOT / "Experiment" / "simp_manual_overrides.json"
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"

# Occurrence identity -> file stem used for the generated copies.
TARGETS = {
    "1734864b48394331": "Unitization_1734864b48394331",
    "3251bc59333b0c31": "EpiMono_3251bc59333b0c31",
}


def entries() -> list[dict[str, object]]:
    return json.loads(DATABASE.read_text(encoding="utf-8"))["overrides"]


def build(occurrence: str, stem: str) -> list[Path]:
    matching = [e for e in entries() if e["occurrence"] == occurrence]
    if len(matching) != 1:
        raise SystemExit(f"expected exactly one entry for {occurrence}")
    entry = matching[0]
    module = str(entry["module"])
    source_path = MATHLIB / module
    source = source_path.read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    if digest != entry["moduleSourceSha256"]:
        raise SystemExit(
            f"pinned source hash mismatch for {module}: "
            f"{digest} != {entry['moduleSourceSha256']}"
        )
    start, end = int(entry["startByte"]), int(entry["endByte"])
    actual = source[start:end].decode("utf-8")
    if actual != entry["source"]:
        raise SystemExit(f"source bytes at range differ for {occurrence}")
    replacement = str(entry["replacement"]).encode("utf-8")
    control = HERE / f"{stem}_control.lean"
    spliced = HERE / f"{stem}_replacement.lean"
    control.write_bytes(source)
    spliced.write_bytes(source[:start] + replacement + source[end:])
    return [control, spliced]


def main(argv: list[str]) -> int:
    wanted = argv[1:] or sorted(TARGETS)
    written: list[Path] = []
    for occurrence in wanted:
        stem = TARGETS.get(occurrence)
        if stem is None:
            raise SystemExit(f"unknown occurrence {occurrence}")
        written.extend(build(occurrence, stem))
    for path in written:
        print(path.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
