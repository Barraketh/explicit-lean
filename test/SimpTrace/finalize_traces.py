#!/usr/bin/env python3
"""Finalize raw recorder files as self-contained simp-trace-v2 records."""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

from trace_identity import find_sites, manifest, validate_invocations

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / "test" / "SimpTrace"
RAW_RE = re.compile(r"^(?P<name>.+)_(?P<site>[0-9]+)(?:\.(?P<run>[0-9]+))?\.json$")


def finalize(name: str) -> int:
    traced_path = OUT / f"{name}.lean"
    manifest_path = OUT / f"{name}.manifest.json"
    if not traced_path.is_file() or not manifest_path.is_file():
        raise ValueError(f"missing traced copy or manifest for {name}")
    # The generator records the original source path in modulePath; resolve it
    # against pinned Mathlib for this trusted-environment producer check.
    value = json.loads(manifest_path.read_text(encoding="utf-8"))
    module_path = value.get("modulePath", "")
    if not module_path.startswith("Mathlib/"):
        raise ValueError("manifest has invalid modulePath")
    original = ROOT / ".lake" / "packages" / "mathlib" / module_path
    source = original.read_text(encoding="utf-8")
    expected = manifest(module_path, source, find_sites(source))
    if value != expected:
        raise ValueError("manifest/source range or callText mismatch")
    files: list[tuple[pathlib.Path, int, int]] = []
    for path in sorted((OUT / "meas_out").glob(f"{name}_*.json")):
        match = RAW_RE.fullmatch(path.name)
        if not match or match.group("name") != name:
            raise ValueError(f"unrecognized trace output: {path.name}")
        files.append((path, int(match.group("site")) - 1,
                      int(match.group("run") or 0)))
    groups: dict[int, list[tuple[pathlib.Path, int]]] = {}
    for path, site, run in files:
        if site < 0 or site >= len(value["sites"]):
            raise ValueError(f"trace site ordinal out of range: {site}")
        groups.setdefault(site, []).append((path, run))
    expected_sites = set(range(len(value["sites"])))
    if set(groups) != expected_sites:
        raise ValueError(f"manifest/output mismatch missing={sorted(expected_sites - set(groups))} "
                         f"extra={sorted(set(groups) - expected_sites)}")
    for site, entries in groups.items():
        entries.sort(key=lambda item: (item[1], item[0].name))
        total = len(entries)
        records: list[dict] = []
        for invocation, (path, _) in enumerate(entries):
            raw = json.loads(path.read_text(encoding="utf-8"))
            if raw.get("schema") == "simp-trace-v2":
                raise ValueError(f"duplicate/already finalized trace: {path.name}")
            if raw.get("schema") != "simp-trace-v1":
                raise ValueError(f"unexpected raw schema in {path.name}")
            records.append({"invocation": invocation, "invocations": total})
            s = value["sites"][site]
            path.write_text(json.dumps({
                "schema": "simp-trace-v2", "modulePath": module_path,
                "site": s, "occurrence": raw.get("occurrence", ""),
                "invocation": invocation, "invocations": total,
                "locations": raw.get("locations", []),
            }, ensure_ascii=False, sort_keys=True, separators=(",", ":")),
                encoding="utf-8")
        validate_invocations(records)
    print(f"{name}: finalized {len(files)} record(s), {len(groups)} site(s)")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("name")
    args = parser.parse_args()
    try:
        return finalize(args.name)
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"FAIL {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
