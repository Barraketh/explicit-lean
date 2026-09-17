#!/usr/bin/env python3
"""Finalize raw recorder files as self-contained simp-trace-v2 records.

The flag-based interface is deliberately non-mutating: raw v1 files are read
from ``--raw-dir`` and finalized records are written only to ``--out-dir``.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

from trace_identity import find_sites, manifest, validate_invocations, verify_transform

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / "test" / "SimpTrace"
RAW_RE = re.compile(r"^(?P<name>.+)_(?P<site>[0-9]+)(?:\.(?P<run>[0-9]+))?\.json$")


def finalize_paths(traced_path: pathlib.Path, manifest_path: pathlib.Path,
                   source_path: pathlib.Path, raw_dir: pathlib.Path,
                   out_dir: pathlib.Path) -> int:
    if not traced_path.is_file() or not manifest_path.is_file() or not source_path.is_file():
        raise ValueError("missing traced source, manifest, or original source")
    source = source_path.read_text(encoding="utf-8")
    value = json.loads(manifest_path.read_text(encoding="utf-8"))
    module_path = value.get("modulePath", "")
    if not isinstance(module_path, str) or not module_path:
        raise ValueError("manifest has invalid modulePath")
    sites = find_sites(source)
    if value != manifest(module_path, source, sites):
        raise ValueError("manifest/source range or callText mismatch")
    traced = traced_path.read_text(encoding="utf-8")
    verify_transform(source, traced_path.stem, traced, sites)
    name = traced_path.stem
    files: list[tuple[pathlib.Path, int, int]] = []
    for path in sorted(raw_dir.glob("*.json")):
        match = RAW_RE.fullmatch(path.name)
        if not match or match.group("name") != name:
            raise ValueError(f"unrecognized trace output: {path.name}")
        files.append((path, int(match.group("site")) - 1,
                      int(match.group("run") or 0)))
    groups: dict[int, list[tuple[pathlib.Path, int]]] = {}
    for path, site, run in files:
        if site < 0 or site >= len(sites):
            raise ValueError(f"trace site ordinal out of range: {site}")
        groups.setdefault(site, []).append((path, run))
    expected_sites = set(range(len(sites)))
    if set(groups) != expected_sites:
        raise ValueError(f"manifest/output mismatch missing={sorted(expected_sites - set(groups))} "
                         f"extra={sorted(set(groups) - expected_sites)}")
    out_dir.mkdir(parents=True, exist_ok=True)
    for site, entries in groups.items():
        entries.sort(key=lambda item: (item[1], item[0].name))
        if len({run for _, run in entries}) != len(entries):
            raise ValueError(f"duplicate invocation output for site {site}")
        total = len(entries)
        records: list[dict] = []
        for invocation, (path, _) in enumerate(entries):
            raw = json.loads(path.read_text(encoding="utf-8"))
            if raw.get("schema") != "simp-trace-v1":
                raise ValueError(f"raw input is not v1: {path.name}")
            if not isinstance(raw.get("occurrence"), str):
                raise ValueError(f"missing diagnostic occurrence: {path.name}")
            if (not isinstance(raw.get("call"), str)
                    or not raw["call"].startswith("simp_trace")
                    or "=>trace" not in raw["call"]):
                raise ValueError(f"raw call text is missing or malformed: {path.name}")
            if "invocation" in raw or "invocations" in raw:
                raise ValueError(f"raw invocation metadata is malformed: {path.name}")
            records.append({"invocation": invocation, "invocations": total})
            s = value["sites"][site]
            final = {"schema": "simp-trace-v2", "modulePath": module_path,
                     "site": {"siteOrdinal": s["siteOrdinal"],
                              "startChar": s["startChar"], "endChar": s["endChar"],
                              "callText": s["callText"]},
                     "occurrence": raw["occurrence"],
                     "invocation": invocation, "invocations": total,
                     "locations": raw.get("locations", [])}
            (out_dir / path.name).write_text(
                json.dumps(final, ensure_ascii=False, sort_keys=True,
                           separators=(",", ":")), encoding="utf-8")
        validate_invocations(records)
    print(f"{name}: finalized {len(files)} record(s), {len(groups)} site(s)")
    return 0


def finalize(name: str) -> int:
    """Legacy convenience mode; the explicit flag interface is non-mutating."""
    traced_path = OUT / f"{name}.lean"
    manifest_path = OUT / f"{name}.manifest.json"
    value = json.loads(manifest_path.read_text(encoding="utf-8"))
    source_path = ROOT / ".lake" / "packages" / "mathlib" / value["modulePath"]
    return finalize_paths(traced_path, manifest_path, source_path,
                          OUT / "meas_out", OUT / "meas_out")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("name", nargs="?")
    parser.add_argument("--traced-source", type=pathlib.Path)
    parser.add_argument("--manifest", type=pathlib.Path)
    parser.add_argument("--source", type=pathlib.Path)
    parser.add_argument("--raw-dir", type=pathlib.Path)
    parser.add_argument("--out-dir", type=pathlib.Path)
    args = parser.parse_args()
    try:
        supplied = [args.traced_source, args.manifest, args.source,
                    args.raw_dir, args.out_dir]
        if all(path is not None for path in supplied):
            return finalize_paths(*supplied)
        if args.name and not any(path is not None for path in supplied):
            return finalize(args.name)
        raise ValueError("provide name or all five non-mutating finalizer paths")
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"FAIL {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
