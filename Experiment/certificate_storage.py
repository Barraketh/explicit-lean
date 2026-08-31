#!/usr/bin/env python3
"""Opt-in lossless hardlink storage for one completed, unpublished cold certificate.

Run with the same frozen project inputs that produced the receipt. A single
writer must serialize certification, deduplication, and publication. All
original paths and bytes remain intact; inode sizes are not APFS allocation.
"""
from __future__ import annotations
import hashlib, importlib.util, json, os, sys
from pathlib import Path

FAMILIES = ("ordinary-stock", "ordinary-applied", "audited-stock", "audited-applied", "bridge-stock", "bridge-applied")
SUFFIXES = (".olean", ".olean.server", ".olean.private", ".ir")
GROUPS = {"stock": ("ordinary-stock", "audited-stock", "bridge-stock"),
          "applied": ("ordinary-applied", "audited-applied", "bridge-applied")}

class DedupError(RuntimeError): pass

def _sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""): h.update(block)
    return h.hexdigest()

def _canonical(path: Path, *, directory=False) -> Path:
    raw = os.fspath(path)
    if not os.path.isabs(raw) or os.path.normpath(raw) != raw:
        raise DedupError(f"path is not canonical absolute: {path}")
    current, chain = path, []
    while True:
        chain.append(current)
        if current.parent == current: break
        current = current.parent
    for item in reversed(chain):
        try:
            if item.is_symlink(): raise DedupError(f"symlink in path: {item}")
        except OSError as error: raise DedupError(f"cannot inspect path: {item}") from error
    if directory and not path.is_dir(): raise DedupError(f"not a directory: {path}")
    return path

def _regular(path: Path) -> None:
    _canonical(path)
    if not path.is_file(): raise DedupError(f"not a regular file: {path}")

def _inside(path: Path, root: Path) -> None:
    try: path.relative_to(root)
    except ValueError as error: raise DedupError(f"path escapes certificate quarantine: {path}") from error

def _load_verifier():
    source = Path(__file__).resolve().parents[1] / "Experiment" / "cold_certified_module.py"
    root = str(source.parent)
    if root not in sys.path: sys.path.insert(0, root)
    spec = importlib.util.spec_from_file_location("cold_certified_module_frozen", source)
    if spec is None or spec.loader is None: raise DedupError("cannot load frozen cold verifier")
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

def _verify(receipt_path, record, receipt_hash):
    try:
        verifier = _load_verifier()
        cert = verifier.Certification(receipt_path, receipt_hash, record)
        verifier.verify_certification(cert, require_target_absent=True)
    except Exception as error:
        raise DedupError(f"production cold verifier rejected receipt: {error}") from error

def _member_map(record, work):
    families = record.get("artifactFamilies")
    if not isinstance(families, dict) or set(families) != set(FAMILIES):
        raise DedupError("receipt does not contain exactly six artifact families")
    result, seen_paths = {}, set()
    suffixes = SUFFIXES if record.get("isModule") else SUFFIXES[:1]
    relative = Path(*record["module"].split(".")).with_suffix(suffixes[0])
    for family in FAMILIES:
        expected = {str((work / family / relative).with_suffix(s)) for s in suffixes}
        entries = families[family]
        if not isinstance(entries, dict) or set(entries) != expected: raise DedupError(f"invalid family identity: {family}")
        mapped = {}
        for raw, digest in entries.items():
            path = Path(raw); _canonical(path); _inside(path, work); _regular(path)
            if path in seen_paths: raise DedupError(f"receipt reuses a path: {path}")
            seen_paths.add(path)
            if not isinstance(digest, str) or len(digest) != 64 or _sha(path) != digest: raise DedupError(f"receipt digest mismatch: {path}")
            suffix = next((s for s in suffixes if path.name.endswith(s)), None)
            if suffix is None or suffix in mapped: raise DedupError(f"unexpected family member: {path}")
            mapped[suffix] = path
        result[family] = mapped
    return result

def deduplicate(receipt_path: Path, *, fail_after=None):
    receipt_path = _canonical(Path(receipt_path)); _regular(receipt_path)
    try: record = json.loads(receipt_path.read_text(encoding="utf-8"))
    except Exception as error: raise DedupError(f"invalid receipt JSON: {error}") from error
    if not isinstance(record, dict): raise DedupError("receipt is not an object")
    receipt_hash, work = _sha(receipt_path), _canonical(receipt_path.parent, directory=True)
    quarantine = Path(record.get("quarantine", "")); _canonical(quarantine, directory=True)
    if quarantine != work / "ordinary-applied": raise DedupError("receipt quarantine is not ordinary-applied sibling")
    _inside(quarantine, work)
    _verify(receipt_path, record, receipt_hash)
    members = _member_map(record, work)
    if fail_after is not None and (isinstance(fail_after, bool) or fail_after < 0): raise DedupError("invalid failure injection")
    operations = []
    for side, names in GROUPS.items():
        anchor = members[names[0]]
        for suffix, source in anchor.items():
            digest = _sha(source)
            for family in names[1:]:
                target = members[family][suffix]
                if _sha(target) != digest: raise DedupError(f"same-source family mismatch: {side} {suffix}")
                target_stat, source_stat = os.stat(target), os.stat(source)
                if target != source and (target_stat.st_dev, target_stat.st_ino) != (source_stat.st_dev, source_stat.st_ino): operations.append((source, target))
    for source, target in operations:
        _regular(source); _regular(target)
        if os.stat(source).st_dev != os.stat(target).st_dev: raise DedupError("hard links require one filesystem")
        temporary = target.with_name("." + target.name + ".dedup-tmp")
        if temporary.exists() or temporary.is_symlink(): raise DedupError(f"poisoned target temporary: {temporary}")
        _canonical(temporary)
    all_paths = [path for family in members.values() for path in family.values()]
    logical = sum(path.stat().st_size for path in all_paths)
    before_unique = {(os.stat(path).st_dev, os.stat(path).st_ino): path.stat().st_size for path in all_paths}
    replaced = 0
    for source, target in operations:
        if fail_after is not None and replaced >= fail_after: raise OSError("injected replacement failure")
        temporary = target.with_name("." + target.name + ".dedup-tmp")
        try:
            os.link(source, temporary); os.replace(temporary, target)
        finally:
            if temporary.exists() or temporary.is_symlink(): temporary.unlink()
        replaced += 1
    _verify(receipt_path, record, receipt_hash)
    after_unique = {(os.stat(path).st_dev, os.stat(path).st_ino): path.stat().st_size for path in all_paths}
    physical = sum(after_unique.values())
    saved_unique = sum(before_unique.values()) - physical
    return {"receipt": str(receipt_path), "groups": 2, "paths": replaced,
            "logicalBytes": logical, "physicalBytes": physical,
            "savedBytes": logical - physical, "savedUniqueInodeBytes": saved_unique,
            "store": None}

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(); parser.add_argument("receipt", type=Path); args = parser.parse_args()
    print(json.dumps(deduplicate(args.receipt), sort_keys=True))
