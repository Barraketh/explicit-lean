"""Mechanical checks for recorder-side dependent-forall transport metadata."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def walk(steps):
    for step in steps:
        yield step
        yield from walk(step.get("steps", []))
        yield from walk(step.get("domain", []))
        yield from walk(step.get("body", []))
        for side in step.get("side", []):
            yield from walk(side.get("steps", []))


def check(path: Path):
    data = json.loads(path.read_text())
    transports = [s for loc in data["locations"] for s in walk(loc["steps"])
                  if s.get("kind") == "transport"]
    handles = [s.get("handle") for s in transports]
    assert len(handles) == len(set(handles)), f"duplicate handles in {path}"
    for step in transports:
        assert isinstance(step.get("handle"), int), f"missing handle in {path}"
        assert isinstance(step.get("domain"), list)
        assert isinstance(step.get("body"), list)
        for nested in step["domain"] + step["body"]:
            assert isinstance(nested.get("pos"), list)
            assert "proof" not in nested and "expr" not in nested
            assert nested.get("dir") in (None, "fwd", "rev")
    # The wire event is intentionally metadata-only: Expr/proof objects never
    # cross the JSON boundary.  Before/after are diagnostic strings already in
    # the v1 contract, not serialized kernel objects.
    encoded = path.read_text()
    assert '"proof":' not in encoded and '"expr":' not in encoded
    return len(transports)


def main() -> int:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("test/SimpTrace/meas_out")
    fixture = root / "T35DependentTransport.json"
    count = check(fixture)
    assert count >= 1, "focused fixture emitted no transport"
    all_transports = 0
    for path in sorted(root.glob("LogicBasicTraced_27*.json")):
        all_transports += check(path)
    for path in sorted(root.glob("LogicBasicTraced_28*.json")):
        all_transports += check(path)
    assert all_transports >= 4, "targeted branch captures did not emit transport metadata"
    print(f"T35 transport payload checks: PASS ({count} fixture, {all_transports} branch transports)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
