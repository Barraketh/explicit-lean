#!/usr/bin/env python3
"""Run the `explicit_rw` fixtures and their negative-test expectations.

Builds `ExplicitLean.ExplicitRw`, then elaborates every fixture under
`test/ExplicitRw/` with `lake env lean`. A fixture passes when it elaborates
with no diagnostics at all: the positive fixtures assert their intermediate
goal with `guard_target` / `guard_hyp` before closing, and the negative fixture
pins each expected error with `#guard_msgs`, so any drift in a message or in a
resulting goal turns into output here and fails the check.

Run with `python3 -B Experiment/check_explicit_rw.py`.
"""

from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
FIXTURE_DIR = REPO / "test" / "ExplicitRw"
REJECTED_DIR = FIXTURE_DIR / "RejectedSyntax"
MODULE = "ExplicitLean.ExplicitRw"

# Fixtures that deliberately contain failing proofs, checked via `#guard_msgs`.
# Listed so the report distinguishes them from the positive fixtures.
NEGATIVE = {"Negative.lean"}

# A single fixture must not run away; the task's escalation bound is 30 minutes.
TIMEOUT_SECONDS = 30 * 60


def run(cmd: list[str], timeout: int = TIMEOUT_SECONDS) -> tuple[int, str, float]:
    start = time.monotonic()
    proc = subprocess.run(
        cmd,
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    elapsed = time.monotonic() - start
    return proc.returncode, (proc.stdout + proc.stderr).strip(), elapsed


def main() -> int:
    if not FIXTURE_DIR.is_dir():
        print(f"check_explicit_rw: FAIL: no fixture directory at {FIXTURE_DIR}")
        return 1

    fixtures = sorted(FIXTURE_DIR.glob("*.lean"))
    if not fixtures:
        print(f"check_explicit_rw: FAIL: no fixtures in {FIXTURE_DIR}")
        return 1

    print(f"check_explicit_rw: building {MODULE}")
    code, output, elapsed = run(["lake", "build", MODULE])
    if code != 0:
        print(f"check_explicit_rw: FAIL: `lake build {MODULE}` exited {code} "
              f"after {elapsed:.1f}s")
        print(output)
        return 1
    # A warning in product code is a defect too: the build must be clean.
    if "warning:" in output:
        print(f"check_explicit_rw: FAIL: `lake build {MODULE}` produced warnings")
        print(output)
        return 1
    print(f"check_explicit_rw: build clean ({elapsed:.1f}s)")

    failures: list[str] = []
    for fixture in fixtures:
        rel = fixture.relative_to(REPO)
        kind = "negative" if fixture.name in NEGATIVE else "positive"
        try:
            code, output, elapsed = run(["lake", "env", "lean", str(rel)])
        except subprocess.TimeoutExpired:
            print(f"  {rel} ({kind}): FAIL (timed out after {TIMEOUT_SECONDS}s)")
            failures.append(f"{rel}: timed out")
            continue

        # `#guard_msgs` consumes the expected diagnostics, so a passing fixture
        # of either kind leaves no output and exits 0.
        if code == 0 and not output:
            print(f"  {rel} ({kind}): PASS ({elapsed:.1f}s)")
        else:
            print(f"  {rel} ({kind}): FAIL (exit {code}, {elapsed:.1f}s)")
            print("    " + "\n    ".join(output.splitlines()) if output else "")
            failures.append(f"{rel}: exit {code}")

    # Forms that must be rejected by the *parser*. `#guard_msgs` cannot pin a
    # parse error, because parsing fails before the command elaborates, so each
    # of these files must fail to compile with the recorded message fragment.
    expected_path = REJECTED_DIR / "expected.json"
    if not expected_path.is_file():
        print(f"check_explicit_rw: FAIL: missing {expected_path.relative_to(REPO)}")
        return 1
    expected: dict[str, str] = json.loads(expected_path.read_text(encoding="utf-8"))

    rejected = sorted(REJECTED_DIR.glob("*.lean"))
    if not rejected:
        print(f"check_explicit_rw: FAIL: no files in {REJECTED_DIR.relative_to(REPO)}")
        return 1
    unlisted = {f.name for f in rejected} - set(expected)
    if unlisted:
        print(f"check_explicit_rw: FAIL: not listed in expected.json: {sorted(unlisted)}")
        return 1

    for fixture in rejected:
        rel = fixture.relative_to(REPO)
        fragment = expected[fixture.name]
        code, output, elapsed = run(["lake", "env", "lean", str(rel)])
        if code == 0:
            print(f"  {rel} (rejected-syntax): FAIL (compiled, but must be rejected)")
            failures.append(f"{rel}: compiled although it must be rejected")
        elif fragment not in output:
            print(f"  {rel} (rejected-syntax): FAIL (wrong reason)")
            print(f"    expected to contain: {fragment}")
            print("    " + "\n    ".join(output.splitlines()[:4]))
            failures.append(f"{rel}: rejected for the wrong reason")
        else:
            print(f"  {rel} (rejected-syntax): PASS ({elapsed:.1f}s)")

    total = len(fixtures) + len(rejected)
    if failures:
        print()
        print(f"check_explicit_rw: FAIL ({len(failures)} of {total} fixture(s))")
        for f in failures:
            print(f"  {f}")
        return 1

    print()
    print(f"check_explicit_rw: PASS ({len(fixtures)} fixture(s), "
          f"{len(rejected)} rejected-syntax case(s))")
    return 0


if __name__ == "__main__":
    sys.exit(main())
