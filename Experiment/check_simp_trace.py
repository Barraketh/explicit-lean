#!/usr/bin/env python3
"""Check `simp_trace` fixture output against committed step skeletons.

Each fixture in `test/SimpTrace/Fixtures.lean` writes a trace to
`test/SimpTrace/out/<name>.json`.  This script compares every such trace
against `test/SimpTrace/expected/<name>.json`, which records the skeleton we
expect: the schema, the locations, whether each location was closed and how,
and, per step, the kind, position, lemma/hypothesis name, direction, simproc
source, replay tactic, and any side-condition sub-traces.

The debug fields (`before`, `after`, `pre`, `post`, `lhs`, `rhs`, `to`) are
deliberately not compared: the spec calls them debug fields that replay must
not depend on, and pretty-printing is not stable enough to pin in a fixture.

Run from the repository root:

    python3 -B Experiment/check_simp_trace.py

Exit status is 0 when every fixture matches, 1 otherwise.
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT_DIR = ROOT / "test" / "SimpTrace" / "out"
EXPECTED_DIR = ROOT / "test" / "SimpTrace" / "expected"

# Step kinds the spec defines for v1.  An unknown kind is a hard error: a
# trace must never carry a step the replay tactic cannot interpret.
KNOWN_KINDS = {"rw", "unfold", "beta", "eta", "proj", "zeta", "change", "eq",
               "intro_ctx"}

# Close forms the amended spec defines. `assumption:` and `absurd:` are prefixes.
CLOSE_EXACT = {"rfl", "true_intro", "decide"}
CLOSE_PREFIXES = ("assumption:", "absurd:")


def check_close(path: str, close, messages: list[str]) -> None:
    """A close form must be one the amended spec defines, and the hypothesis
    forms must actually name a hypothesis."""
    if close is None:
        return
    by = close.get("by")
    if by in CLOSE_EXACT:
        return
    for prefix in CLOSE_PREFIXES:
        if isinstance(by, str) and by.startswith(prefix):
            if not by[len(prefix):]:
                fail(messages, f"{path}.close: {by!r} names no hypothesis")
            return
    fail(messages, f"{path}.close: {by!r} is not a spec close form")


def fail(messages: list[str], text: str) -> None:
    messages.append(text)


def check_steps(path: str, actual: list, expected: list, messages: list[str]) -> None:
    if len(actual) != len(expected):
        fail(
            messages,
            f"{path}: expected {len(expected)} step(s), got {len(actual)}\n"
            f"    expected kinds: {[s['kind'] for s in expected]}\n"
            f"    actual kinds:   {[s.get('kind') for s in actual]}",
        )
        return

    for index, (got, want) in enumerate(zip(actual, expected)):
        where = f"{path}.steps[{index}]"

        kind = got.get("kind")
        if kind not in KNOWN_KINDS:
            fail(messages, f"{where}: unknown step kind {kind!r}")

        for field in ("kind", "pos", "name", "dir", "source", "by", "local"):
            if field in want:
                if got.get(field) != want[field]:
                    fail(
                        messages,
                        f"{where}.{field}: expected {want[field]!r}, "
                        f"got {got.get(field)!r}",
                    )
            elif field in got and field in ("name", "dir", "source"):
                fail(messages, f"{where}: unexpected {field}={got[field]!r}")

        # A `rw` step must name a lemma and a direction; an `eq` step must name
        # its simproc source and the ordinary tactic that replays it.
        if kind == "rw":
            if not got.get("name"):
                fail(messages, f"{where}: `rw` step without a name")
            if got.get("dir") not in ("fwd", "rev"):
                fail(messages, f"{where}: `rw` step with dir={got.get('dir')!r}")
        if kind == "eq":
            if not got.get("source"):
                fail(messages, f"{where}: `eq` step without a source")
            if got.get("by") not in ("rfl", "decide", "unknown"):
                fail(messages, f"{where}: `eq` step with by={got.get('by')!r}")
        if kind == "unfold" and not got.get("name"):
            fail(messages, f"{where}: `unfold` step without a constant name")

        local = got.get("local")
        if local is not None:
            if local.get("contextual") is True:
                if not isinstance(local.get("ctxIndex"), int):
                    fail(messages, f"{where}.local: contextual ref without ctxIndex")
                if "userName" in local:
                    fail(
                        messages,
                        f"{where}.local: contextual ref must not carry userName "
                        f"(the namespaces must not collide)",
                    )
            else:
                if not local.get("userName"):
                    fail(messages, f"{where}.local: ordinary ref without userName")
                if not isinstance(local.get("inaccessible"), bool):
                    fail(messages, f"{where}.local: ordinary ref without inaccessible")
                if not isinstance(local.get("ctxIndex"), int):
                    fail(messages, f"{where}.local: ordinary ref without ctxIndex")

        if not isinstance(got.get("pos", []), list) or not all(
            isinstance(c, int) and c >= 0 for c in got.get("pos", [])
        ):
            fail(messages, f"{where}.pos: not a list of child indices: {got.get('pos')!r}")

        want_side = want.get("side", [])
        got_side = got.get("side", [])
        if len(got_side) != len(want_side):
            fail(
                messages,
                f"{where}.side: expected {len(want_side)} sub-trace(s), "
                f"got {len(got_side)}",
            )
        else:
            for side_index, (gs, ws) in enumerate(zip(got_side, want_side)):
                side_path = f"{where}.side[{side_index}]"
                if gs.get("goal") != ws.get("goal"):
                    fail(
                        messages,
                        f"{side_path}.goal: expected {ws.get('goal')!r}, "
                        f"got {gs.get('goal')!r}",
                    )
                check_close(side_path, gs.get("close"), messages)
                if gs.get("close") != ws.get("close"):
                    fail(
                        messages,
                        f"{side_path}.close: expected {ws.get('close')!r}, "
                        f"got {gs.get('close')!r}",
                    )
                check_steps(side_path, gs.get("steps", []), ws.get("steps", []), messages)


def check_trace(name: str, actual: dict, expected: dict, messages: list[str]) -> None:
    if actual.get("schema") != expected.get("schema"):
        fail(
            messages,
            f"{name}: schema is {actual.get('schema')!r}, "
            f"expected {expected.get('schema')!r}",
        )

    for field in ("module", "occurrence", "call"):
        if field not in actual:
            fail(messages, f"{name}: missing required field {field!r}")

    got_locs = actual.get("locations", [])
    want_locs = expected.get("locations", [])
    if len(got_locs) != len(want_locs):
        fail(
            messages,
            f"{name}: expected {len(want_locs)} location(s), got {len(got_locs)}",
        )
        return

    for index, (got, want) in enumerate(zip(got_locs, want_locs)):
        path = f"{name}.locations[{index}]"
        if got.get("loc") != want.get("loc"):
            fail(
                messages,
                f"{path}.loc: expected {want.get('loc')!r}, got {got.get('loc')!r}",
            )
        closed = got.get("post") is None
        if closed != want.get("closed"):
            fail(
                messages,
                f"{path}: expected closed={want.get('closed')}, got {closed}",
            )
        check_close(path, got.get("close"), messages)
        if got.get("close") != want.get("close"):
            fail(
                messages,
                f"{path}.close: expected {want.get('close')!r}, "
                f"got {got.get('close')!r}",
            )
        check_steps(path, got.get("steps", []), want.get("steps", []), messages)


NEGATIVE_FIXTURE = ROOT / "test" / "SimpTrace" / "OutsideRoot.lean"
SYMLINK_FIXTURE = ROOT / "test" / "SimpTrace" / "SymlinkEscape.lean"
SYMLINK_DIR = ROOT / "test" / "SimpTrace" / "linkescape"


def check_symlink_containment(messages: list[str]) -> None:
    """A symlink under the package root must not become a write primitive.

    Textual `..` collapsing does not see through a symlink, so containment has
    to compare realpath-resolved paths. Creates the symlink, compiles a fixture
    aimed through it, and requires refusal with no file written.
    """
    if not SYMLINK_FIXTURE.is_file():
        fail(messages, f"missing symlink fixture {SYMLINK_FIXTURE.name}")
        return

    target = pathlib.Path("/tmp/simp_trace_symlink_check.json")
    for path in (target,):
        try:
            path.unlink()
        except FileNotFoundError:
            pass
    try:
        SYMLINK_DIR.unlink()
    except FileNotFoundError:
        pass

    SYMLINK_DIR.symlink_to("/tmp")
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(SYMLINK_FIXTURE.relative_to(ROOT))],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        output = result.stdout + result.stderr
        if result.returncode == 0:
            fail(messages, f"{SYMLINK_FIXTURE.name}: compiled without error; "
                           f"a path through a symlink must be rejected")
        if "refusing to write outside the package root" not in output:
            fail(
                messages,
                f"{SYMLINK_FIXTURE.name}: expected the containment error, got:\n"
                f"    {output.strip()[:300]}",
            )
        if target.exists():
            fail(messages, f"{SYMLINK_FIXTURE.name}: wrote {target} through a symlink")
            target.unlink()
    finally:
        try:
            SYMLINK_DIR.unlink()
        except FileNotFoundError:
            pass


def check_path_containment(messages: list[str]) -> None:
    """The out-clause must refuse to write outside the package root.

    Compiles a fixture that aims at an absolute path in /tmp and requires both
    that the compile fails with the containment error and that no file appears.
    A tactic that can write anywhere is a hazard regardless of what it traces.
    """
    if not NEGATIVE_FIXTURE.is_file():
        fail(messages, f"missing negative fixture {NEGATIVE_FIXTURE.name}")
        return

    target = pathlib.Path("/tmp/simp_trace_escape_check.json")
    try:
        target.unlink()
    except FileNotFoundError:
        pass

    result = subprocess.run(
        ["lake", "env", "lean", str(NEGATIVE_FIXTURE.relative_to(ROOT))],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    output = result.stdout + result.stderr

    if result.returncode == 0:
        fail(messages, f"{NEGATIVE_FIXTURE.name}: compiled without error; "
                       f"an out-of-root path must be rejected")
    if "refusing to write outside the package root" not in output:
        fail(
            messages,
            f"{NEGATIVE_FIXTURE.name}: expected the containment error, got:\n"
            f"    {output.strip()[:300]}",
        )
    if target.exists():
        fail(messages, f"{NEGATIVE_FIXTURE.name}: wrote {target} outside the root")
        target.unlink()


def main() -> int:
    if not EXPECTED_DIR.is_dir():
        print(f"missing expected directory: {EXPECTED_DIR}", file=sys.stderr)
        return 1

    expected_files = sorted(EXPECTED_DIR.glob("*.json"))
    if not expected_files:
        print(f"no expected skeletons in {EXPECTED_DIR}", file=sys.stderr)
        return 1

    messages: list[str] = []
    checked = 0

    for expected_path in expected_files:
        name = expected_path.name
        actual_path = OUT_DIR / name
        if not actual_path.is_file():
            fail(
                messages,
                f"{name}: no trace produced at {actual_path.relative_to(ROOT)}; "
                f"run `lake env lean test/SimpTrace/Fixtures.lean` first",
            )
            continue

        try:
            actual = json.loads(actual_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            fail(messages, f"{name}: produced trace is not valid JSON: {exc}")
            continue

        expected = json.loads(expected_path.read_text(encoding="utf-8"))
        check_trace(name, actual, expected, messages)
        checked += 1

    # Report traces that exist but have no committed skeleton, so a new fixture
    # cannot be added without an expectation.
    for actual_path in sorted(OUT_DIR.glob("*.json")):
        if not (EXPECTED_DIR / actual_path.name).is_file():
            fail(
                messages,
                f"{actual_path.name}: trace has no expected skeleton in "
                f"{EXPECTED_DIR.relative_to(ROOT)}",
            )

    check_path_containment(messages)
    check_symlink_containment(messages)

    if messages:
        for message in messages:
            print(f"FAIL {message}")
        print(f"\n{len(messages)} problem(s) across {checked} checked trace(s)")
        return 1

    print(f"OK: {checked} simp_trace fixture(s) match their expected skeletons, "
          f"and out-of-root paths (including through symlinks) are refused")
    return 0


if __name__ == "__main__":
    sys.exit(main())
