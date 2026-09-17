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
               "intro_ctx", "congr"}

# Close forms the amended spec defines.  `omega` is a side-condition-only form
# (a user-supplied `omega` discharger); `nofun` closes a goal refutable by empty
# pattern matching, e.g. `reduceCtorEq`'s constructor disequality (spec
# fd4419b).  `assumption:`, `absurd:` and `unresolved:` are prefixes.  `unresolved:` is the spec's classified outcome:
# the call still leaves stock simp's goal state and reports one error line.
CLOSE_EXACT = {"rfl", "true_intro", "decide", "omega", "nofun"}
CLOSE_PREFIXES = ("assumption:", "absurd:", "unresolved:")


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

        for field in ("kind", "pos", "name", "dir", "source", "by", "local",
                      "prop", "arg", "args"):
            if field in want:
                if got.get(field) != want[field]:
                    fail(
                        messages,
                        f"{where}.{field}: expected {want[field]!r}, "
                        f"got {got.get(field)!r}",
                    )
            elif field in got and field in ("name", "dir", "source", "prop",
                                            "local", "arg", "args"):
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
            by = got.get("by")
            if by not in ("rfl", "decide") and not (
                isinstance(by, str) and by.startswith("unresolved:simproc:")
            ):
                fail(messages, f"{where}: `eq` step with by={by!r}")
        # The amended spec's lemma-headed simproc proofs: a `rw` may carry a
        # `source` naming the simproc the lemma application came from.  When it
        # does, the lemma's discharged conditions must appear as `side` entries,
        # or the step tells a replayer to apply a conditional lemma with nothing
        # to discharge its hypothesis.
        # A `rw` from a simproc-lemma or a user congruence theorem must carry a
        # `side` per condition the lemma has -- but a lemma with *no* conditions
        # legitimately has none, so the expectation decides. Comparing counts
        # (done below) is the real check; asserting non-emptiness here would
        # reject an unconditional lemma such as `fixtureTag_iff`.
        if (
            kind == "rw"
            and got.get("source")
            and want.get("side")
            and not got.get("side")
        ):
            fail(
                messages,
                f"{where}: `rw` from {got['source']!r} carries no `side` "
                f"sub-trace where one is expected",
            )

        # `congr` (spec 3b17247): the step must name the argument it rewrote and
        # carry the nested steps that rewrite it, and those nested positions are
        # *relative to that argument*.  A nested step whose position is not
        # relative would send a replayer to the wrong subterm, so the nesting is
        # checked recursively here, exactly as for the top level.
        # A `rw` with `"source": "congr"` is a user `@[congr]` theorem (spec
        # 2e73661): it must carry one `side` per hypothesis, or replay has
        # nothing to prove the theorem's arguments with.
        if kind == "rw" and got.get("source") == "congr" and not got.get("side"):
            fail(
                messages,
                f"{where}: `rw` from a user congruence theorem "
                f"{got.get('name')!r} carries no `side` sub-traces",
            )

        if kind == "congr":
            if not isinstance(got.get("arg"), int):
                fail(messages, f"{where}: `congr` step without an integer `arg`")
            if not got.get("steps"):
                fail(messages, f"{where}: `congr` step with no nested `steps`")
            check_steps(
                f"{where}.steps",
                got.get("steps", []),
                want.get("steps", []),
                messages,
            )
        elif got.get("steps"):
            fail(messages, f"{where}: nested `steps` on a {kind!r} step")

        if kind == "unfold" and not got.get("name"):
            fail(messages, f"{where}: `unfold` step without a constant name")

        # The amended spec's `prop` flag: present only on `rw`, and only with
        # the two values replay knows how to act on (`eq_true` / `eq_false`).
        prop = got.get("prop")
        if prop is not None:
            if kind != "rw":
                fail(messages, f"{where}: `prop` flag on a {kind!r} step")
            if prop not in ("true", "false"):
                fail(messages, f"{where}: `prop` flag with value {prop!r}")
        if kind == "intro_ctx" and not got.get("name"):
            fail(messages, f"{where}: `intro_ctx` step without a hypothesis name")

        # `ctxIndex` is `LocalDecl.index` -- an identifier for the declaration,
        # not a `rename_i` argument (spec 3b17247). It is only required to be a
        # non-negative integer; no relationship to the count of inaccessible
        # hypotheses is asserted, because none holds.
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
                # `pre`/`post` (spec e95c745): a side trace says what its goal
                # started as and what remains, like a location. Without them a
                # replayer cannot tell whether the side goal is closed.
                if "pre" not in gs:
                    fail(messages, f"{side_path}: side trace has no `pre`")
                if "post" not in gs:
                    fail(messages, f"{side_path}: side trace has no `post`")
                for field in ("pre", "post"):
                    if field in ws and gs.get(field) != ws.get(field):
                        fail(
                            messages,
                            f"{side_path}.{field}: expected {ws.get(field)!r}, "
                            f"got {gs.get(field)!r}",
                        )

                # `intros` (spec 2e73661): the antecedents an implication-shaped
                # congruence hypothesis introduces before its steps. Each must be
                # a non-empty name a generator can `intro`.
                got_intros = gs.get("intros", [])
                if got_intros != ws.get("intros", []):
                    fail(
                        messages,
                        f"{side_path}.intros: expected {ws.get('intros', [])!r}, "
                        f"got {got_intros!r}",
                    )
                for n in got_intros:
                    if not isinstance(n, str) or not n:
                        fail(messages, f"{side_path}.intros: {n!r} is not a name")
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


# Fixture files that must compile cleanly.  The negative fixtures
# (`OutsideRoot`, `SymlinkEscape`) are checked separately and are *expected* to
# fail, so they are not listed here.
POSITIVE_FIXTURES = ("test/SimpTrace/Fixtures.lean",
                     "test/SimpTrace/IsEmptyBasicTraced.lean")

# Fixtures whose calls are classified `unresolved:`, so the file itself exits 1
# by design.  Their traces are still compared against skeletons; only the exit
# code is not required to be zero.
UNRESOLVED_FIXTURES = ("test/SimpTrace/UnresolvedFixtures.lean",)


def check_fixture_compiles(messages: list[str]) -> None:
    """Every positive fixture must compile with exit code 0.

    Without this the suite could be green while a fixture file failed to
    compile: `simp_trace` reports an unresolved call with `logError`, which
    makes the *file* fail even though each trace it did write is well formed.
    REVIEW-4 defect 4 was exactly that -- `Fixtures.lean` exiting 1 while the
    result was reported as a pass. The traces are regenerated here too, so the
    skeleton comparison below always runs against current output.
    """
    for rel in POSITIVE_FIXTURES:
        result = subprocess.run(
            ["lake", "env", "lean", rel],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            output = (result.stdout + result.stderr).strip()
            fail(
                messages,
                f"{rel}: exited {result.returncode}; a positive fixture must "
                f"compile cleanly:\n    {output[:500]}",
            )

    # The unresolved fixtures are run for their traces only.  Each must report
    # at least one classified line: a fixture that stopped being unresolved
    # belongs in `Fixtures.lean`, and silence here would hide that.
    for rel in UNRESOLVED_FIXTURES:
        result = subprocess.run(
            ["lake", "env", "lean", rel],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        output = result.stdout + result.stderr
        if "simp_trace unresolved:" not in output:
            fail(
                messages,
                f"{rel}: reported no `simp_trace unresolved:` line; if its calls "
                f"now trace cleanly, move them to Fixtures.lean",
            )


# Directories the measurement modules write to, and the module that writes each.
MEASUREMENT_DIRS = (
    ("IsEmptyBasicTraced", ROOT / "test" / "SimpTrace" / "isempty_out", ""),
    ("NontrivialDefsTraced", ROOT / "test" / "SimpTrace" / "meas_out",
     "NontrivialDefsTraced_"),
    ("FunctionDefsTraced", ROOT / "test" / "SimpTrace" / "meas_out",
     "FunctionDefsTraced_"),
    ("ExistsUniqueTraced", ROOT / "test" / "SimpTrace" / "meas_out",
     "ExistsUniqueTraced_"),
    ("FunctionBasicTraced", ROOT / "test" / "SimpTrace" / "meas_out",
     "FunctionBasicTraced_"),
)


def tally(paths: list[pathlib.Path]) -> dict:
    """Count calls, steps and kinds over a set of traces.

    Steps nested inside `congr` steps and inside `side` sub-traces are counted
    too: they are steps a replayer must perform, so leaving them out understates
    the trace. Byte counts are the files' own sizes.
    """
    kinds: dict[str, int] = {}
    steps = 0
    per_call = []

    def walk(step_list: list) -> int:
        nonlocal steps
        n = 0
        for st in step_list:
            kind = st.get("kind", "?")
            kinds[kind] = kinds.get(kind, 0) + 1
            steps += 1
            n += 1
            n += walk(st.get("steps", []))
            for side in st.get("side", []):
                n += walk(side.get("steps", []))
        return n

    total_bytes = 0
    for path in paths:
        total_bytes += path.stat().st_size
        trace = json.loads(path.read_text(encoding="utf-8"))
        count = 0
        for loc in trace.get("locations", []):
            count += walk(loc.get("steps", []))
        per_call.append(count)

    return {
        "calls": len(paths),
        "steps": steps,
        "kinds": dict(sorted(kinds.items(), key=lambda kv: (-kv[1], kv[0]))),
        "bytes": total_bytes,
        "min": min(per_call) if per_call else 0,
        "max": max(per_call) if per_call else 0,
    }


def report() -> int:
    """Print the measurement numbers, generated from the committed artefacts.

    RESULT.md's table is transcribed from this, so the counts cannot drift from
    what the tree actually produces -- REVIEW-5 defect 5, where four figures had
    gone stale. Run the five measurement modules first; this reads their output.
    """
    missing = []
    rows = []
    for name, directory, prefix in MEASUREMENT_DIRS:
        if not directory.is_dir():
            missing.append(f"{name}: {directory.relative_to(ROOT)} does not exist")
            continue
        paths = sorted(p for p in directory.glob(f"{prefix}*.json"))
        if not paths:
            missing.append(f"{name}: no traces under {directory.relative_to(ROOT)}")
            continue
        rows.append((name, tally(paths)))

    if missing:
        for line in missing:
            print(f"MISSING {line}", file=sys.stderr)
        print(
            "\nRun the five measurement modules first, e.g.\n"
            "  for f in IsEmptyBasicTraced NontrivialDefsTraced FunctionDefsTraced \\\n"
            "           ExistsUniqueTraced FunctionBasicTraced; do \\\n"
            "    lake env lean test/SimpTrace/$f.lean; done",
            file=sys.stderr,
        )
        return 1

    print("| file | calls | steps | kinds | bytes |")
    print("| --- | --- | --- | --- | --- |")
    totals = {"calls": 0, "steps": 0, "bytes": 0}
    all_kinds: dict[str, int] = {}
    for name, t in rows:
        kinds = ", ".join(f"`{k}` {v}" for k, v in t["kinds"].items())
        print(
            f"| `{name}.lean` | {t['calls']} | {t['steps']} | {kinds} | "
            f"{t['bytes']} |"
        )
        for key in totals:
            totals[key] += t[key]
        for k, v in t["kinds"].items():
            all_kinds[k] = all_kinds.get(k, 0) + v
    kinds = ", ".join(
        f"`{k}` {v}"
        for k, v in sorted(all_kinds.items(), key=lambda kv: (-kv[1], kv[0]))
    )
    print(
        f"| **total** | **{totals['calls']}** | **{totals['steps']}** | {kinds} | "
        f"**{totals['bytes']}** |"
    )
    return 0


def main() -> int:
    if "--report" in sys.argv[1:]:
        return report()

    if not EXPECTED_DIR.is_dir():
        print(f"missing expected directory: {EXPECTED_DIR}", file=sys.stderr)
        return 1

    expected_files = sorted(EXPECTED_DIR.glob("*.json"))
    if not expected_files:
        print(f"no expected skeletons in {EXPECTED_DIR}", file=sys.stderr)
        return 1

    messages: list[str] = []
    checked = 0

    # Compile the positive fixtures first: this both regenerates the traces the
    # comparison below reads and makes a nonzero exit a hard failure.
    check_fixture_compiles(messages)

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
