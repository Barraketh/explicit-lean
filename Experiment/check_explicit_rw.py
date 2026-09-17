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
import os
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
FIXTURE_DIR = REPO / "test" / "ExplicitRw"
REJECTED_DIR = FIXTURE_DIR / "RejectedSyntax"
SWEEP_DIR = FIXTURE_DIR / "sweep"
# Slots swept by default; the rest need `T2_FULL_SWEEP=1` (see run_escape_sweep).
SWEEP_SLOTS_DEFAULT = 2
# The only escape probes the *parser* cannot stop; see run_escape_sweep.
POST_PARSE_ESCAPES = {"admit", "$x"}
# The only axioms a replayed proof may depend on: Lean's three classical
# axioms, which ordinary Mathlib lemmas already use. Anything else — `sorryAx`
# from an admitted proof, or a freshly declared `axiom` — fails the audit.
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
MODULE = "ExplicitLean.ExplicitRw"

# Fixtures that deliberately contain failing proofs, checked via `#guard_msgs`.
# Listed so the report distinguishes them from the positive fixtures.
NEGATIVE = {"Negative.lean", "Strict.lean"}

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


def run_escape_sweep(full: bool = False) -> tuple[int, str, float]:
    """Compile one probe per (term, slot) and classify parse vs elaboration.

    An `escape` term must be rejected by the *parser*; a `benign` term must
    reach elaboration. By default only the first `SWEEP_SLOTS_DEFAULT` slots are
    swept, because the full matrix is ~5 minutes of serial Lean; set
    `T2_FULL_SWEEP=1` for all of them. The subset is documented in the report
    line so the number in RESULT.md is never ambiguous about what it covers.
    """
    import json
    import tempfile

    spec = json.loads((SWEEP_DIR / "probes.json").read_text(encoding="utf-8"))
    slots = dict(spec["slots"])
    if not full:
        slots = {k: v for k, v in list(slots.items())[:SWEEP_SLOTS_DEFAULT]}

    start = time.monotonic()
    escapes = benigns = esc_bad = ben_bad = 0
    parse_rejected = elab_rejected = 0
    failures: list[str] = []
    for kind in ("escape", "benign"):
        for term in spec[kind]:
            for slot_name, slot in slots.items():
                # Each slot brings its own goal, so a probe reaches the term
                # rather than dying on a position the goal cannot support. The
                # step is the file's last tactic: a trailing one would be
                # absorbed as an argument, since application spans lines.
                src = ("import ExplicitLean.ExplicitRw\n"
                       "set_option linter.unusedVariables false\n"
                       "example (n a b : Nat) (f' g : Nat → Nat) (p : Prop)\n"
                       f"    (h : a = b) {slot['binders']} : {slot['goal']} := by\n"
                       "  " + slot["tmpl"].replace("{T}", term) + "\n")
                with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                                 dir=str(REPO)) as fh:
                    fh.write(src)
                    probe = Path(fh.name)
                try:
                    code, out, _ = run(["lake", "env", "lean",
                                        str(probe.relative_to(REPO))])
                finally:
                    probe.unlink(missing_ok=True)
                parsed_off = any(m in out for m in (
                    "unexpected token", "unexpected identifier", "expected token",
                    "missing end of character literal"))
                if kind == "escape":
                    escapes += 1
                    if parsed_off:
                        parse_rejected += 1
                    elif term in POST_PARSE_ESCAPES and code != 0 and any(
                            m in out for m in ("explicit_rw:", "Unknown identifier")):
                        # Rejected after the parser, and *attributably*: the
                        # message must name this tactic or the unresolved
                        # identifier, and the probe must exit non-zero. Without
                        # that, an unrelated error would be credited as a refusal.
                        elab_rejected += 1
                    else:
                        esc_bad += 1
                        why = ("no error at all" if not out.strip()
                               else "survived the parser")
                        failures.append(f"ESCAPE {why}: {term!r} in slot {slot_name}")
                else:
                    benigns += 1
                    if parsed_off:
                        ben_bad += 1
                        failures.append(f"BENIGN parse-rejected: {term!r} "
                                        f"in slot {slot_name}")
    elapsed = time.monotonic() - start
    if failures:
        return 1, "\n  ".join(failures[:20]), elapsed
    scope = "all slots" if full else f"{len(slots)} of {len(spec['slots'])} slots"
    return 0, (f"{escapes} escape probes all rejected "
               f"({parse_rejected} by the parser, {elab_rejected} at "
               f"elaboration), {benigns} benign all parse ({scope})"), elapsed


def run_axiom_check(fixtures: list[Path]) -> tuple[int, str, float]:
    """`#print axioms` every theorem of the positive fixtures, against an allowlist.

    The fixture bodies are concatenated into one scratch file with their imports
    hoisted, then one `#print axioms` per theorem is appended and the reported
    axiom set is parsed.

    The governing rule forbids `sorry`/`admit` *and* new axioms. An earlier
    version grepped the output for `sorryAx`, which enforced only the first half:
    a theorem depending on a freshly declared `axiom` prints that axiom's name
    and no `sorryAx`, so it passed. Comparing against an allowlist closes that,
    and is the honest reading of the rule — anything outside
    `ALLOWED_AXIOMS` is a new axiom by definition.
    """
    import re
    import tempfile

    positives = [f for f in fixtures if f.name not in NEGATIVE]
    imports: list[str] = []
    bodies: list[str] = []
    prints: list[str] = []
    for f in positives:
        src = f.read_text(encoding="utf-8")
        body_lines = []
        for line in src.splitlines():
            if line.startswith("import "):
                if line not in imports:
                    imports.append(line)
            else:
                body_lines.append(line)
        bodies.append("\n".join(body_lines))
        ns_match = re.search(r"^namespace (\S+)", src, re.M)
        ns = ns_match.group(1) if ns_match else ""
        for m in re.finditer(r"^theorem (\w+)", src, re.M):
            prints.append(f"#print axioms {ns}.{m.group(1)}" if ns else
                          f"#print axioms {m.group(1)}")

    if not prints:
        return 1, "no theorems found in the positive fixtures", 0.0

    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     dir=str(REPO)) as fh:
        fh.write("\n".join(imports) + "\n")
        fh.write("\n".join(bodies) + "\n")
        fh.write("\n".join(prints) + "\n")
        scratch = Path(fh.name)
    try:
        code, output, elapsed = run(["lake", "env", "lean",
                                     str(scratch.relative_to(REPO))])
        if code != 0:
            return 1, f"the axiom-audit file failed to compile:\n{output}", elapsed
        # Parse every `#print axioms` line and compare its axiom set with the
        # allowlist, rather than searching the text for one forbidden name.
        offenders: list[str] = []
        reported = 0
        clean = 0
        for line in output.splitlines():
            m = re.match(r"'(?P<thm>[^']+)' depends on axioms: \[(?P<ax>[^\]]*)\]",
                         line.strip())
            if m:
                reported += 1
                axs = {a.strip() for a in m.group("ax").split(",") if a.strip()}
                extra = axs - ALLOWED_AXIOMS
                if extra:
                    offenders.append(f"{m.group('thm')} depends on "
                                     f"{sorted(extra)}")
                continue
            if "does not depend on any axioms" in line:
                reported += 1
                clean += 1
        if offenders:
            return 1, ("fixture theorems depend on axioms outside the allowlist "
                       f"{sorted(ALLOWED_AXIOMS)}:\n  "
                       + "\n  ".join(offenders)), elapsed
        if reported != len(prints):
            return 1, (f"expected {len(prints)} axiom reports, parsed {reported}"
                       f" — the audit is not covering every theorem"), elapsed
        return 0, (f"{len(prints)} theorems, all within the allowlist "
                   f"({clean} axiom-free)"), elapsed
    finally:
        scratch.unlink(missing_ok=True)


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

    # Every theorem in the positive fixtures must be free of `sorryAx`.
    # A replayed proof that depends on it is a proof of nothing: round 6 found a
    # false theorem admitted that way, through an elaboration failure that logged
    # a recoverable error and returned `sorryAx` while the harness stayed green
    # (the file elaborated with no output and exited 0). Asserting this here, on
    # every run, is what makes that class of defect visible to CI rather than to
    # the next reviewer.
    code, output, elapsed = run_axiom_check(fixtures)
    if code != 0:
        print("check_explicit_rw: FAIL: axiom audit")
        print(output)
        return 1
    print(f"  axiom audit: {output} ({elapsed:.1f}s)")

    # The escape sweep: the artefact behind RESULT.md's escape-count claim.
    code, output, elapsed = run_escape_sweep(full=os.environ.get("T2_FULL_SWEEP"))
    if code != 0:
        print("check_explicit_rw: FAIL: escape sweep")
        print(output)
        return 1
    print(f"  escape sweep: {output} ({elapsed:.1f}s)")

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
