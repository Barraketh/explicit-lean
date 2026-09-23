#!/usr/bin/env python3
"""Exercise quantified proposition recording through ordinary explicit_rw replay."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "Experiment" / "pipeline"))
import render as R  # noqa: E402

FIXTURE = ROOT / "test" / "SimpTrace" / "QuantifiedPropReplay.lean"
NEGATIVE = ROOT / "test" / "SimpTrace" / "QuantifiedPropUnassigned.lean"


def run_lean(path: pathlib.Path, *, success: bool = True) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        capture_output=True, text=True, timeout=1800,
    )
    if (proc.returncode == 0) != success:
        raise AssertionError(
            f"Lean returned {proc.returncode} for {path}:\n{proc.stdout}{proc.stderr}"
        )
    return proc


def render_one(trace_path: pathlib.Path, source_text: str) -> tuple[str, dict]:
    raw = json.loads(trace_path.read_text(encoding="utf-8"))
    rendered, _ = R.render_trace(
        {"schema": "simp-trace-v2", "site": {"sourceArgs": raw["sourceArgs"]},
         "locations": raw["locations"]},
        source_text=source_text,
    )
    if len(rendered) != 1:
        raise AssertionError(f"expected one rendered location: {rendered!r}")
    return rendered[0], raw


def main() -> None:
    private = ROOT / ".lake" / "private"
    private.mkdir(parents=True, exist_ok=True)
    run_dir = pathlib.Path(tempfile.mkdtemp(prefix="quantified-prop-", dir=private))
    paths = {
        "GLOBAL": run_dir / "global.json",
        "LOCAL": run_dir / "local.json",
        "FALSE": run_dir / "false.json",
    }
    source = FIXTURE.read_text(encoding="utf-8")
    for key, path in paths.items():
        source = source.replace(f"QUANTIFIED_PROP_{key}_TRACE_PATH", path.as_posix())
    recorded = run_dir / "QuantifiedPropRecorded.lean"
    recorded.write_text(source, encoding="utf-8")
    run_lean(recorded)

    rendered: dict[str, str] = {}
    raw: dict[str, dict] = {}
    for key, path in paths.items():
        rendered[key], raw[key] = render_one(path, source)
    if "prop_true " not in rendered["GLOBAL"] or "fixtureGlobal at" not in rendered["GLOBAL"]:
        raise AssertionError(f"global proposition did not retain source term: {rendered['GLOBAL']}")
    if "prop_true h" not in rendered["LOCAL"]:
        raise AssertionError(f"local proposition did not retain source term: {rendered['LOCAL']}")
    if "prop_false h" not in rendered["FALSE"]:
        raise AssertionError(f"negative proposition did not retain source term: {rendered['FALSE']}")
    for key in paths:
        for step in raw[key]["locations"][0]["steps"]:
            if step.get("unresolved") == "unapplied_quantified_prop":
                raise AssertionError(f"obsolete quantified-proposition classification survived: {step}")

    replay = FIXTURE.read_text(encoding="utf-8")
    for key, call in rendered.items():
        marker = next(line.strip() for line in FIXTURE.read_text(encoding="utf-8").splitlines()
                      if f"QUANTIFIED_PROP_{key}_TRACE_PATH" in line)
        replay = replay.replace(marker, call)
    replayed = run_dir / "QuantifiedPropReplayed.lean"
    replayed.write_text(replay, encoding="utf-8")
    run_lean(replayed)

    negative_source = NEGATIVE.read_text(encoding="utf-8").replace(
        "QUANTIFIED_PROP_UNASSIGNED_TRACE_PATH", (run_dir / "unassigned.json").as_posix()
    )
    negative = run_dir / "QuantifiedPropUnassigned.lean"
    negative.write_text(negative_source, encoding="utf-8")
    failed = run_lean(negative, success=False)
    output = failed.stdout + failed.stderr
    if "`simp_trace` made no progress" not in output:
        raise AssertionError(f"undetermined value binder did not fail closed:\n{output}")

    print("quantified proposition recorder/render/replay: passed")
    for key in paths:
        print(f"  {key.lower()}: {rendered[key]}")
    print("  undetermined value binder: simp refused the rewrite")


if __name__ == "__main__":
    main()
