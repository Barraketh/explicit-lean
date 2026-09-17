#!/usr/bin/env python3
"""Regression tests for validated suffixed simp-trace outputs."""

from __future__ import annotations

import importlib.util
import json
import pathlib
import shutil
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER_PATH = ROOT / "Experiment" / "check_simp_trace.py"


def load_checker():
    spec = importlib.util.spec_from_file_location("simp_trace_checker", CHECKER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load simp-trace checker")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_checker(checker, out_dir: pathlib.Path, expected_dir: pathlib.Path) -> int:
    checker.OUT_DIR = out_dir
    checker.EXPECTED_DIR = expected_dir
    checker.check_fixture_compiles = lambda messages: None
    checker.check_replay_traces = lambda messages: None
    checker.check_path_containment = lambda messages: None
    checker.check_symlink_containment = lambda messages: None
    old_argv = sys.argv
    sys.argv = [str(CHECKER_PATH), "--allow-suffixed-invocations"]
    try:
        return checker.main()
    finally:
        sys.argv = old_argv


def main() -> int:
    source_out = ROOT / "test" / "SimpTrace" / "out"
    source_expected = ROOT / "test" / "SimpTrace" / "expected"
    checker = load_checker()
    with tempfile.TemporaryDirectory(prefix="simp-trace-suffix-", dir=ROOT) as raw:
        work = pathlib.Path(raw)
        out_dir, expected_dir = work / "out", work / "expected"
        out_dir.mkdir()
        expected_dir.mkdir()
        shutil.copy2(source_expected / "chained.json", expected_dir / "chained.json")
        base = source_out / "chained.json"
        suffix = out_dir / "chained.1.json"
        if not base.is_file():
            raise AssertionError("run Fixtures.lean first to produce chained.json")
        shutil.copy2(base, out_dir / base.name)
        # The checker regression is intentionally isolated from the recorder's
        # current multi-invocation naming.  A copied canonical trace is a
        # structurally valid known suffix, which lets this test exercise the
        # suffix branch deterministically (including chained.1.json mutation).
        shutil.copy2(base, suffix)
        if run_checker(checker, out_dir, expected_dir) != 0:
            raise AssertionError("valid known suffix was rejected")

        forged = json.loads((out_dir / suffix.name).read_text(encoding="utf-8"))
        forged["locations"][0]["steps"][0]["kind"] = "bogus"
        (out_dir / suffix.name).write_text(json.dumps(forged), encoding="utf-8")
        if run_checker(checker, out_dir, expected_dir) == 0:
            raise AssertionError("forged suffixed trace was accepted")

        shutil.copy2(base, suffix)
        shutil.copy2(base, out_dir / "unknown.1.json")
        if run_checker(checker, out_dir, expected_dir) == 0:
            raise AssertionError("unknown suffixed trace was accepted")
    print("OK: suffixed traces are validated; forged and unknown suffixes fail")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
