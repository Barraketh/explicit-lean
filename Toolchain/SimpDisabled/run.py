#!/usr/bin/env python3
"""Fail-closed compiler driver for certification.

This driver never selects elan's ordinary compiler.  It verifies the private
patched artifact, forces the engine option on, and promotes only ``hasSorry``
to an error.  An arbitrary axiom is intentionally outside this diagnostic.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
_BUILD = __import__("importlib.util").util.spec_from_file_location(
    "simp_disabled_build", Path(__file__).with_name("build.py")
)
if _BUILD is None or _BUILD.loader is None:
    raise RuntimeError("cannot load private simp-disabled build module")
_build = __import__("importlib.util").util.module_from_spec(_BUILD)
_BUILD.loader.exec_module(_build)


def verify() -> dict[str, object]:
    manifest = _build.expected_manifest()
    if manifest is None or not _build.artifact_is_fresh():
        raise RuntimeError(
            "patched Lean artifact is missing or stale; run build.py explicitly "
            "and refusing stock Lean fallback"
        )
    binary = _build.BINARY
    if not binary.is_file():
        raise RuntimeError("patched Lean binary is missing")
    identity = _build.version()
    if manifest.get("compilerIdentity") != identity:
        raise RuntimeError("patched Lean identity differs from its manifest")
    if manifest.get("guardOption") != "explicitLean.simpDisabled=true":
        raise RuntimeError("manifest does not certify the simp-disabled option")
    return manifest


def command(arguments: list[str]) -> list[str]:
    forbidden = {
        "-DexplicitLean.simpDisabled=false",
        "-DexplicitLean.simpDisabled=false\n",
        "-DexplicitLean.certification=false",
        "--incr-load",
    }
    if any(argument in forbidden - {"--incr-load"} for argument in arguments):
        raise RuntimeError("certification cannot override certification guards")
    for index, argument in enumerate(arguments):
        if argument == "-D" and index + 1 < len(arguments):
            argument = arguments[index + 1]
        if re.fullmatch(r"-?D?explicitLean\.simpDisabled=false", argument):
            raise RuntimeError("certification cannot override explicitLean.simpDisabled")
    if any(argument.startswith("--incr-load") or argument == "-Z" or argument.startswith("-Z") for argument in arguments):
        raise RuntimeError("certification rejects incremental-load snapshots")
    return [
        str(_build.BINARY),
        "-DexplicitLean.simpDisabled=true",
        "-DexplicitLean.certification=true",
        "-E", "hasSorry",
        *arguments,
    ]


def _fresh_output(arguments: list[str]) -> None:
    outputs: list[str] = []
    index = 0
    while index < len(arguments):
        argument = arguments[index]
        if argument in {"-o", "--o"}:
            if index + 1 >= len(arguments):
                raise RuntimeError("compiler output option has no path")
            outputs.append(arguments[index + 1])
            index += 2
            continue
        for prefix in ("-o", "--o="):
            if argument.startswith(prefix) and len(argument) > len(prefix):
                outputs.append(argument[len(prefix):])
                break
        index += 1
    for raw in outputs:
        path = Path(raw).expanduser()
        if not path.is_absolute():
            path = ROOT / path
        if path.exists():
            raise RuntimeError(f"certification output must be fresh: {path}")


def run(arguments: list[str]) -> subprocess.CompletedProcess[str]:
    verify()
    _fresh_output(arguments)
    environment = os.environ.copy()
    environment["LEAN_SYSROOT"] = str(_build.SYSROOT)
    environment["EXPLICIT_LEAN_SIMP_DISABLED"] = "1"
    environment["EXPLICIT_LEAN_CERTIFICATION"] = "1"
    core = str(_build.SYSROOT / "lib" / "lean")
    prior = environment.get("LEAN_PATH")
    environment["LEAN_PATH"] = core if not prior else core + os.pathsep + prior
    return subprocess.run(
        command(arguments), cwd=ROOT, env=environment, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False, timeout=1800,
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="compile with pinned patched Lean, simp disabled, and -E hasSorry"
    )
    parser.add_argument("--identity", action="store_true")
    parser.add_argument("arguments", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    try:
        manifest = verify()
        if args.identity and args.arguments:
            raise RuntimeError("--identity does not accept compiler arguments")
        if args.identity:
            print(json.dumps({
                "binary": str(_build.BINARY),
                "sysroot": str(_build.SYSROOT),
                "compilerIdentity": manifest["compilerIdentity"],
                "guardOption": manifest["guardOption"],
                "guardArguments": manifest["guardArguments"],
                "guardEnvironment": manifest["guardEnvironment"],
                "diagnostic": manifest["hasSorryDiagnostic"],
            }, indent=2, sort_keys=True))
            return 0
        arguments = list(args.arguments)
        if arguments[:1] == ["--"]:
            arguments = arguments[1:]
        result = run(arguments)
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"simp-disabled certification failed closed: {error}", file=sys.stderr)
        return 1
    print(result.stdout, end="")
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
