#!/usr/bin/env python3
"""Return-code and fresh-output controls for T56 certification mode."""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "Toolchain" / "SimpDisabled" / "build.py"
RUN = ROOT / "Toolchain" / "SimpDisabled" / "run.py"
TESTS = ROOT / "test" / "SimpDisabled"
EXPECTED_DIAGNOSTIC = "explicitLean.simpDisabled: stock"


def checked(command: list[str], *, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False, timeout=1800,
    )


def lake_path() -> str:
    result = checked(["lake", "env", "printenv", "LEAN_PATH"])
    if result.returncode not in {0, 1} or not result.stdout.strip():
        raise RuntimeError(f"cannot obtain the pinned package search path:\n{result.stdout}")
    return result.stdout.strip().splitlines()[0]


def stock_binary() -> Path:
    prefix = checked(["lean", "--print-prefix"])
    if prefix.returncode != 0:
        raise RuntimeError(f"cannot locate stock pinned Lean:\n{prefix.stdout}")
    binary = Path(prefix.stdout.strip().splitlines()[-1]) / "bin" / "lean"
    identity = checked([str(binary), "--version"])
    expected = "version 4.32.2"
    if identity.returncode != 0 or expected not in identity.stdout or "commit f3b06c705e6c85f5314019d5d3baab0fec5b580c" not in identity.stdout:
        raise RuntimeError(f"off-mode Lean is not pinned:\n{identity.stdout}")
    return binary


def certification_env() -> dict[str, str]:
    environment = os.environ.copy()
    environment["LEAN_PATH"] = lake_path()
    return environment


def compile_case(
    name: str, *, certified: bool, succeeds: bool, env: dict[str, str]
) -> str:
    with tempfile.TemporaryDirectory(prefix=f"t56-{name}-", dir=ROOT / ".lake" / "SimpDisabled") as raw:
        output = Path(raw) / "fresh.olean"
        command = [str(stock_binary())] if not certified else [sys.executable, str(RUN), "--"]
        command += ["-o", str(output), str(TESTS / f"{name}.lean")]
        result = checked(command, env=env)
        output_exists = output.is_file() and output.stat().st_size > 0
        if succeeds and (result.returncode != 0 or not output_exists):
            raise AssertionError(
                f"{name}: expected success and fresh output, got {result.returncode};\n{result.stdout}"
            )
        if not succeeds and (result.returncode == 0 or output_exists):
            raise AssertionError(
                f"{name}: expected failure without fresh output, got {result.returncode};\n{result.stdout}"
            )
        if not succeeds and certified and EXPECTED_DIAGNOSTIC not in result.stdout and name not in {"sorry", "sorryAx", "sorry_warn_disabled"}:
            raise AssertionError(f"{name}: missing engine diagnostic:\n{result.stdout}")
        return result.stdout


def compile_patched_off(manifest: dict[str, object], env: dict[str, str]) -> None:
    with tempfile.TemporaryDirectory(prefix="t56-patched-off-", dir=ROOT / ".lake" / "SimpDisabled") as raw:
        output = Path(raw) / "fresh.olean"
        off_env = env.copy()
        sysroot = Path(str(manifest["sysroot"]))
        off_env["LEAN_SYSROOT"] = str(sysroot)
        off_env["LEAN_PATH"] = str(sysroot / "lib" / "lean") + os.pathsep + lake_path()
        off_env.pop("EXPLICIT_LEAN_SIMP_DISABLED", None)
        result = checked([
            str(manifest["binary"]), "-DexplicitLean.simpDisabled=false",
            "-o", str(output), str(TESTS / "off.lean")
        ], env=off_env)
        if result.returncode != 0 or not output.is_file() or output.stat().st_size == 0:
            raise AssertionError(f"patched off-mode simp did not compile freshly:\n{result.stdout}")


def main() -> int:
    build = checked([sys.executable, str(BUILD), "--json"])
    if build.returncode != 0:
        print(build.stdout, file=sys.stderr, end="")
        return 1
    try:
        manifest = json.loads(build.stdout)
        if manifest.get("guardOption") != "explicitLean.simpDisabled=true":
            raise AssertionError("build manifest does not prove the guard option")
        identity = checked([sys.executable, str(RUN), "--identity"])
        if identity.returncode != 0:
            raise AssertionError(f"identity check failed:\n{identity.stdout}")
        proof = json.loads(identity.stdout)
        if (
            proof.get("guardOption") != "explicitLean.simpDisabled=true"
            or proof.get("guardArguments") != "-DexplicitLean.simpDisabled=true;-DexplicitLean.certification=true;-E hasSorry"
            or proof.get("guardEnvironment") != "EXPLICIT_LEAN_SIMP_DISABLED=1;EXPLICIT_LEAN_CERTIFICATION=1"
            or proof.get("diagnostic") != "-E hasSorry"
        ):
            raise AssertionError(f"driver did not prove certification settings: {proof}")
        env = certification_env()
        compile_case("off", certified=False, succeeds=True, env=env)
        compile_patched_off(manifest, env)
        for name in ("positive", "axiom_limitation"):
            compile_case(name, certified=True, succeeds=True, env=env)
        for name in ("simp", "dsimp", "meta_simp", "meta_dsimp", "try_simp", "mutate_env", "source_disable", "indirect_norm_num", "sorry", "sorryAx", "sorry_warn_disabled"):
            compile_case(name, certified=True, succeeds=False, env=env)
    except (AssertionError, OSError, RuntimeError, json.JSONDecodeError, subprocess.TimeoutExpired) as error:
        print(f"simp-disabled controls failed: {error}", file=sys.stderr)
        return 1
    print("simp-disabled certification controls: passed")
    print("arbitrary axiom: accepted by -E hasSorry; separate no-new-axiom comparison remains required")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
