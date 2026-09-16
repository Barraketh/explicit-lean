#!/usr/bin/env python3
"""Pure Python parity control for cold Lean frontend options.

The cold compiler and both native cold consumers must use the pinned
package-plus-async parser options.  Verification-only linter/heartbeat flags
are intentionally excluded because they change selector fingerprints.
"""
from __future__ import annotations

import re
from pathlib import Path

import cold_certified_module as cold


ROOT = Path(__file__).resolve().parents[1]
FRONTEND_OPTIONS = ROOT / "ExplicitLean/SimpEngine/FrontendOptions.lean"
ORACLE_SOURCE = ROOT / "Experiment/SimpEngineDeclarationOracle.lean"
COMMAND_AUDIT_SOURCE = ROOT / "Experiment/SimpEngineCommandAudit.lean"


def parse_set_chain(block: str, label: str) -> dict[str, bool | int]:
    lines = [line for line in block.splitlines() if "|>.set" in line]
    if not lines:
        raise SystemExit(f"native {label} option chain is empty")
    result: dict[str, bool | int] = {}
    for line in lines:
        match = re.fullmatch(r"\s*\|>\.set `([A-Za-z0-9_.]+) (true|false|\((\d+) : Nat\))\s*", line)
        if match is None:
            raise SystemExit(f"native {label} option syntax changed: {line!r}")
        name, raw, number = match.groups()
        if name in result:
            raise SystemExit(f"native {label} contains duplicate option {name}")
        result[name] = int(number) if number is not None else raw == "true"
    return result


def native_parser_options() -> dict[str, bool | int]:
    source = FRONTEND_OPTIONS.read_text(encoding="utf-8")
    package_match = re.search(
        r"def mathlibPackageOptions : Options :=(?P<body>.*?)\n/-- Package options",
        source,
        re.DOTALL,
    )
    parser_match = re.search(
        r"def mathlibParserOptions : Options :=(?P<body>.*?)\n\n/-- Mathlib package options",
        source,
        re.DOTALL,
    )
    if not all((package_match, parser_match)):
        raise SystemExit("native frontend option definitions changed shape")
    package = parse_set_chain(package_match.group("body"), "package")
    parser_async = re.findall(r"Elab\.async\.set mathlibPackageOptions (true|false)", parser_match.group("body"))
    if parser_async != ["true"]:
        raise SystemExit(f"native parser async option changed: {parser_async!r}")
    native = dict(package)
    native["Elab.async"] = True
    return native


def native_consumer_selection(path: Path) -> str:
    source = path.read_text(encoding="utf-8")
    matches = re.findall(
        r"let options := ExplicitLean\.SimpEngine\.([A-Za-z0-9_]+)", source
    )
    if matches != ["mathlibParserOptions"]:
        raise SystemExit(
            f"{path.name} must select mathlibParserOptions exactly once; found {matches!r}"
        )
    return matches[0]


def command_line_options() -> dict[str, bool | int]:
    result: dict[str, bool | int] = {}
    for option in cold.PLAIN_OPTIONS:
        if not isinstance(option, str) or not option.startswith("-D") or "=" not in option[2:]:
            raise SystemExit(f"invalid cold frontend option: {option!r}")
        name, raw = option[2:].split("=", 1)
        if name in result:
            raise SystemExit(f"cold PLAIN_OPTIONS contains duplicate option {name}")
        if raw in {"true", "false"}:
            value: bool | int = raw == "true"
        elif raw.isdecimal():
            value = int(raw)
        else:
            raise SystemExit(f"unsupported cold frontend option value: {option!r}")
        result[name] = value
    return result


def main() -> None:
    native = native_parser_options()
    actual = command_line_options()
    if actual != native:
        raise SystemExit(
            "cold PLAIN_OPTIONS diverges from native mathlibParserOptions\n"
            f"expected={native!r}\nfound={actual!r}"
        )
    selected = [native_consumer_selection(path) for path in (ORACLE_SOURCE, COMMAND_AUDIT_SOURCE)]
    print(f"cold frontend option parity: {len(actual)} parser options; consumers={selected}")


if __name__ == "__main__":
    main()
