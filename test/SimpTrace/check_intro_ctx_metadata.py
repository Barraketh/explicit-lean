"""Check T34 contextual-introduction metadata from a fresh focused capture."""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "out"


def intro_steps(value):
    if isinstance(value, dict):
        if value.get("kind") == "intro_ctx":
            yield value
        for child in value.values():
            yield from intro_steps(child)
    elif isinstance(value, list):
        for child in value:
            yield from intro_steps(child)


def main() -> None:
    paths = sorted(OUT.glob("t34_intro_ctx_final_*.json"))
    if not paths:
        raise SystemExit("no focused T34 traces; run IntroCtxStable.lean first")
    for path in paths:
        trace = json.loads(path.read_text(encoding="utf-8"))
        steps = list(intro_steps(trace))
        if not steps:
            raise SystemExit(f"{path.name}: no intro_ctx metadata")
        handles = [step["intro"]["handle"] for step in steps]
        if handles != list(range(len(handles))):
            raise SystemExit(f"{path.name}: handles are not stable: {handles}")
        for step in steps:
            if "name" in step or "name" in step.get("intro", {}):
                raise SystemExit(f"{path.name}: display-name metadata leaked")
            intro = step["intro"]
            if intro["operation"] != "simpArrowT.contextual":
                raise SystemExit(f"{path.name}: unexpected operation")
            if intro["scope"]["owner"] != intro["operation"]:
                raise SystemExit(f"{path.name}: scope owner mismatch")
            if not isinstance(intro["domain"]["dependencies"], list):
                raise SystemExit(f"{path.name}: malformed domain dependencies")
    print(f"OK: {len(paths)} focused intro_ctx traces have stable operational handles")


if __name__ == "__main__":
    main()
