#!/usr/bin/env python3
"""Render a term-free simp operation trace as readable ``explicit_rw_v2`` source."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


class UnsupportedOperation(ValueError):
    pass


def render_name(value: Any) -> str:
    parts = value["name"] if isinstance(value, dict) and "name" in value else value
    if isinstance(parts, str):
        if not parts:
            raise UnsupportedOperation("anonymous declaration name")
        return parts
    rendered: list[str] = []
    for kind, component in parts:
        if kind == "str":
            rendered.append(component)
        elif kind == "num":
            if not rendered:
                raise UnsupportedOperation("numeric name component has no parent")
            rendered[-1] += f".{component}"
        else:
            raise UnsupportedOperation(f"unknown name component {kind!r}")
    if not rendered:
        raise UnsupportedOperation("anonymous declaration name")
    return ".".join(rendered)


def render_position(position: Any) -> str:
    if position is None:
        raise UnsupportedOperation("operation has no exact raw child position")
    return "at [" + ", ".join(str(index) for index in position) + "]"


def render_rule_origin(origin: dict[str, Any]) -> str:
    if "decl" in origin:
        return f"rule {render_name(origin['decl'])}"
    if "local" in origin:
        return f"local local_ref {origin['local']['contextIndex']}"
    if "equation" in origin:
        equation = origin["equation"]
        return (
            f"equation {render_name(equation['declaration'])} "
            f"index {equation['index']}"
        )
    if "syntax" in origin:
        syntax = origin["syntax"]
        if not isinstance(syntax, dict) or not isinstance(syntax.get("source"), str):
            raise UnsupportedOperation("source-syntax simp rule has no exact parser source")
        source = syntax["source"].strip()
        if not source:
            raise UnsupportedOperation("source-syntax simp rule has empty parser source")
        return f"source_rule lean_term({source})"
    if "other" in origin:
        raise UnsupportedOperation("opaque simp rule origin is not an operational operand")
    raise UnsupportedOperation(f"unknown rule origin {origin!r}")


def render_premise_terminal(premise: dict[str, Any]) -> str:
    terminal = premise["terminal"]
    if terminal == "dischargeRfl":
        return "rfl"
    if terminal == "isTrue":
        return "true_intro"
    if isinstance(terminal, dict) and "localAssumption" in terminal:
        index = terminal["localAssumption"]["contextIndex"]
        return f"assumption local_ref {index}"
    if terminal == "equationHypothesis":
        raise UnsupportedOperation("equation-hypothesis premise terminal is not implemented")
    if terminal == "failed":
        raise UnsupportedOperation("committed rewrite contains a failed premise")
    raise UnsupportedOperation(f"unknown premise terminal {terminal!r}")


def render_premise(premise: dict[str, Any]) -> str:
    proof = render_premise_terminal(premise)
    events = premise.get("events")
    if not isinstance(events, list):
        raise UnsupportedOperation("rewrite premise has no recursive operation stream")
    if not events:
        return proof
    return f"explicit_rw_v2 [{', '.join(render_events(events))}] then {proof}"


def render_rewrite(payload: dict[str, Any], position: Any) -> str:
    rule = payload["rule"]
    premises = ", ".join(render_premise(premise) for premise in payload["premises"])
    phase = rule["phase"]
    if phase not in ("pre", "post", "dpre", "dpost"):
        raise UnsupportedOperation(f"rewrite phase {phase!r} is not supported by the source DSL")
    direction = "rev" if rule["inverse"] else "fwd"
    return (
        f"{render_rule_origin(rule['origin'])} variant {rule['variant']} "
        f"phase {phase} {direction} extra {rule['numExtraArgs']} "
        f"{render_position(position)} with [{premises}]"
    )


def render_reduction(payload: Any, position: Any) -> str:
    at = render_position(position)
    if payload == "instantiateMVars":
        return f"instantiate {at}"
    if payload == "beta":
        return f"beta {at}"
    if payload == "iota":
        return f"iota {at}"
    if payload in ("zetaUnused",):
        return f"zeta {at}"
    if isinstance(payload, dict):
        if "zetaUsed" in payload:
            return f"zeta {at}"
        if "projection" in payload or "projectionFunction" in payload:
            return f"proj {at}"
        if "delta" in payload:
            return f"unfold {render_name(payload['delta']['name'])} {at}"
    raise UnsupportedOperation(f"reduction {payload!r} has no exact source operation yet")


def render_events(events: list[dict[str, Any]]) -> list[str]:
    steps: list[str] = []
    for index, event in enumerate(events):
        action = event["action"]
        try:
            if "rewrite" in action:
                steps.append(render_rewrite(action["rewrite"], event["position"]))
            elif "reduce" in action:
                steps.append(render_reduction(action["reduce"]["reduction"], event["position"]))
            elif "simproc" in action:
                raise UnsupportedOperation("simproc operation is a known residual")
            elif "builtin" in action:
                raise UnsupportedOperation("builtin simp operation has no exact source operation yet")
            else:
                raise UnsupportedOperation(f"unknown operation {action!r}")
        except UnsupportedOperation as error:
            raise UnsupportedOperation(f"event {index}: {error}") from error
    return steps


def render_trace(trace: dict[str, Any], location: str | None = None) -> str:
    steps = render_events(trace["events"])
    source = "explicit_rw_v2 [" + ", ".join(steps) + "]"
    if location is not None:
        source += " " + location
    terminal = trace.get("terminal", "open")
    if terminal == "trueIntro":
        source += " then true_intro"
    elif terminal == "falseElim":
        if location is None:
            raise UnsupportedOperation("false-elimination terminal has no local subject")
        source += " then false_elim"
    elif terminal != "open":
        raise UnsupportedOperation(f"unknown terminal operation {terminal!r}")
    return source


def render_observation(observation: dict[str, Any]) -> list[str]:
    if isinstance(observation.get("events"), list):
        return [render_trace(observation)]
    subjects = observation.get("subjects")
    if not isinstance(subjects, list):
        raise UnsupportedOperation("operational observation has neither events nor subjects")
    if not subjects:
        raise UnsupportedOperation("located simp observation has no subjects")
    rendered: list[str] = []
    for subject in subjects:
        trace = subject.get("trace")
        if not isinstance(trace, dict) or not isinstance(trace.get("events"), list):
            raise UnsupportedOperation("located simp subject has no operational trace")
        identity = subject.get("subject")
        if identity == "target":
            location = None
        elif isinstance(identity, dict) and isinstance(identity.get("namedLocal"), dict):
            source = identity["namedLocal"].get("source")
            if not isinstance(source, str) or not source.strip():
                raise UnsupportedOperation("located simp local has no exact source identifier")
            location = f"at {source}"
        elif isinstance(identity, dict) and isinstance(identity.get("local"), dict):
            index = identity["local"].get("contextIndex")
            if not isinstance(index, int):
                raise UnsupportedOperation("located simp local has no exact context index")
            location = f"at local_ref {index}"
        else:
            raise UnsupportedOperation(f"unknown simp subject {identity!r}")
        rendered.append(render_trace(trace, location))
    return rendered


def load_trace(path: Path | None) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8") if path else sys.stdin.read()
    for line in text.splitlines():
        if "SIMP_OPERATIONS " in line:
            text = line.split("SIMP_OPERATIONS ", 1)[1]
            break
    value = json.loads(text)
    if not isinstance(value, dict) or not isinstance(value.get("events"), list):
        raise ValueError("expected an operational trace object with an events array")
    return value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("trace", nargs="?", type=Path)
    args = parser.parse_args()
    print(render_trace(load_trace(args.trace)))


if __name__ == "__main__":
    main()
