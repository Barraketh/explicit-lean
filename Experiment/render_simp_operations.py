#!/usr/bin/env python3
"""Render a term-free simp operation trace as readable ``explicit_rw_v2`` source."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import simp_family_lint


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


def render_global_name(value: Any) -> str:
    """Render the recorder's exact root-qualified declaration identity."""
    parts = value["name"] if isinstance(value, dict) and "name" in value else value
    # Lean's environment identity for a source `private` declaration is
    # `_private.<module>.<nonce>.<user name>`. That internal name is neither
    # legal nor resolvable as source (`.0` is a numeric Name component). The
    # declaration is replayed in the same module after its original command,
    # where Lean resolves its exact user-facing private name back to that
    # environment declaration. Keep it unqualified by `_root_`: private-name
    # resolution is intentionally source-scope aware.
    if isinstance(parts, str):
        components = parts.split(".")
        if components and components[0] == "_private":
            nonce = next(
                (index for index, component in enumerate(components[1:], 1)
                 if component.isdecimal()),
                None,
            )
            if nonce is None or nonce + 1 >= len(components):
                raise UnsupportedOperation("malformed private declaration identity")
            return ".".join(components[nonce + 1:])
    elif isinstance(parts, list) and parts:
        first = parts[0]
        if first == ["str", "_private"] or first == ("str", "_private"):
            nonce = next(
                (index for index, component in enumerate(parts[1:], 1)
                 if component[0] == "num"),
                None,
            )
            if nonce is None or nonce + 1 >= len(parts):
                raise UnsupportedOperation("malformed private declaration identity")
            return render_name(parts[nonce + 1:])
    return "_root_." + render_name(value)


def render_position(position: Any) -> str:
    if position is None:
        raise UnsupportedOperation("operation has no exact raw child position")
    return "at [" + ", ".join(str(index) for index in position) + "]"


BoundNames = tuple[str | None, ...]


def render_rule_origin(origin: dict[str, Any], bound_names: BoundNames = ()) -> str:
    if "decl" in origin:
        return f"rule {render_global_name(origin['decl'])}"
    if "local" in origin:
        return f"local local_ref {origin['local']['contextIndex']}"
    if "bound" in origin:
        ordinal = origin["bound"]["ordinal"]
        if not isinstance(ordinal, int) or isinstance(ordinal, bool) or ordinal < 0:
            raise UnsupportedOperation("congruence-bound local has no ordinal")
        if bound_names:
            try:
                name = bound_names[ordinal]
            except IndexError:
                raise UnsupportedOperation(
                    f"congruence-bound local {ordinal} is outside {len(bound_names)} binders"
                ) from None
            if name is not None:
                return f"local {name}"
        return f"bound {ordinal}"
    if "equation" in origin:
        equation = origin["equation"]
        return (
            f"equation {render_global_name(equation['declaration'])} "
            f"index {equation['index']}"
        )
    if "syntax" in origin:
        syntax = origin["syntax"]
        if not isinstance(syntax, dict) or not isinstance(syntax.get("source"), str):
            raise UnsupportedOperation("source-syntax simp rule has no exact parser source")
        source = syntax["source"].strip()
        if not source:
            raise UnsupportedOperation("source-syntax simp rule has empty parser source")
        forbidden = simp_family_lint.findings(source)
        if forbidden:
            names = ", ".join(dict.fromkeys(item.token for item in forbidden))
            raise UnsupportedOperation(
                f"source-syntax simp rule contains forbidden simp-family tactic(s): {names}"
            )
        return f"source_rule lean_term({source})"
    if "other" in origin:
        raise UnsupportedOperation("opaque simp rule origin is not an operational operand")
    raise UnsupportedOperation(f"unknown rule origin {origin!r}")


def render_premise_terminal(
    premise: dict[str, Any], bound_names: BoundNames = ()
) -> str:
    terminal = premise["terminal"]
    if terminal == "dischargeRfl":
        return "rfl"
    if terminal == "isTrue":
        return "true_intro"
    if terminal == "equationHypothesis":
        return "equation_hypothesis"
    if isinstance(terminal, dict) and "localAssumption" in terminal:
        index = terminal["localAssumption"]["contextIndex"]
        return f"assumption local_ref {index}"
    if isinstance(terminal, dict) and "boundAssumption" in terminal:
        ordinal = terminal["boundAssumption"]["ordinal"]
        if not isinstance(ordinal, int) or isinstance(ordinal, bool) or ordinal < 0:
            raise UnsupportedOperation("congruence-bound assumption has no ordinal")
        if bound_names:
            try:
                name = bound_names[ordinal]
            except IndexError:
                raise UnsupportedOperation(
                    f"congruence-bound assumption {ordinal} is outside {len(bound_names)} binders"
                ) from None
            if name is not None:
                return f"assumption {name}"
        return f"assumption bound {ordinal}"
    if terminal == "failed":
        raise UnsupportedOperation("committed rewrite contains a failed premise")
    raise UnsupportedOperation(f"unknown premise terminal {terminal!r}")


def render_premise(premise: dict[str, Any], bound_names: BoundNames = ()) -> str:
    proof = render_premise_terminal(premise, bound_names)
    events = premise.get("events")
    if not isinstance(events, list):
        raise UnsupportedOperation("rewrite premise has no recursive operation stream")
    if not events:
        return proof
    return (
        f"explicit_rw_v2 [{', '.join(render_events(events, bound_names))}] then {proof}"
    )


def render_rewrite(
    payload: dict[str, Any], position: Any, bound_names: BoundNames = ()
) -> str:
    rule = payload["rule"]
    premises = ", ".join(
        render_premise(premise, bound_names) for premise in payload["premises"]
    )
    phase = rule["phase"]
    if phase not in ("pre", "post", "dpre", "dpost"):
        raise UnsupportedOperation(f"rewrite phase {phase!r} is not supported by the source DSL")
    direction = "rev" if rule["inverse"] else "fwd"
    return (
        f"{render_rule_origin(rule['origin'], bound_names)} variant {rule['variant']} "
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
    if payload == "foldRawNatLit":
        return f"fold_nat_lit {at}"
    if isinstance(payload, dict):
        if "zetaUsed" in payload:
            return f"zeta {at}"
        if "projection" in payload or "projectionFunction" in payload:
            return f"proj {at}"
        if "delta" in payload:
            return f"unfold {render_global_name(payload['delta']['name'])} {at}"
        if "localDef" in payload:
            local_def = payload["localDef"]
            index = local_def.get("contextIndex")
            reason = local_def.get("reason")
            if not isinstance(index, int) or isinstance(index, bool) or index < 0:
                raise UnsupportedOperation("local-definition reduction has no context index")
            if reason not in ("zetaDelta", "requested", "implementationDetail"):
                raise UnsupportedOperation(
                    f"local-definition reduction has unknown reason {reason!r}"
                )
            return f"zeta_local local_ref {index} {reason} {at}"
    raise UnsupportedOperation(f"reduction {payload!r} has no exact source operation yet")


def render_congruence(
    payload: dict[str, Any], position: Any, bound_names: BoundNames = ()
) -> str:
    entries: list[tuple[int, str]] = []
    for child in payload["children"]:
        argument = child["argumentIndex"]
        count = child["binderCount"]
        names = tuple(f"__explicit_rw_v2_bound_{i}" for i in range(count)) + bound_names
        events = child.get("events")
        if not isinstance(events, list):
            raise UnsupportedOperation("named congruence child has no operation stream")
        proof = "rfl"
        if events:
            proof = f"explicit_rw_v2 [{', '.join(render_events(events, names))}] then rfl"
        if count:
            proof = f"intro {count} ; {proof}"
        entries.append((argument, f"arg {argument} {proof}"))
    for indexed in payload["premises"]:
        argument = indexed["argumentIndex"]
        entries.append(
            (argument, f"arg {argument} {render_premise(indexed['premise'], bound_names)}")
        )
    entries.sort(key=lambda entry: entry[0])
    if len({argument for argument, _ in entries}) != len(entries):
        raise UnsupportedOperation("named congruence has duplicate theorem argument programs")
    return (
        f"congr_rule {render_global_name(payload['theoremName'])} "
        f"{render_position(position)} with [{', '.join(source for _, source in entries)}]"
    )


def render_auto_congruence(
    payload: dict[str, Any], position: Any, bound_names: BoundNames = ()
) -> str:
    entries: list[str] = []
    seen: set[int] = set()
    for child in payload["children"]:
        argument = child["argumentIndex"]
        if not isinstance(argument, int) or isinstance(argument, bool) or argument < 0:
            raise UnsupportedOperation("automatic congruence child has no argument index")
        if argument in seen:
            raise UnsupportedOperation(
                f"automatic congruence repeats argument {argument}"
            )
        seen.add(argument)
        events = child.get("events")
        if not isinstance(events, list):
            raise UnsupportedOperation(
                "automatic congruence child has no operation stream"
            )
        entries.append(
            f"arg {argument} [{', '.join(render_events(events, bound_names))}]"
        )
    return (
        f"auto_congr {render_position(position)} with "
        f"[{', '.join(entries)}]"
    )


def render_forall_congruence(
    payload: dict[str, Any], position: Any, bound_names: BoundNames = ()
) -> str:
    domain = payload.get("domain")
    body = payload.get("body")
    if not isinstance(domain, list) or not isinstance(body, list):
        raise UnsupportedOperation("forall congruence has no exact operation streams")
    return (
        f"forall_congr {render_position(position)} "
        f"domain [{', '.join(render_events(domain, bound_names))}] "
        f"body [{', '.join(render_events(body, (None,) + bound_names))}]"
    )


def render_events(
    events: list[dict[str, Any]], bound_names: BoundNames = ()
) -> list[str]:
    steps: list[str] = []
    for index, event in enumerate(events):
        action = event["action"]
        try:
            if "rewrite" in action:
                steps.append(
                    render_rewrite(action["rewrite"], event["position"], bound_names)
                )
            elif "reduce" in action:
                steps.append(render_reduction(action["reduce"]["reduction"], event["position"]))
            elif "simproc" in action:
                raise UnsupportedOperation("simproc operation is a known residual")
            elif "builtin" in action:
                raise UnsupportedOperation("builtin simp operation has no exact source operation yet")
            elif "cacheReuse" in action:
                cached = action["cacheReuse"].get("events")
                if not isinstance(cached, list) or not cached:
                    raise UnsupportedOperation("changed simp cache result has no source operations")
                steps.append(
                    "cached ["
                    + ", ".join(render_events(cached, bound_names))
                    + "] "
                    + render_position(event["position"])
                )
            elif "congruence" in action:
                steps.append(
                    render_congruence(action["congruence"], event["position"], bound_names)
                )
            elif "autoCongruence" in action:
                steps.append(
                    render_auto_congruence(
                        action["autoCongruence"], event["position"], bound_names
                    )
                )
            elif "forallCongruence" in action:
                steps.append(
                    render_forall_congruence(
                        action["forallCongruence"], event["position"], bound_names
                    )
                )
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


def render_repeated_goal_traces(observations: list[dict[str, Any]]) -> list[str]:
    """Render repeated executions of one source tactic in exact goal order."""
    programs: list[str] = []
    for index, observation in enumerate(observations):
        rendered = render_observation(observation)
        rendered = ["explicit_rw_v2 []" if item == "skip" else item
                    for item in rendered]
        if len(rendered) == 1 and isinstance(observation.get("events"), list):
            programs.append(rendered[0])
        else:
            programs.append(
                "explicit_rw_v2_sequence [" + ", ".join(rendered) + "]"
            )
    if not programs:
        raise UnsupportedOperation("repeated source tactic emitted no invocations")
    return ["explicit_rw_v2_goals [" + ", ".join(programs) + "]"]


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
        # `simp at *` reports every eligible hypothesis and the target, even
        # when a subject is unchanged.  Such a subject is not an operation to
        # replay.  In particular, rewriting an unchanged local declaration
        # would retire its fvar and perturb the identities of later subjects.
        if not trace["events"] and trace.get("terminal", "open") == "open":
            continue
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
    return rendered or ["skip"]


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
