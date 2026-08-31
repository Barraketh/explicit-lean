"""Structural validation of the closed boundary expression DAG wire format.

Lean reconstructs and type-checks the expression. This module checks only the
wire structure and literal terminal constants; it is not proof verification.
"""
from __future__ import annotations

import json
import re
from typing import Any

EXPR_DAG_VERSION = "expr_dag_v1"


def _nat(value: Any) -> bool:
    return type(value) is int and value >= 0


def _name(value: Any) -> bool:
    return isinstance(value, list) and all(
        isinstance(part, list) and len(part) == 2
        and ((part[0] == "s" and isinstance(part[1], str))
             or (part[0] == "n" and _nat(part[1])))
        for part in value
    )


def _level(value: Any, reference_count: int | None = None) -> bool:
    pending = [value]
    while pending:
        node = pending.pop()
        if not isinstance(node, list) or not node:
            return False
        tag = node[0]
        if tag == "z" and len(node) == 1:
            continue
        if tag == "s" and len(node) == 2:
            pending.append(node[1])
        elif tag in ("max", "imax") and len(node) == 3:
            pending.extend(node[1:])
        elif tag == "p" and len(node) == 2 and _name(node[1]):
            continue
        elif (tag == "r" and len(node) == 2 and reference_count is not None
              and _nat(node[1]) and node[1] < reference_count):
            continue
        else:
            return False
    return True


def _validate_expr_dag(source: object, label: str, *, boundary_universes: bool) -> list[Any]:
    if not isinstance(source, str):
        raise RuntimeError(f"{label} must be a string")
    if len(source.encode("utf-8")) > 64 * 1024 * 1024:
        raise RuntimeError(f"{label} exceeds the expression source size limit")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not an expression DAG: {error}") from error
    reference_count = None
    if boundary_universes:
        if not (isinstance(value, list) and len(value) == 4
                and value[0] == "expr_dag_v2" and _nat(value[1])):
            raise RuntimeError(f"{label} has an invalid boundary expression DAG header")
        _, reference_count, nodes, root = value
    else:
        if not (isinstance(value, list) and len(value) == 3
                and value[0] == EXPR_DAG_VERSION):
            raise RuntimeError(f"{label} has an invalid expression DAG header")
        _, nodes, root = value
    if not isinstance(nodes, list) or not _nat(root) or root >= len(nodes):
        raise RuntimeError(f"{label} has an invalid expression DAG root")
    if len(nodes) > 2_000_000:
        raise RuntimeError(f"{label} exceeds the expression node count limit")
    for index, node in enumerate(nodes):
        if not isinstance(node, list) or not node or not isinstance(node[0], str):
            raise RuntimeError(f"{label} has an invalid node at {index}")
        tag = node[0]
        references = []
        valid = False
        if tag in ("b", "f", "n"):
            valid = len(node) == 2 and _nat(node[1])
        elif tag == "t":
            valid = len(node) == 2 and isinstance(node[1], str)
        elif tag == "s":
            valid = len(node) == 2 and _level(node[1], reference_count)
        elif tag == "c":
            valid = (len(node) == 3 and _name(node[1]) and isinstance(node[2], list)
                     and all(_level(level, reference_count) for level in node[2]))
        elif tag == "a":
            valid = len(node) == 3
            references = node[1:]
        elif tag in ("l", "q"):
            valid = len(node) == 5 and _name(node[1]) and _nat(node[2]) and node[2] < 4
            references = node[3:]
        elif tag == "e":
            valid = len(node) == 6 and _name(node[1]) and type(node[5]) is bool
            references = node[2:5]
        elif tag == "p":
            valid = len(node) == 4 and _name(node[1]) and _nat(node[2])
            references = node[3:]
        if not valid or any(not _nat(ref) or ref >= index for ref in references):
            raise RuntimeError(f"{label} has an invalid node or forward reference at {index}")
        if tag in ("c", "p") and node[1] == [["s", "sorryAx"]]:
            raise RuntimeError(f"{label} contains forbidden sorryAx")
    return value


def validate_expr_dag(source: object, label: str = "boundary expression") -> list[Any]:
    """Validate the closed v1 expression format; boundary references are forbidden."""
    return _validate_expr_dag(source, label, boundary_universes=False)


def validate_boundary_expr_dag(source: object, label: str = "boundary expression") -> list[Any]:
    """Validate v2 reference bounds; Lean authenticates the pre-boundary reference table."""
    return _validate_expr_dag(source, label, boundary_universes=True)


def validate_theorem_payload(source: object, expected_name: object,
                             label: str = "boundary theorem") -> list[Any]:
    if not _name(expected_name) or not expected_name:
        raise RuntimeError(f"{label} has an invalid expected theorem name")
    if not isinstance(source, str):
        raise RuntimeError(f"{label} must be a string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not a theorem payload: {error}") from error
    if not (isinstance(value, list) and len(value) == 6
            and value[0] == "boundary_theorem_dag_v1"
            and _name(value[1]) and value[1] and value[1] == expected_name):
        raise RuntimeError(f"{label} has an invalid theorem header or name")
    for names, field in ((value[2], "declaration group"), (value[3], "universes")):
        if not isinstance(names, list) or any(not _name(name) or not name for name in names):
            raise RuntimeError(f"{label} has invalid {field}")
        if field == "universes" and len({json.dumps(name) for name in names}) != len(names):
            raise RuntimeError(f"{label} has duplicate {field}")
    validate_expr_dag(value[4], f"{label} type")
    validate_expr_dag(value[5], f"{label} value")
    return value


def expr_is_constant(source: str, name: str) -> bool:
    """Recognize the same literal constant shape as Lean Expr.isConstOf."""
    _, nodes, root = validate_expr_dag(source)
    return nodes[root] == ["c", [["s", name]], []]


def boundary_expr_is_constant(source: str, name: str) -> bool:
    _, _, nodes, root = validate_boundary_expr_dag(source)
    return nodes[root] == ["c", [["s", name]], []]


def validate_congruence_payload(source: object, expected_name: object = None,
                                label: str = "boundary congruence") -> list[Any]:
    if not isinstance(source, str):
        raise RuntimeError(f"{label} must be a string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not a congruence payload: {error}") from error
    kinds = {"fixed", "fixedNoParam", "eq", "cast", "heq", "subsingletonInst"}
    if not (isinstance(value, list) and len(value) == 4
            and value[0] == "boundary_congruence_v1"
            and _name(value[1]) and value[1]
            and isinstance(value[2], str) and isinstance(value[3], list)
            and all(isinstance(kind, str) and kind in kinds for kind in value[3])):
        raise RuntimeError(f"{label} has an invalid congruence header or argument kinds")
    try:
        theorem = json.loads(value[2])
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} has invalid theorem data") from error
    if not isinstance(theorem, list) or len(theorem) != 6:
        raise RuntimeError(f"{label} has invalid theorem data")
    name = theorem[1] if expected_name is None else expected_name
    validate_theorem_payload(value[2], name, label)
    if name[:-1] != value[1] or name[-1][0] != "s":
        raise RuntimeError(f"{label} has a mismatched anchor")
    suffix = name[-1][1]
    if suffix != "congr_simp" and not re.fullmatch(r"hcongr_[0-9]+(?:_[0-9]+)*", suffix):
        raise RuntimeError(f"{label} has an unsupported congruence name")
    return value


def validate_equation_payload(source: object, expected_name: object = None,
                              label: str = "boundary equation") -> list[Any]:
    if not isinstance(source, str):
        raise RuntimeError(f"{label} must be a string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not an equation payload: {error}") from error
    if not (isinstance(value, list) and len(value) == 6
            and value[0] == "boundary_equation_v1"
            and _name(value[1]) and value[1] and isinstance(value[2], str)
            and all(type(flag) is bool for flag in value[3:])):
        raise RuntimeError(f"{label} has an invalid equation header or metadata")
    try:
        theorem = json.loads(value[2])
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} has invalid theorem data") from error
    if not isinstance(theorem, list) or len(theorem) != 6:
        raise RuntimeError(f"{label} has invalid theorem data")
    name = theorem[1] if expected_name is None else expected_name
    validate_theorem_payload(value[2], name, label)
    if name[:-1] != value[1] or name[-1][0] != "s":
        raise RuntimeError(f"{label} has a mismatched anchor")
    suffix = name[-1][1]
    if suffix not in {"eq_def", "eq_unfold"} and not re.fullmatch(r"eq_[0-9]+(?:_[0-9]+)*", suffix):
        raise RuntimeError(f"{label} has an unsupported equation name")
    return value


def validate_definition_payload(source: object, expected_name: object,
                                label: str = "boundary definition") -> list[Any]:
    if not isinstance(source, str):
        raise RuntimeError(f"{label} must be a string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not a definition payload") from error
    if not (isinstance(value, list) and len(value) == 8
            and value[0] == "boundary_definition_dag_v1"
            and _name(expected_name) and expected_name and value[1] == expected_name
            and value[2] == [expected_name] and value[5] == "safe"):
        raise RuntimeError(f"{label} has an invalid safe singleton definition header")
    levels, hints = value[3:5]
    if (not isinstance(levels, list) or any(not _name(n) or not n for n in levels)
            or len({json.dumps(n) for n in levels}) != len(levels)):
        raise RuntimeError(f"{label} has invalid universes")
    if not (hints in (["opaque"], ["abbrev"]) or
            (isinstance(hints, list) and len(hints) == 2 and hints[0] == "regular"
             and _nat(hints[1]) and hints[1] <= 4294967295)):
        raise RuntimeError(f"{label} has invalid reducibility hints")
    validate_expr_dag(value[6], f"{label} type")
    validate_expr_dag(value[7], f"{label} value")
    return value


def validate_matcher_payload(source: object, expected_anchor: object,
                             label: str = "boundary matcher") -> list[Any]:
    """Validate the closed bundle format; Lean checks declarations/provenance.

    An anchor already exists. Its private equation/splitter declarations form
    the action's added names; the anchor is never a declared member.
    """
    def reject(detail: str) -> None:
        raise RuntimeError(f"{label}: {detail}")

    def key(name: object) -> str:
        if not _name(name) or not name:
            reject("invalid name")
        return json.dumps(name, separators=(",", ":"))

    def names(value: object) -> list:
        if not isinstance(value, list) or len({key(n) for n in value}) != len(value):
            reject("invalid or duplicate names")
        return value

    def info(value: object) -> None:
        if not (isinstance(value, list) and len(value) == 6 and
                _nat(value[0]) and _nat(value[1]) and isinstance(value[2], list) and
                (value[3] is None or _nat(value[3])) and isinstance(value[4], list)
                and len(value[4]) == value[1] and isinstance(value[5], list)):
            reject("invalid MatcherInfo")
        for alt in value[2]:
            if not (isinstance(alt, list) and len(alt) == 3 and _nat(alt[0])
                    and _nat(alt[1]) and type(alt[2]) is bool):
                reject("invalid alternative info")
        for name in value[4]:
            if name is not None:
                key(name)
        seen = set()
        for entry in value[5]:
            if not (isinstance(entry, list) and len(entry) == 2 and _nat(entry[0])
                    and entry[0] < len(value[2]) and entry[0] not in seen
                    and isinstance(entry[1], list) and all(_nat(n) and n < len(value[2]) for n in entry[1])
                    and len(set(entry[1])) == len(entry[1])):
                reject("invalid overlap map")
            seen.add(entry[0])

    def eqns(value: object) -> None:
        if not isinstance(value, list) or len(value) != 3:
            reject("invalid MatchEqns")
        names(value[0]); key(value[1]); info(value[2])
        if value[1] in value[0] or len(value[0]) != len(value[2][2]):
            reject("invalid equation count or splitter name")

    def match_state(value: object) -> tuple[dict, set]:
        if not (isinstance(value, list) and len(value) == 2 and isinstance(value[0], list)):
            reject("invalid matcher state")
        mapping = {}
        for entry in value[0]:
            if not isinstance(entry, list) or len(entry) != 2:
                reject("invalid matcher state entry")
            name = key(entry[0]); eqns(entry[1])
            if name in mapping:
                reject("duplicate matcher state key")
            mapping[name] = entry[1]
        return mapping, {key(n) for n in names(value[1])}

    def equation_state(value: object) -> None:
        if not isinstance(value, list):
            reject("invalid equation registration map")
        seen = set()
        for entry in value:
            if not isinstance(entry, list) or len(entry) != 2:
                reject("invalid equation registration entry")
            name = key(entry[0]); key(entry[1])
            if name in seen:
                reject("duplicate equation registration")
            seen.add(name)

    if not isinstance(source, str):
        reject("payload must be a string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label}: invalid JSON") from error
    if not (isinstance(value, list) and len(value) == 15
            and value[0] == "boundary_matcher_bundle_v1" and value[1] == expected_anchor):
        reject("invalid matcher bundle header or anchor")
    anchor_key = key(expected_anchor)
    info(value[2]); eqns(value[3])
    eqn_names, splitter, _ = value[3]
    if not eqn_names or len(eqn_names) != len(value[2][2]) or value[5] != "inline" or value[6] is not None:
        reject("unsupported matcher bundle metadata")
    if expected_anchor in eqn_names or expected_anchor == splitter:
        reject("anchor is not a new declaration")
    validate_definition_payload(value[4], splitter, label)
    if not isinstance(value[7], list) or len(value[7]) != len(eqn_names):
        reject("invalid captured equation list")
    for expected, equation in zip(eqn_names, value[7]):
        if not (isinstance(equation, list) and len(equation) == 6 and equation[0] == expected
                and type(equation[2]) is bool and type(equation[3]) is bool
                and all(n is None or n == expected_anchor for n in equation[4:])):
            reject("invalid captured equation metadata")
        theorem = validate_theorem_payload(equation[1], expected, label)
        if theorem[2] != [expected]:
            reject("matcher theorem declaration group must be singleton")
    before, before_eqns = match_state(value[8])
    after, after_eqns = match_state(value[9])
    match_state(value[10])
    member_keys = {key(n) for n in eqn_names}
    if anchor_key in before or before_eqns & member_keys:
        reject("nonfresh matcher snapshot")
    if after != {**before, anchor_key: value[3]} or after_eqns != before_eqns | member_keys:
        reject("invalid matcher snapshot transition")
    for state in value[11:15]:
        equation_state(state)
    return value


def validate_local_theorems_payload(source: object, expected_anchor: object,
                                    label: str = "boundary local theorems") -> list[Any]:
    if not isinstance(source, str):
        raise RuntimeError(f"{label} must be a string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not a local theorem bundle") from error
    def reject(message: str) -> None:
        raise RuntimeError(f"{label}: {message}")
    if not (isinstance(value, list) and len(value) == 3
            and value[0] == "boundary_local_theorems_bundle_v1"
            and _name(expected_anchor) and expected_anchor and value[1] == expected_anchor
            and isinstance(value[2], list) and value[2]):
        reject("invalid bundle header")
    names = []
    for entry in value[2]:
        if not (isinstance(entry, list) and len(entry) == 2 and _name(entry[0]) and entry[0]
                and isinstance(entry[1], str)):
            reject("invalid member")
        name, payload = entry
        if name in names:
            reject("duplicate member")
        names.append(name)
        try:
            thm = json.loads(payload)
        except (ValueError, RecursionError):
            reject("invalid member payload")
        if not (isinstance(thm, list) and len(thm) == 7
                and thm[0] == "boundary_local_theorem_v1"
                and type(thm[1]) is bool and thm[1] == (name[0] == ["s", "_private"])
                and isinstance(thm[2], str) and thm[2] in {"private", "axiom", "theorem"}
                and type(thm[4]) is bool and type(thm[5]) is bool):
            reject("invalid theorem metadata")
        body = validate_theorem_payload(thm[3], name, label)
        if body[2] != [name]:
            reject("nonsingleton theorem group")
        cache = thm[6]
        if cache is not None:
            if not (isinstance(cache, list) and len(cache) == 4 and isinstance(cache[0], str)
                    and type(cache[1]) is bool and type(cache[2]) is bool):
                reject("invalid cache entry")
            validate_expr_dag(cache[0], f"{label} cache type")
            if thm[1] and not cache[1]:
                reject("public cache key for private name")
            old = cache[3]
            if old is not None and not (isinstance(old, list) and len(old) == 2
                    and _name(old[0]) and old[0] and isinstance(old[1], list)
                    and all(_name(level) and level for level in old[1])):
                reject("invalid previous cache value")
    # Lean validates canonical anchor order using Name.toString; here require
    # exact membership without approximating Lean's escaped name rendering.
    if expected_anchor not in names:
        reject("anchor is not a member")
    return value
