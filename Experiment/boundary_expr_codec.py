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


def _level(value: Any) -> bool:
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
        else:
            return False
    return True


def validate_expr_dag(source: object, label: str = "boundary expression") -> list[Any]:
    if not isinstance(source, str):
        raise RuntimeError(f"{label} must be a string")
    if len(source.encode("utf-8")) > 64 * 1024 * 1024:
        raise RuntimeError(f"{label} exceeds the expression source size limit")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not an expression DAG: {error}") from error
    if not (isinstance(value, list) and len(value) == 3
            and value[0] == EXPR_DAG_VERSION and isinstance(value[1], list)
            and _nat(value[2]) and value[2] < len(value[1])):
        raise RuntimeError(f"{label} has an invalid expression DAG header")
    nodes = value[1]
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
            valid = len(node) == 2 and _level(node[1])
        elif tag == "c":
            valid = (len(node) == 3 and _name(node[1]) and isinstance(node[2], list)
                     and all(_level(level) for level in node[2]))
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
