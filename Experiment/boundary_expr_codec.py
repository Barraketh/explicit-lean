"""Structural validation of the closed boundary expression DAG wire format.

Lean reconstructs and type-checks the expression. This module checks only the
wire structure and literal terminal constants; it is not proof verification.
"""
from __future__ import annotations

import json
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
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not an expression DAG: {error}") from error
    if not (isinstance(value, list) and len(value) == 3
            and value[0] == EXPR_DAG_VERSION and isinstance(value[1], list)
            and _nat(value[2]) and value[2] < len(value[1])):
        raise RuntimeError(f"{label} has an invalid expression DAG header")
    nodes = value[1]
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
    return value


def expr_is_constant(source: str, name: str) -> bool:
    """Recognize the same literal constant shape as Lean Expr.isConstOf."""
    _, nodes, root = validate_expr_dag(source)
    return nodes[root] == ["c", [["s", name]], []]
