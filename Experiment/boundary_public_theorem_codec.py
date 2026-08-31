#!/usr/bin/env python3
"""Strict structural validator for the public-theorem boundary wire format.

This validates JSON shape and closed-expression DAG structure only.  It does not
authenticate capture, resolve names in an Environment, or replace Lean's
kernel/type/tag checks.
"""
from __future__ import annotations

import json
from typing import Any

from boundary_expr_codec import _name, validate_expr_dag, validate_theorem_payload


PUBLIC_THEOREM_VERSION = "boundary_public_theorem_v1"


def _nonanonymous_name(value: object, label: str) -> None:
    if not _name(value) or not value:
        raise RuntimeError(f"{label} must be a nonanonymous encoded Name")


def _unique_universe_names(value: object, label: str) -> None:
    if not isinstance(value, list):
        raise RuntimeError(f"{label} must be an array")
    seen: set[str] = set()
    for index, name in enumerate(value):
        _nonanonymous_name(name, f"{label}[{index}]")
        encoded = json.dumps(name, separators=(",", ":"), ensure_ascii=False)
        if encoded in seen:
            raise RuntimeError(f"{label} contains a duplicate universe name")
        seen.add(encoded)


def _validate_cache(cache: object, label: str) -> None:
    if cache is None:
        return
    if not isinstance(cache, list) or len(cache) != 4:
        raise RuntimeError(f"{label} must be null or an exact four-element array")
    if not isinstance(cache[0], str):
        raise RuntimeError(f"{label}.type must be an expression string")
    validate_expr_dag(cache[0], f"{label}.type")
    if type(cache[1]) is not bool or type(cache[2]) is not bool:
        raise RuntimeError(f"{label}.isPrivate and {label}.defeq must be booleans")
    previous = cache[3]
    if previous is None:
        return
    if not isinstance(previous, list) or len(previous) != 2:
        raise RuntimeError(f"{label}.previous must be null or an exact two-element array")
    _nonanonymous_name(previous[0], f"{label}.previous.name")
    _unique_universe_names(previous[1], f"{label}.previous.levels")


def validate_public_theorem_payload(
    source: object, expected_name: object, label: str = "boundary public theorem"
) -> list[Any]:
    """Validate a ``boundary_public_theorem_v1`` payload without Lean effects."""
    _nonanonymous_name(expected_name, f"{label}.expectedName")
    if not isinstance(source, str):
        raise RuntimeError(f"{label} must be a JSON string")
    try:
        payload = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not valid JSON: {error}") from error
    if not (isinstance(payload, list) and len(payload) == 5
            and payload[0] == PUBLIC_THEOREM_VERSION
            and isinstance(payload[1], str)
            and type(payload[2]) is bool and type(payload[3]) is bool):
        raise RuntimeError(f"{label} has an invalid exact five-element header")

    theorem = validate_theorem_payload(payload[1], expected_name, f"{label}.theorem")
    if theorem[2] != [expected_name]:
        raise RuntimeError(f"{label}.theorem declaration group must be exactly [expectedName]")
    _validate_cache(payload[4], f"{label}.cache")
    return payload
