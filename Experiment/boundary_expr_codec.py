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


def _validate_expr_dag(source: object, label: str, *, boundary_universes: bool,
                       structural: bool = False) -> list[Any]:
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
                and value[0] == ("expr_struct_dag_v1" if structural else EXPR_DAG_VERSION)):
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
            if structural and tag == "f":
                valid = False
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
        elif tag == "m" and structural:
            valid = len(node) == 3 and isinstance(node[1], list)
            references = node[2:]
            if valid:
                for entry in node[1]:
                    if not (isinstance(entry, list) and len(entry) == 2 and _name(entry[0])
                            and isinstance(entry[1], list) and len(entry[1]) == 2):
                        valid = False
                        break
                    kind, data = entry[1]
                    if not ((kind == "string" and isinstance(data, str))
                            or (kind == "bool" and type(data) is bool)
                            or (kind == "name" and _name(data))
                            or (kind == "nat" and _nat(data))
                            or (kind == "int" and type(data) is int)):
                        valid = False
                        break
        if not valid or any(not _nat(ref) or ref >= index for ref in references):
            raise RuntimeError(f"{label} has an invalid node or forward reference at {index}")
        if tag in ("c", "p") and node[1] == [["s", "sorryAx"]]:
            raise RuntimeError(f"{label} contains forbidden sorryAx")
    return value


def validate_expr_dag(source: object, label: str = "boundary expression") -> list[Any]:
    """Validate the closed v1 expression format; boundary references are forbidden."""
    return _validate_expr_dag(source, label, boundary_universes=False)


def validate_struct_expr_dag(source: object, label: str = "structural expression") -> list[Any]:
    return _validate_expr_dag(source, label, boundary_universes=False, structural=True)


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
            and isinstance(value[0], str) and value[0] in {"boundary_definition_dag_v1", "boundary_definition_dag_v2"}
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
    validator = validate_struct_expr_dag if value[0] == "boundary_definition_dag_v2" else validate_expr_dag
    validator(value[6], f"{label} type")
    validator(value[7], f"{label} value")
    return value


def _validate_matcher_payload_v1(source: object, expected_anchor: object,
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


def _private_name(value: object) -> bool:
    return _name(value) and bool(value) and value[0] == ["s", "_private"]


def _validate_sparse_key(value: object, label: str) -> None:
    if (not isinstance(value, list) or len(value) != 3 or not _name(value[0])
            or not value[0] or not isinstance(value[1], list)
            or type(value[2]) is not bool or any(not _name(n) or not n for n in value[1])):
        raise RuntimeError(f"{label} has an invalid sparse cache key")
    if len({json.dumps(n, separators=(",", ":")) for n in value[1]}) != len(value[1]):
        raise RuntimeError(f"{label} has duplicate sparse constructors")


def _validate_sparse_cache(value: object, label: str) -> dict[str, tuple[object, object]]:
    if not isinstance(value, list):
        raise RuntimeError(f"{label} must be an array")
    result: dict[str, tuple[object, object]] = {}
    previous = ""
    for entry in value:
        if not isinstance(entry, list) or len(entry) != 2:
            raise RuntimeError(f"{label} has an invalid cache entry")
        _validate_sparse_key(entry[0], label)
        if not _name(entry[1]) or not entry[1]:
            raise RuntimeError(f"{label} has an invalid cache value")
        cache_key = json.dumps(entry[0], separators=(",", ":"))
        if cache_key in result:
            raise RuntimeError(f"{label} has duplicate cache keys")
        encoded = json.dumps(entry, separators=(",", ":"), ensure_ascii=False)
        if encoded <= previous:
            raise RuntimeError(f"{label} must be sorted and unique")
        previous = encoded
        result[cache_key] = (entry[0], entry[1])
    return result


def validate_sparse_payload(source: object, expected_name: object = None,
                            label: str = "boundary sparse cases") -> list[Any]:
    """Validate the structural v1 sparse-helper payload nested in matcher v2."""
    if not isinstance(source, str):
        raise RuntimeError(f"{label} must be a string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label} is not sparse cases JSON") from error
    if not (isinstance(value, list) and len(value) == 5
            and value[0] == "boundary_sparse_cases_v1" and _name(value[1]) and value[1]):
        raise RuntimeError(f"{label} has an invalid sparse cases header")
    if expected_name is not None and value[1] != expected_name:
        raise RuntimeError(f"{label} has a mismatched helper name")
    if not _private_name(value[1]):
        raise RuntimeError(f"{label} helper is not private")
    if not isinstance(value[2], str):
        raise RuntimeError(f"{label} definition is not a string")
    definition = validate_definition_payload(value[2], value[1], label)
    if definition[4] != ["abbrev"] or definition[5] != "safe":
        raise RuntimeError(f"{label} definition is not a safe abbreviation")
    key = value[3]
    _validate_sparse_key(key, label)
    if key[2] is not True:
        raise RuntimeError(f"{label} cache key is not private")
    info = value[4]
    if (not isinstance(info, list) or len(info) != 4 or not _name(info[0]) or not info[0]
            or not _nat(info[1]) or not _nat(info[2]) or not isinstance(info[3], list)
            or any(not _name(n) or not n for n in info[3])):
        raise RuntimeError(f"{label} has invalid sparse metadata")
    if info[0] != key[0] or info[3] != key[1]:
        raise RuntimeError(f"{label} metadata does not match its cache key")
    if info[2] != info[1] + len(info[3]) + 2:
        raise RuntimeError(f"{label} metadata arity is inconsistent")
    if definition[1] != value[1] or definition[2] != [value[1]]:
        raise RuntimeError(f"{label} definition identity mismatch")
    return value


def validate_matcher_payload_v2(source: object, expected_anchor: object,
                                 label: str = "boundary matcher") -> list[Any]:
    """Reuse the common bundle checks, then validate the sparse cache transition."""
    def reject(detail: str) -> None:
        raise RuntimeError(f"{label}: {detail}")

    def key(name: object) -> str:
        if not _name(name) or not name:
            reject("invalid name")
        return json.dumps(name, separators=(",", ":"))

    if not isinstance(source, str):
        reject("payload must be a string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label}: invalid JSON") from error
    if not (isinstance(value, list) and len(value) == 19
            and value[0] == "boundary_matcher_bundle_v2" and value[1] == expected_anchor):
        reject("invalid matcher bundle v2 header or anchor")
    common = ["boundary_matcher_bundle_v1", *value[1:15]]
    _validate_matcher_payload_v1(json.dumps(common, separators=(",", ":")), expected_anchor, label)
    eqn_names, splitter, _ = value[3]
    if value[3][2][0:2] != value[2][0:2] or value[3][2][3:] != value[2][3:]:
        reject("unrelated splitter metadata")
    if not _private_name(splitter) or any(not _private_name(n) for n in eqn_names):
        reject("matcher members must be private")
    member_keys = {key(n) for n in eqn_names}
    if not isinstance(value[15], list):
        reject("invalid sparse helper list")
    sparse_names = set()
    helper_keys: dict[str, tuple[object, object]] = {}
    for helper in value[15]:
        if not isinstance(helper, list) or len(helper) != 2:
            reject("invalid sparse helper entry")
        helper_key = key(helper[0])
        if helper[0][:len(splitter)] != splitter:
            reject("sparse helper is outside splitter namespace")
        if helper_key in sparse_names or helper_key in member_keys or helper_key == key(splitter):
            reject("duplicate sparse helper name")
        sparse_names.add(helper_key)
        sparse = validate_sparse_payload(helper[1], helper[0], label)
        sparse_key = json.dumps(sparse[3], separators=(",", ":"))
        if sparse_key in helper_keys:
            reject("duplicate sparse helper cache key")
        helper_keys[sparse_key] = (sparse[3], helper[0])
    sparse_before = _validate_sparse_cache(value[16], label + " asyncSparseBefore")
    sparse_after = _validate_sparse_cache(value[17], label + " asyncSparseAfter")
    _validate_sparse_cache(value[18], label + " localSparseState")
    if any(cache_key not in sparse_after or sparse_after[cache_key][1] != helper[1]
           for cache_key, helper in helper_keys.items()):
        reject("async sparse cache lacks a captured helper")
    expected_before = {cache_key: entry for cache_key, entry in sparse_after.items()
                       if cache_key not in helper_keys}
    if sparse_before != expected_before:
        reject("invalid async sparse cache transition")
    return value


def validate_matcher_payload_v3(source: object, expected_anchor: object,
                              label: str = "boundary matcher") -> list[Any]:
    if not isinstance(source, str):
        raise RuntimeError(f"{label}: payload must be a string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label}: invalid JSON") from error
    if not (isinstance(value, list) and len(value) == 20
            and value[0] == "boundary_matcher_bundle_v3"):
        raise RuntimeError(f"{label}: invalid matcher bundle v3 header")
    validate_matcher_payload_v2(json.dumps(["boundary_matcher_bundle_v2", *value[1:19]],
                                         separators=(",", ":")), expected_anchor, label)
    members = [entry[0] for entry in value[15]] + value[3][0] + [value[3][1]]
    order = value[19]
    key = lambda name: json.dumps(name, separators=(",", ":"))
    if (not isinstance(order, list) or any(not _name(n) or not n for n in order)
            or sorted(map(key, order)) != sorted(map(key, members))
            or [n for n in order if n in value[3][0]] != value[3][0]
            or order[-1:] != [value[3][1]]):
        raise RuntimeError(f"{label}: invalid matcher declaration order")
    return value


def validate_matcher_payload(source: object, expected_anchor: object,
                             label: str = "boundary matcher") -> list[Any]:
    """Dispatch strict validation for legacy v1 and sparse-aware v2 bundles."""
    if isinstance(source, str):
        try:
            header = json.loads(source)
        except (ValueError, RecursionError):
            header = None
        if isinstance(header, list) and header and header[0] == "boundary_matcher_bundle_v2":
            return validate_matcher_payload_v2(source, expected_anchor, label)
        if isinstance(header, list) and header and header[0] == "boundary_matcher_bundle_v3":
            return validate_matcher_payload_v3(source, expected_anchor, label)
    return _validate_matcher_payload_v1(source, expected_anchor, label)


def validate_realization_payload(source: object, expected_anchor: object,
                                 label: str = "boundary realizations") -> list[Any]:
    """Validate fixed captured groups, never infer a runtime group or declaration."""
    def reject(message: str) -> None:
        raise RuntimeError(f"{label}: {message}")

    def key(value: object) -> str:
        if not _name(value) or not value:
            reject("invalid name")
        return json.dumps(value, separators=(",", ":"))

    def names(value: object) -> list:
        if not isinstance(value, list) or len({key(n) for n in value}) != len(value):
            reject("invalid or duplicate names")
        return value

    def equation_state(value: object) -> None:
        if not isinstance(value, list):
            reject("invalid equation map")
        seen = set()
        for entry in value:
            if not isinstance(entry, list) or len(entry) != 2:
                reject("invalid equation map entry")
            k = key(entry[0]); key(entry[1])
            if k in seen:
                reject("duplicate equation map key")
            seen.add(k)

    def match_state(value: object) -> None:
        if not (isinstance(value, list) and len(value) == 2 and isinstance(value[0], list)):
            reject("invalid matcher state")
        names(value[1]); seen = set()
        for entry in value[0]:
            if not isinstance(entry, list) or len(entry) != 2:
                reject("invalid matcher map entry")
            k = key(entry[0])
            if k in seen:
                reject("duplicate matcher map key")
            seen.add(k)
            eqns = entry[1]
            if not isinstance(eqns, list) or len(eqns) != 3:
                reject("invalid match equations")
            names(eqns[0]); key(eqns[1]); info = eqns[2]
            if not (isinstance(info, list) and len(info) == 6 and _nat(info[0]) and _nat(info[1])
                    and isinstance(info[2], list) and (info[3] is None or _nat(info[3]))
                    and isinstance(info[4], list) and len(info[4]) == info[1]
                    and isinstance(info[5], list) and len(info[2]) == len(eqns[0])
                    and eqns[1] not in eqns[0]):
                reject("invalid matcher info")
            for alt in info[2]:
                if not (isinstance(alt, list) and len(alt) == 3 and _nat(alt[0]) and _nat(alt[1])
                        and type(alt[2]) is bool):
                    reject("invalid alternative")
            for n in info[4]:
                if n is not None:
                    key(n)
            overlap_keys = set()
            for overlap in info[5]:
                if not (isinstance(overlap, list) and len(overlap) == 2 and _nat(overlap[0])
                        and overlap[0] < len(info[2]) and overlap[0] not in overlap_keys
                        and isinstance(overlap[1], list)
                        and all(_nat(n) and n < len(info[2]) for n in overlap[1])
                        and len(set(overlap[1])) == len(overlap[1])):
                    reject("invalid overlap")
                overlap_keys.add(overlap[0])

    def sparse_state(value: object) -> None:
        if not isinstance(value, list):
            reject("invalid sparse cache")
        seen = set()
        for entry in value:
            if not (isinstance(entry, list) and len(entry) == 2
                    and isinstance(entry[0], list) and len(entry[0]) == 3
                    and type(entry[0][2]) is bool):
                reject("invalid sparse entry")
            key(entry[0][0]); names(entry[0][1]); key(entry[1])
            encoded = json.dumps(entry[0], separators=(",", ":"))
            if encoded in seen:
                reject("duplicate sparse key")
            seen.add(encoded)

    def descriptor(value: object, owner: object, root: object) -> tuple[list, list]:
        if not (isinstance(value, list) and len(value) == 6 and isinstance(value[0], str)
                and value[0] in {"completed_realization_v1", "completed_realization_v2"}
                and value[1] is True and value[2] == owner and value[3] == root
                and isinstance(value[4], list) and value[4] and isinstance(value[5], list)):
            reject("invalid completed group descriptor")
        key(owner); key(root)
        expression_validator = validate_struct_expr_dag if value[0] == "completed_realization_v2" else validate_expr_dag
        def members(entries: list, public: bool) -> list:
            result = []
            signatures = {}
            def tree_check(tree: object, allowed: list, depth: int = 0) -> None:
                if not (isinstance(tree, list) and len(tree) == 4 and type(tree[1]) is bool
                        and isinstance(tree[3], list) and depth <= len(entries) + 1
                        and isinstance(tree[0], list) and len(tree[0]) >= 2):
                    reject("invalid nested branch tree")
                name = tree[0][1]
                if key(name) not in signatures or tree[0] != signatures[key(name)]:
                    reject("nested branch signature mismatch")
                if tree[2] is not None:
                    meta = tree[2]
                    if not (isinstance(meta, list) and len(meta) == 4 and isinstance(meta[3], list)):
                        reject("invalid nested metadata")
                    match_state(meta[0]); equation_state(meta[1]); sparse_state(meta[2]); seen_exts = set()
                    for ext in meta[3]:
                        if not (isinstance(ext, list) and len(ext) == 2 and isinstance(ext[1], str)
                                and len(ext[1]) % 2 == 0 and re.fullmatch(r"[0-9a-f]+", ext[1])):
                            reject("invalid nested persistent bytes")
                        k = key(ext[0])
                        if k in seen_exts:
                            reject("duplicate nested extension")
                        seen_exts.add(k)
                child_names = []
                for child in tree[3]:
                    if not (isinstance(child, list) and child and isinstance(child[0], list)
                            and len(child[0]) >= 2 and child[0][1] in allowed):
                        reject("nested branch not a prior member")
                    n = child[0][1]
                    child_names.append(n)
                    tree_check(child, allowed[:allowed.index(n)], depth + 1)
                names(child_names)
            for entry in entries:
                if not (isinstance(entry, list) and len(entry) == 3 and isinstance(entry[0], list)):
                    reject("invalid group member")
                sig, meta, tree = entry
                if not sig or sig[0] not in {"theorem", "definition", "public-proof-interface"}:
                    reject("unsupported declaration signature")
                expected_size = {"theorem": 5, "definition": 7, "public-proof-interface": 4}[sig[0]]
                if len(sig) != expected_size or (public != (sig[0] == "public-proof-interface")):
                    reject("invalid declaration signature shape")
                key(sig[1]); names(sig[2]); expression_validator(sig[3], label)
                if not public:
                    names(sig[4])
                if sig[0] == "definition":
                    hints = sig[5]
                    if not (hints in (["opaque"], ["abbrev"]) or
                            isinstance(hints, list) and len(hints) == 2 and hints[0] == "regular"
                            and _nat(hints[1]) and hints[1] <= 4294967295):
                        reject("invalid definition hints")
                    expression_validator(sig[6], label)
                if not (isinstance(meta, list) and len(meta) == 4 and isinstance(meta[3], list)):
                    reject("invalid member metadata")
                match_state(meta[0]); equation_state(meta[1]); sparse_state(meta[2]); seen_exts = set()
                for ext in meta[3]:
                    if not (isinstance(ext, list) and len(ext) == 2 and isinstance(ext[1], str)
                            and len(ext[1]) % 2 == 0 and re.fullmatch(r"[0-9a-f]+", ext[1])):
                        reject("invalid persistent metadata bytes")
                    k = key(ext[0])
                    if k in seen_exts:
                        reject("duplicate persistent metadata")
                    seen_exts.add(k)
                signatures[key(sig[1])] = sig
                if not (isinstance(tree, list) and len(tree) == 4 and tree[0] == sig
                        and tree[1] is True and tree[2] == meta):
                    reject("root async member mismatch")
                tree_check(tree, result)
                result.append(sig[1])
            return names(result)
        private = members(value[4], False); public = members(value[5], True)
        if private[-1] != root or any(n not in private for n in public):
            reject("invalid group root or public members")
        return private, public

    if not isinstance(source, str) or len(source.encode()) > 128 * 1024 * 1024:
        reject("invalid payload string")
    try:
        value = json.loads(source)
    except (ValueError, RecursionError) as error:
        raise RuntimeError(f"{label}: invalid JSON") from error
    if isinstance(value, list) and value and value[0] == "boundary_realization_batch_v2":
        if not (len(value) == 12 and type(value[1]) is bool
                and isinstance(value[10], list) and value[10]
                and isinstance(value[11], list) and value[11]):
            reject("invalid recursive batch header")
        key(expected_anchor); names(value[2]); names(value[3])
        match_state(value[4]); match_state(value[5]); equation_state(value[6]); equation_state(value[7])
        sparse_state(value[8]); sparse_state(value[9])
        node_members, node_public, depths, identities = [], [], [], set()
        nodes, roots = value[10:12]
        for index, node in enumerate(nodes):
            if not (isinstance(node, list) and len(node) == 6
                    and isinstance(node[0], str) and node[0] in {"matcher", "equation"}
                    and isinstance(node[4], list)):
                reject("invalid recursive node")
            kind, owner, root_name, payload, children, captured = node
            identity = (key(owner), key(root_name))
            if identity in identities:
                reject("duplicate recursive node")
            identities.add(identity)
            if (any(not _nat(i) or i >= index for i in children)
                    or len(set(children)) != len(children)):
                reject("non-topological recursive children")
            depth = max((depths[i] + 1 for i in children), default=0)
            if depth > 2:
                reject("recursive producer depth unsupported")
            depths.append(depth)
            if not (isinstance(captured, list) and captured and captured[0] == "completed_realization_v2"):
                reject("recursive nodes require structural descriptors")
            private, public = descriptor(captured, owner, root_name)
            if kind == "matcher":
                if children or public or not _private_name(root_name):
                    reject("invalid recursive matcher")
                if value[1]:
                    if payload is not None:
                        reject("cached recursive matcher has producer")
                else:
                    matcher = validate_matcher_payload(payload, owner, label)
                    if matcher[0] != "boundary_matcher_bundle_v3" or matcher[19] != private:
                        reject("recursive matcher member mismatch")
            else:
                if _private_name(root_name) or root_name[:-1] != owner:
                    reject("foreign recursive equation owner")
                equation = validate_equation_payload(payload, root_name, label)
                if equation[1] != owner:
                    reject("recursive equation anchor mismatch")
                child_private = [n for i in children for n in node_members[i]]
                child_public = [n for i in children for n in node_public[i]]
                if child_private + [root_name] != private or child_public + [root_name] != public:
                    reject("recursive child closure mismatch")
                for i in children:
                    if nodes[i][0] == "equation" and json.loads(nodes[i][3])[5]:
                        reject("nested equation registration unsupported")
            node_members.append(private); node_public.append(public)
        if (any(not _nat(i) or i >= len(nodes) for i in roots)
                or len(set(roots)) != len(roots)
                or any(nodes[i][0] != "equation" for i in roots)):
            reject("invalid recursive roots")
        reachable = set(roots)
        for index in range(len(nodes) - 1, -1, -1):
            if index in reachable:
                reachable.update(nodes[index][4])
        if len(reachable) != len(nodes):
            reject("unused recursive node")
        private, public = [], []
        for i in roots:
            if nodes[i][2] in private:
                reject("recursive root already active")
            private.extend(n for n in node_members[i] if n not in private)
            public.extend(n for n in node_public[i] if n not in public)
        if private != value[2] or public != value[3] or nodes[roots[0]][2] != expected_anchor:
            reject("recursive projected order or anchor mismatch")
        return value
    if not (isinstance(value, list) and len(value) == 11 and value[0] == "boundary_realization_batch_v1"
            and type(value[1]) is bool and isinstance(value[10], list) and value[10]):
        reject("invalid batch header")
    key(expected_anchor); names(value[2]); names(value[3])
    match_state(value[4]); match_state(value[5]); equation_state(value[6]); equation_state(value[7])
    sparse_state(value[8]); sparse_state(value[9])
    all_private, all_public = [], []
    for root in value[10]:
        if not (isinstance(root, list) and len(root) == 5 and isinstance(root[3], list)):
            reject("invalid root")
        owner, root_name, equation, children, captured = root
        key(owner); key(root_name)
        if root_name[:-1] != owner:
            reject("foreign root owner")
        validate_equation_payload(equation, root_name, label)
        private, public = descriptor(captured, owner, root_name)
        child_names = []
        for child in children:
            if not isinstance(child, list) or len(child) != 4:
                reject("invalid child")
            anchor, child_root, payload, child_capture = child
            child_private, child_public = descriptor(child_capture, anchor, child_root)
            if child_public:
                reject("unsupported public child")
            if value[1]:
                if payload is not None:
                    reject("cached activation carries producer")
            else:
                matcher = validate_matcher_payload(payload, anchor, label)
                sparse_names = ([entry[0] for entry in matcher[15]]
                                if matcher[0] in {"boundary_matcher_bundle_v2", "boundary_matcher_bundle_v3"} else [])
                matcher_names = (matcher[19] if matcher[0] == "boundary_matcher_bundle_v3"
                                 else sparse_names + matcher[3][0] + [matcher[3][1]])
                if matcher_names != child_private:
                    reject("nested matcher member mismatch")
            child_names.extend(child_private)
        if child_names + [root_name] != private:
            reject("nested group closure mismatch")
        all_private.extend(private); all_public.extend(public)
    names(all_private); names(all_public)
    if all_private != value[2] or all_public != value[3] or value[10][0][1] != expected_anchor:
        reject("batch member order or anchor mismatch")
    return value
