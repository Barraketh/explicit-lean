#!/usr/bin/env python3
"""Parser-free adversarial checks for the direct-simp AST trust boundary."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

from pipeline import tactic_syntax_ast as ast


MODULE = "Mathlib.Test.SimpAstIdentity"
SOURCE = '''import Mathlib

-- λ and 🧪 exercise byte/character offset conversion.
theorem first : True := by simp

theorem second : True := by aesop (add simp [True.intro])
'''
FIRST_REPLACEMENT = "theorem first : True := by exact True.intro"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def raw_inventory(module: str, request_id: str, source: str) -> dict:
    commands = []
    source_bytes = source.encode("utf-8")
    for ordinal, match in enumerate(re.finditer(r"(?m)^theorem (?:first|second) .*?$", source)):
        start_char, end_char = match.span()
        start = len(source[:start_char].encode("utf-8"))
        end = len(source[:end_char].encode("utf-8"))
        command_text = match.group(0)
        sites = []
        direct = re.search(r"\bby\s+(simp)(?:\s|$)", command_text)
        if direct:
            site_start_char = start_char + direct.start(1)
            site_end_char = start_char + direct.end(1)
            sites.append({
                "startByte": len(source[:site_start_char].encode("utf-8")),
                "endByte": len(source[:site_end_char].encode("utf-8")),
                "kind": "Lean.Parser.Tactic.simp",
            })
        commands.append({
            "commandOrdinal": ordinal,
            "kind": "Lean.Parser.Command.declaration",
            "startByte": start,
            "endByte": end,
            "simpSites": sites,
        })
    assert source_bytes
    return {
        "module": module,
        "requestId": request_id,
        "status": "ok",
        "reason": "complete_simp_syntax_inventory",
        "refusals": [],
        "commands": commands,
    }


def request_id(ordinal: int, module: str, source: str) -> str:
    return hashlib.sha256(
        f"simp-inventory\0batch\0{ordinal}\0{module}\0{digest(source.encode())}".encode()
    ).hexdigest()


def fake_batch(modules: list[dict[str, str]], *, repo_root=ast.ROOT,
               candidate_range_drift: bool = False,
               refuse_candidate: bool = False) -> list[dict]:
    results = []
    for index, entry in enumerate(modules):
        result = raw_inventory(
            entry["module"], request_id(index, entry["module"], entry["source"]),
            entry["source"],
        )
        if candidate_range_drift and index == 1:
            result["commands"][0]["startByte"] += 1
        if refuse_candidate and index == 1:
            result = {
                "module": entry["module"],
                "requestId": request_id(index, entry["module"], entry["source"]),
                "status": "failed",
                "reason": "module parser reported an error or recovery",
            }
        result = ast._validate_simp_inventory_result(
            result,
            module=entry["module"],
            source=entry["source"],
            source_bytes=entry["source"].encode("utf-8"),
            digest=digest(entry["source"].encode("utf-8")),
            request_id=request_id(index, entry["module"], entry["source"]),
            allow_parse_failure=True,
        )
        results.append(result)
    return results


def source_rows(source: str) -> list[dict]:
    inv = raw_inventory(MODULE, "fixture", source)
    raw = source.encode("utf-8")
    return [
        {
            "ordinal": item["commandOrdinal"],
            "start": item["startByte"],
            "end": item["endByte"],
            "kind": item["kind"],
            "sha256": digest(raw[item["startByte"]:item["endByte"]]),
        }
        for item in inv["commands"]
    ]


def assert_valid_gate() -> None:
    rows = source_rows(SOURCE)
    replacements = {0: FIRST_REPLACEMENT}
    candidate, ranges = ast._candidate_from_authenticated_rows(
        original_source=SOURCE, command_rows=rows,
        candidate_replacements=replacements,
    )
    assert candidate.startswith("import Mathlib\nimport ExplicitLean.ExplicitRw")
    assert ranges[0][0] > rows[0]["start"]  # generated header import is accounted for
    assert rows[0]["start"] > len(SOURCE[:SOURCE.index("theorem first")])
    assert rows[0]["start"] > SOURCE.index("theorem first")  # UTF-8 byte offset includes λ/🧪
    with patch.object(ast, "inventory_simp_tactics_batch", side_effect=fake_batch):
        ast.assert_success_commands_have_no_simp(
            module=MODULE,
            original_source=SOURCE,
            candidate_source=candidate,
            expected_source_sha256=digest(SOURCE.encode("utf-8")),
            command_rows=rows,
            success_ordinals={0},
            candidate_replacements=replacements,
        )

        no_import_source = "module\n-- λ\ntheorem first : True := by simp\n"
        no_import_rows = source_rows(no_import_source)
        no_import_replacements = {0: FIRST_REPLACEMENT}
        no_import_candidate, _ = ast._candidate_from_authenticated_rows(
            original_source=no_import_source, command_rows=no_import_rows,
            candidate_replacements=no_import_replacements,
        )
        assert no_import_candidate.startswith(
            "module\npublic import ExplicitLean.ExplicitRw\n-- λ"
        )
        ast.assert_success_commands_have_no_simp(
            module=MODULE,
            original_source=no_import_source,
            candidate_source=no_import_candidate,
            expected_source_sha256=digest(no_import_source.encode("utf-8")),
            command_rows=no_import_rows,
            success_ordinals={0},
            candidate_replacements=no_import_replacements,
        )

        bare_source = "theorem first : True := by simp\n"
        bare_rows = source_rows(bare_source)
        bare_replacements = {0: FIRST_REPLACEMENT}
        bare_candidate, bare_ranges = ast._candidate_from_authenticated_rows(
            original_source=bare_source, command_rows=bare_rows,
            candidate_replacements=bare_replacements,
        )
        assert bare_candidate.startswith("import ExplicitLean.ExplicitRw\n")
        assert bare_ranges[0][0] > bare_rows[0]["start"]
        ast.assert_success_commands_have_no_simp(
            module=MODULE,
            original_source=bare_source,
            candidate_source=bare_candidate,
            expected_source_sha256=digest(bare_source.encode("utf-8")),
            command_rows=bare_rows,
            success_ordinals={0},
            candidate_replacements=bare_replacements,
        )


def assert_residual_and_side_evidence() -> None:
    rows = source_rows(SOURCE)
    candidate, _ = ast._candidate_from_authenticated_rows(
        original_source=SOURCE, command_rows=rows,
        candidate_replacements={0: SOURCE.encode()[rows[0]["start"]:rows[0]["end"]].decode()},
    )
    with patch.object(ast, "inventory_simp_tactics_batch", side_effect=fake_batch):
        try:
            ast.assert_success_commands_have_no_simp(
                module=MODULE, original_source=SOURCE, candidate_source=candidate,
                expected_source_sha256=digest(SOURCE.encode()), command_rows=rows,
                success_ordinals={0}, candidate_replacements={
                    0: SOURCE.encode()[rows[0]["start"]:rows[0]["end"]].decode()
                },
            )
        except ast.SyntaxExtractionError as error:
            assert "still owns executable simp" in str(error)
        else:
            raise AssertionError("residual direct simp was accepted")

        safe_candidate, _ = ast._candidate_from_authenticated_rows(
            original_source=SOURCE, command_rows=rows,
            candidate_replacements={1: SOURCE.encode()[rows[1]["start"]:rows[1]["end"]].decode()},
        )
        ast.assert_success_commands_have_no_simp(
            module=MODULE, original_source=SOURCE, candidate_source=safe_candidate,
            expected_source_sha256=digest(SOURCE.encode()), command_rows=rows,
            success_ordinals={1}, candidate_replacements={
                1: SOURCE.encode()[rows[1]["start"]:rows[1]["end"]].decode()
            },
        )


def assert_original_identity_attacks_fail() -> None:
    rows = source_rows(SOURCE)
    replacements = {0: FIRST_REPLACEMENT}
    candidate, _ = ast._candidate_from_authenticated_rows(
        original_source=SOURCE, command_rows=rows,
        candidate_replacements=replacements,
    )
    attacks = []
    drifted = [dict(row) for row in rows]
    drifted[0]["start"] += 1
    drifted[0]["sha256"] = digest(SOURCE.encode()[drifted[0]["start"]:drifted[0]["end"]])
    attacks.append((drifted, "identity/range differs"))
    attacks.append(([dict(rows[1]), dict(rows[0])], "identity/range differs"))
    duplicated = [dict(rows[0]), dict(rows[0])]
    duplicated[1]["ordinal"] = 1
    attacks.append((duplicated, "identity/range differs"))

    with patch.object(ast, "inventory_simp_tactics_batch", side_effect=fake_batch):
        for forged_rows, message in attacks:
            try:
                ast.assert_success_commands_have_no_simp(
                    module=MODULE, original_source=SOURCE, candidate_source=candidate,
                    expected_source_sha256=digest(SOURCE.encode()), command_rows=forged_rows,
                    success_ordinals={0}, candidate_replacements=replacements,
                )
            except ast.SyntaxExtractionError as error:
                assert message in str(error), error
            else:
                raise AssertionError("forged source-command identity was accepted")

        reordered = ast.add_recorder_import(
            SOURCE[:rows[0]["start"]] +
            SOURCE.encode()[rows[1]["start"]:rows[1]["end"]].decode() +
            SOURCE[rows[0]["end"]:]
        )
        try:
            ast.assert_success_commands_have_no_simp(
                module=MODULE, original_source=SOURCE, candidate_source=reordered,
                expected_source_sha256=digest(SOURCE.encode()), command_rows=rows,
                success_ordinals={0}, candidate_replacements=replacements,
            )
        except ast.SyntaxExtractionError as error:
            assert "candidate source differs" in str(error)
        else:
            raise AssertionError("reordered candidate commands were accepted")


def assert_candidate_ranges_and_parser_refusal_fail() -> None:
    rows = source_rows(SOURCE)
    replacements = {0: FIRST_REPLACEMENT}
    candidate, _ = ast._candidate_from_authenticated_rows(
        original_source=SOURCE, command_rows=rows,
        candidate_replacements=replacements,
    )
    with patch.object(ast, "inventory_simp_tactics_batch",
                      side_effect=lambda modules, **kwargs: fake_batch(
                          modules, candidate_range_drift=True)):
        try:
            ast.assert_success_commands_have_no_simp(
                module=MODULE, original_source=SOURCE, candidate_source=candidate,
                expected_source_sha256=digest(SOURCE.encode()), command_rows=rows,
                success_ordinals={0}, candidate_replacements=replacements,
            )
        except ast.SyntaxExtractionError as error:
            assert "invalid or overlapping" in str(error) or "edit map" in str(error)
        else:
            raise AssertionError("candidate parser range drift was accepted")

    with patch.object(ast, "inventory_simp_tactics_batch",
                      side_effect=lambda modules, **kwargs: fake_batch(
                          modules, refuse_candidate=True)):
        try:
            ast.assert_success_commands_have_no_simp(
                module=MODULE, original_source=SOURCE, candidate_source=candidate,
                expected_source_sha256=digest(SOURCE.encode()), command_rows=rows,
                success_ordinals={0}, candidate_replacements=replacements,
            )
        except ast.SyntaxExtractionError as error:
            assert "parser inventory refused" in str(error)
        else:
            raise AssertionError("candidate parser refusal was accepted")


def assert_batch_response_order_is_authenticated() -> None:
    sources = ["import Mathlib\n", "import Mathlib\n-- λ\n"]
    with tempfile.TemporaryDirectory(prefix="simp-ast-cwd-audit-") as root:
        root_path = Path(root)

        def fake_run(command, *, cwd, text, capture_output, check, timeout):
            assert Path(cwd) == root_path
            assert not (root_path / ".lake").exists()
            triples = command[command.index("--simp-inventory-batch") + 1:]
            results = []
            for index in range(0, len(triples), 3):
                module, path, rid = triples[index:index + 3]
                source = Path(path).read_text(encoding="utf-8")
                results.append(raw_inventory(module, rid, source))
            return SimpleNamespace(returncode=0, stdout=json.dumps(results), stderr="")

        inputs = [{
            "module": MODULE,
            "source": source,
            "expected_source_sha256": digest(source.encode()),
        } for source in sources]
        with patch.object(ast.subprocess, "run", side_effect=fake_run):
            results = ast.inventory_simp_tactics_batch(inputs, repo_root=root_path)
        assert len(results) == 2
        assert [result["moduleSourceSha256"] for result in results] == [
            digest(source.encode()) for source in sources
        ]

        def swapped_run(command, **kwargs):
            triples = command[command.index("--simp-inventory-batch") + 1:]
            results = []
            for index in range(0, len(triples), 3):
                module, path, rid = triples[index:index + 3]
                source = Path(path).read_text(encoding="utf-8")
                results.append(raw_inventory(module, rid, source))
            return SimpleNamespace(returncode=0, stdout=json.dumps(results[::-1]), stderr="")

        with patch.object(ast.subprocess, "run", side_effect=swapped_run):
            try:
                ast.inventory_simp_tactics_batch(inputs, repo_root=root_path)
            except ast.SyntaxExtractionError as error:
                assert "requestId" in str(error)
            else:
                raise AssertionError("reordered batch AST output was accepted")


def assert_malformed_ast_output_fails_closed() -> None:
    source = "import Mathlib\n"
    expected = digest(source.encode())
    rid = request_id(0, MODULE, source)
    forged = {
        "module": MODULE,
        "requestId": rid,
        "status": "ok",
        "reason": "complete_simp_syntax_inventory",
        "refusals": [],
        "commands": [{
            "commandOrdinal": 0,
            "kind": "Lean.Parser.Command.declaration",
            "startByte": True,
            "endByte": 20,
            "simpSites": [],
        }],
    }
    try:
        ast._validate_simp_inventory_result(
            forged, module=MODULE, source=source, source_bytes=source.encode(),
            digest=expected, request_id=rid,
        )
    except ast.SyntaxExtractionError as error:
        assert "invalid byte range" in str(error)
    else:
        raise AssertionError("forged boolean source range was accepted")

    duplicate = raw_inventory(MODULE, rid, SOURCE)
    duplicate["commands"].append(dict(duplicate["commands"][0]))
    try:
        ast._validate_simp_inventory_result(
            duplicate, module=MODULE, source=SOURCE, source_bytes=SOURCE.encode(),
            digest=digest(SOURCE.encode()), request_id=rid,
        )
    except ast.SyntaxExtractionError as error:
        assert "command ownership" in str(error) or "overlapping" in str(error)
    else:
        raise AssertionError("duplicate forged command range was accepted")


def main() -> int:
    assert_valid_gate()
    assert_residual_and_side_evidence()
    assert_original_identity_attacks_fail()
    assert_candidate_ranges_and_parser_refusal_fail()
    assert_batch_response_order_is_authenticated()
    assert_malformed_ast_output_fails_closed()
    print("check_simp_ast_identity: PASS (6 parser-free trust-boundary checks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
