#!/usr/bin/env python3
"""Parser-free selection and transactional controls for residual-success retry."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import sqlite3
import tempfile
from unittest import mock

import retry_missing_traces as retry
import retry_residual_simp_successes as residual
import tactic_syntax_ast as TSA


MODULE = "Mathlib.RetryResidualFixture"
SOURCE = (
    "theorem residual : True := by simp\n\n"
    "theorem configured : True := by aesop (add simp [True.intro])\n\n"
    "theorem pending : True := by simp\n"
)
COMMAND_KIND = "Lean.Parser.Command.declaration"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def make_db(root: Path) -> sqlite3.Connection:
    raw = SOURCE.encode("utf-8")
    module_path = "Mathlib/RetryResidualFixture.lean"
    pinned = root / ".lake" / "packages" / "mathlib" / module_path
    pinned.parent.mkdir(parents=True, exist_ok=True)
    pinned.write_bytes(raw)
    db = sqlite3.connect(":memory:")
    db.execute("CREATE TABLE modules(name TEXT,path TEXT,source BLOB,source_sha256 TEXT)")
    db.execute("CREATE TABLE commands(module_name TEXT,ordinal INTEGER,start_byte INTEGER,"
                "end_byte INTEGER,kind TEXT,source_sha256 TEXT,"
                "PRIMARY KEY(module_name,ordinal))")
    db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,status TEXT,"
                "replacement_text TEXT,error TEXT,PRIMARY KEY(module_name,ordinal))")
    db.execute("INSERT INTO modules VALUES(?,?,?,?)",
               (MODULE, module_path, raw, sha(raw)))
    starts = [SOURCE.index("theorem residual"), SOURCE.index("theorem configured"),
              SOURCE.index("theorem pending")]
    stops = [SOURCE.index("\n\n", starts[0]), SOURCE.index("\n\n", starts[1]), len(SOURCE)]
    for ordinal, (start_char, stop_char) in enumerate(zip(starts, stops)):
        start = len(SOURCE[:start_char].encode("utf-8"))
        stop = len(SOURCE[:stop_char].encode("utf-8"))
        db.execute("INSERT INTO commands VALUES(?,?,?,?,?,?)",
                   (MODULE, ordinal, start, stop, COMMAND_KIND, sha(raw[start:stop])))
    db.executemany(
        "INSERT INTO simp_replacements VALUES(?,?,?,?,?)",
        [
            (MODULE, 0, "success", "theorem residual : True := by simp", None),
            (MODULE, 1, "success",
             "theorem configured : True := by aesop (add simp [True.intro])", None),
            (MODULE, 2, "pending", None, None),
        ],
    )
    db.commit()
    return db


def fake_authenticated_inventory(*, module, original_source, candidate_source,
                                 expected_source_sha256, command_rows,
                                 candidate_replacements, repo_root):
    assert module == MODULE
    assert expected_source_sha256 == sha(SOURCE.encode())
    assert set(candidate_replacements) == {0, 1}
    assert "by simp" in candidate_source
    assert "aesop (add simp" in candidate_source
    assert len(command_rows) == 3
    _, command_ranges = TSA._candidate_from_authenticated_rows(
        original_source=original_source,
        command_rows=command_rows,
        candidate_replacements=candidate_replacements,
    )
    candidate_bytes = candidate_source.encode()
    commands = []
    for ordinal, (start_byte, end_byte) in enumerate(command_ranges):
        start_char = len(candidate_bytes[:start_byte].decode("utf-8"))
        end_char = len(candidate_bytes[:end_byte].decode("utf-8"))
        sites = []
        if ordinal == 0:
            site_start_char = candidate_source.index("simp")
            site_end_char = site_start_char + len("simp")
            site_start_byte = len(candidate_source[:site_start_char].encode())
            site_end_byte = len(candidate_source[:site_end_char].encode())
            sites = [{
                "kind": "Lean.Parser.Tactic.simp",
                "startByte": site_start_byte,
                "endByte": site_end_byte,
                "startChar": site_start_char,
                "endChar": site_end_char,
            }]
        elif ordinal == 2:
            site_start_char = candidate_source.rindex("simp")
            site_end_char = site_start_char + len("simp")
            site_start_byte = len(candidate_source[:site_start_char].encode())
            site_end_byte = len(candidate_source[:site_end_char].encode())
            sites = [{
                "kind": "Lean.Parser.Tactic.simp",
                "startByte": site_start_byte,
                "endByte": site_end_byte,
                "startChar": site_start_char,
                "endChar": site_end_char,
            }]
        commands.append({
            "commandOrdinal": ordinal,
            "startByte": start_byte,
            "endByte": end_byte,
            "startChar": start_char,
            "endChar": end_char,
            "simpSites": sites,
        })
    return {
        "status": "ok",
        "moduleSourceSha256": sha(candidate_source.encode()),
        "commands": commands,
    }


def selection_checks() -> None:
    with tempfile.TemporaryDirectory(prefix="residual-simp-select-") as directory:
        root = Path(directory)
        db = make_db(root)
        try:
            with mock.patch.object(
                    residual.TSA,
                    "authenticated_candidate_simp_inventory",
                    side_effect=fake_authenticated_inventory):
                rows, evidence = residual.select_residual_successes(
                    db, MODULE, repo_root=root)
            assert rows == [(MODULE, 0, "success", None)]
            assert set(evidence) == {0}
            assert evidence[0]["simp_sites"][0]["kind"] == "Lean.Parser.Tactic.simp"
            assert evidence[0]["source_sha256"] == sha(SOURCE.encode())
            assert evidence[0]["command_sha256"] == db.execute(
                "SELECT source_sha256 FROM commands WHERE module_name=? AND ordinal=0",
                (MODULE,),
            ).fetchone()[0]
            assert db.execute(
                "SELECT status,replacement_text FROM simp_replacements WHERE module_name=? "
                "AND ordinal=0", (MODULE,),
            ).fetchone() == ("success", "theorem residual : True := by simp")
        finally:
            db.close()

        db = make_db(root)
        try:
            with mock.patch.object(
                    residual.TSA,
                    "authenticated_candidate_simp_inventory",
                    side_effect=TSA.SyntaxExtractionError("parser refused")):
                try:
                    residual.select_residual_successes(db, MODULE, repo_root=root)
                except TSA.SyntaxExtractionError:
                    pass
                else:
                    raise AssertionError("parser-refused module produced retry targets")
            assert db.execute(
                "SELECT COUNT(*) FROM simp_replacements WHERE status='success'"
            ).fetchone()[0] == 2
        finally:
            db.close()


def success_evidence(replacement: str) -> dict:
    return {
        "ordinal": 0,
        "source_sha256": "a" * 64,
        "command_sha256": "b" * 64,
        "prior_replacement": replacement,
        "prior_replacement_sha256": sha(replacement.encode()),
        "candidate_source_sha256": "c" * 64,
        "command_range": {
            "startByte": 10,
            "endByte": 100,
            "startChar": 10,
            "endChar": 100,
        },
        "simp_sites": [{
            "kind": "Lean.Parser.Tactic.simp",
            "startByte": 20,
            "endByte": 24,
            "startChar": 20,
            "endChar": 24,
        }],
    }


def make_persistence_db(replacement: str) -> sqlite3.Connection:
    db = sqlite3.connect(":memory:")
    db.execute("CREATE TABLE modules(name TEXT PRIMARY KEY,source_sha256 TEXT)")
    db.execute("CREATE TABLE commands(module_name TEXT,ordinal INTEGER,source_sha256 TEXT,"
                "PRIMARY KEY(module_name,ordinal))")
    db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,status TEXT,"
                "replacement_text TEXT,error TEXT,PRIMARY KEY(module_name,ordinal))")
    db.execute("INSERT INTO modules VALUES('Mathlib.X',?)", ("a" * 64,))
    db.execute("INSERT INTO commands VALUES('Mathlib.X',0,?)", ("b" * 64,))
    db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',0,'success',?,?)",
               (replacement, "historical success error"))
    db.execute(retry.COMMAND_SCHEMA)
    db.execute(retry.RESIDUAL_SUCCESS_HISTORY_SCHEMA)
    db.execute("CREATE TABLE isolated_trace_audit(module_name TEXT,ordinal INTEGER,"
                "result_status TEXT,trace_state TEXT,compile_detail TEXT,updated_at TEXT,"
                "PRIMARY KEY(module_name,ordinal))")
    db.execute("INSERT INTO isolated_trace_audit VALUES(?,?,?,?,?,?)",
               ("Mathlib.X", 0, "success", "compiled", "old audit", "old time"))
    db.execute(retry.COMMAND_SCHEMA)
    db.execute(
        "INSERT INTO isolated_trace_command_retry VALUES(?,?,?,?,?,?,?,?,?)",
        ("Mathlib.X", 0, "a" * 64, "success", "compiled_success", "d" * 64,
         None, None, "prior retry"),
    )
    db.commit()
    return db


def persist_success_checks() -> None:
    old = "theorem x : True := by simp"
    new = "theorem x : True := by exact True.intro"
    evidence = success_evidence(old)
    db = make_persistence_db(old)
    live = {0: old}
    try:
        with mock.patch.object(retry.TSA, "assert_success_commands_have_no_simp"):
            retry._persist_command_result(
                db, "Mathlib.X", 0, "a" * 64, "success", "compiled_success",
                new, None, None, proof_hole_audited=True,
                original_source="source", candidate_source="candidate",
                command_rows=[], candidate_replacements={0: new},
                residual_success_evidence=evidence,
                live_success_replacements=live,
            )
        archived = db.execute(
            "SELECT prior_replacement_text,prior_error,prior_audit_json,"
            "prior_command_retry_json,residual_simp_sites_json "
            "FROM residual_simp_success_history"
        ).fetchone()
        assert archived[0:2] == (old, "historical success error")
        assert json.loads(archived[2])["compile_detail"] == "old audit"
        assert json.loads(archived[3])["result_status"] == "compiled_success"
        assert json.loads(archived[4])[0]["kind"] == "Lean.Parser.Tactic.simp"
        assert db.execute(
            "SELECT status,replacement_text,error FROM simp_replacements"
        ).fetchone() == ("success", new, None)
        assert live == {0: new}
    finally:
        db.close()

    db = make_persistence_db(old)
    live = {0: old}
    try:
        retry._persist_command_result(
            db, "Mathlib.X", 0, "a" * 64, "success", "compile_failed",
            None, None, "candidate did not compile",
            residual_success_evidence=evidence,
            live_success_replacements=live,
        )
        assert db.execute(
            "SELECT status,replacement_text,error FROM simp_replacements"
        ).fetchone() == ("compile_failed", None, "candidate did not compile")
        assert db.execute(
            "SELECT prior_replacement_text FROM residual_simp_success_history"
        ).fetchone() == (old,)
        assert live == {}
    finally:
        db.close()

    db = make_persistence_db(old)
    try:
        db.execute("CREATE TRIGGER reject_retry_update BEFORE UPDATE ON simp_replacements "
                   "WHEN NEW.replacement_text='theorem x : True := by exact True.intro' "
                   "BEGIN SELECT RAISE(ABORT,'injected update failure'); END")
        with mock.patch.object(retry.TSA, "assert_success_commands_have_no_simp"):
            try:
                retry._persist_command_result(
                    db, "Mathlib.X", 0, "a" * 64, "success", "compiled_success",
                    new, None, None, proof_hole_audited=True,
                    original_source="source", candidate_source="candidate",
                    command_rows=[], candidate_replacements={0: new},
                    residual_success_evidence=evidence,
                )
            except sqlite3.IntegrityError:
                pass
            else:
                raise AssertionError("injected replacement update failure was ignored")
        assert db.execute("SELECT COUNT(*) FROM residual_simp_success_history").fetchone()[0] == 0
        assert db.execute(
            "SELECT status,replacement_text,error FROM simp_replacements"
        ).fetchone() == ("success", old, "historical success error")
        assert db.execute(
            "SELECT result_status FROM isolated_trace_command_retry"
        ).fetchone() == ("compiled_success",)
    finally:
        db.close()

    db = make_persistence_db("changed after selection")
    try:
        try:
            retry._persist_command_result(
                db, "Mathlib.X", 0, "a" * 64, "success", "compile_failed",
                None, None, "failed",
                residual_success_evidence=evidence,
            )
        except retry.RetryError as error:
            assert "changed after AST selection" in str(error)
        else:
            raise AssertionError("stale success row evidence was accepted")
        assert db.execute("SELECT COUNT(*) FROM residual_simp_success_history").fetchone()[0] == 0
    finally:
        db.close()


def evidence_validation_checks() -> None:
    evidence = success_evidence("by simp")
    retry._validate_residual_success_evidence(
        "Mathlib.X", 0, "a" * 64, "success", evidence)
    bad = dict(evidence)
    bad["simp_sites"] = [{**evidence["simp_sites"][0],
                          "kind": "Lean.Parser.Tactic.aesopConfig"}]
    try:
        retry._validate_residual_success_evidence(
            "Mathlib.X", 0, "a" * 64, "success", bad)
    except retry.RetryError:
        pass
    else:
        raise AssertionError("non-direct AST node was accepted as retry evidence")

    evidence_by_ordinal = {0: evidence}
    retry._validate_residual_success_targets(
        [("Mathlib.X", 0, "success", None)], evidence_by_ordinal)
    retry._require_residual_success_site_alignment(
        "Mathlib.X", evidence_by_ordinal, {0: [7]})
    for target_rows, owners, expected in (
            ([("Mathlib.X", 0, "success", None),
              ("Mathlib.X", 0, "success", None)], {0: [7]}, "targets differ"),
            ([("Mathlib.X", 0, "success", None),
              ("Mathlib.X", 1, "pending", None)], {0: [7]}, "only historical success"),
            ([("Mathlib.X", 0, "success", None)], {}, "source-site owner")):
        try:
            if "source-site owner" in expected:
                retry._require_residual_success_site_alignment(
                    "Mathlib.X", evidence_by_ordinal, owners)
            else:
                retry._validate_residual_success_targets(target_rows, evidence_by_ordinal)
        except retry.RetryError as error:
            assert expected in str(error)
        else:
            raise AssertionError(f"unsafe residual target configuration was accepted: {expected}")


def copy_boundary_checks() -> None:
    with tempfile.TemporaryDirectory(prefix="residual-simp-copy-boundary-") as directory:
        root = Path(directory)
        old_root, old_run_root, old_runs_root, old_source, old_source_hash = (
            residual.ROOT, residual.RUN_ROOT, residual.RUNS_ROOT,
            residual.SOURCE_DATABASE, residual.SOURCE_DATABASE_SHA256,
        )
        try:
            residual.ROOT = (root / "repo").resolve()
            residual.ROOT.mkdir()
            residual.RUN_ROOT = residual.ROOT / ".lake" / "private" / \
                "T77-residual-success-retry-20260923"
            residual.RUNS_ROOT = residual.RUN_ROOT / "runs"
            residual.RUNS_ROOT.mkdir(parents=True)
            residual.SOURCE_DATABASE = root / "baseline.sqlite3"
            residual.SOURCE_DATABASE.write_bytes(b"baseline")
            residual.SOURCE_DATABASE_SHA256 = sha(b"baseline")
            run_id = "20260923T120000Z-1234abcd"
            run_dir = residual.RUNS_ROOT / run_id
            run_dir.mkdir(parents=True)
            database = run_dir / "mathlib-db-copy.sqlite3"
            database.write_bytes(b"copy")
            receipt = {
                "schema": 1,
                "sourceDatabase": str(residual.SOURCE_DATABASE),
                "sourceSha256": residual.SOURCE_DATABASE_SHA256,
                "databaseSha256": sha(b"copy"),
            }
            (run_dir / "database-copy.json").write_text(json.dumps(receipt), encoding="utf-8")
            assert residual._validate_writable_copy(database, run_dir) == database.resolve()
            linked = root / "other-link.sqlite3"
            os.link(database, linked)
            try:
                residual._validate_writable_copy(database, run_dir)
            except residual.ResidualRetryError as error:
                assert "single-link" in str(error)
            else:
                raise AssertionError("multiply linked DB copy was accepted")
        finally:
            (residual.RUN_ROOT, residual.RUNS_ROOT,
             residual.SOURCE_DATABASE, residual.SOURCE_DATABASE_SHA256,
             residual.ROOT) = (
                old_run_root, old_runs_root, old_source, old_source_hash,
                old_root,
            )


def main() -> int:
    selection_checks()
    persist_success_checks()
    evidence_validation_checks()
    copy_boundary_checks()
    print("check_retry_residual_simp_successes: PASS (selection, copy-boundary, and transaction controls)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
