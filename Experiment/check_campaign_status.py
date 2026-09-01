#!/usr/bin/env python3
"""Focused identity and fail-closed checks for campaign_status."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import campaign_status
import campaign_worker
from boundary_materialize_shard import REPORT_SCHEMA
from translation_index import connect, import_manifest, occurrence_id, plan_work, record_result


class CampaignStatusTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="campaign-status-")
        self.root = Path(self.temp.name)
        (self.root / "Mathlib").mkdir()
        self.source = self.root / "Mathlib" / "A.lean"
        source = "theorem a : True := by simp\n"
        self.source.write_text(source, encoding="utf-8")
        start = source.index("simp")
        source_hash = hashlib.sha256(source.encode()).hexdigest()
        module = "Mathlib/A.lean"
        self.manifest = self.root / "manifest.json"
        self.manifest_value = {
            "kind": "simp_engine_boundary_manifest",
            "reportSchema": 2,
            "allowDirty": False,
            "allowUnresolved": False,
            "modulePrefix": "Mathlib/",
            "moduleFileCount": 1,
            "occurrenceCount": 1,
            "repositoryCommit": "r" * 40,
            "mathlibCommit": "m" * 40,
            "lean": {"version": "v", "commit": "l" * 40},
            "implementationHashes": {"fixture": "implementation"},
            "sourceRoot": str(self.root),
            "modules": [{
                "module": module,
                "compiledModule": "Mathlib.A",
                "sourceHash": source_hash,
                "moduleHash": "module-hash",
                "occurrences": [{
                    "id": occurrence_id(module, start, start + 4),
                    "kind": "simp",
                    "source": "simp",
                    "startByte": start,
                    "endByte": start + 4,
                    "syntaxKind": "Lean.Parser.Tactic.simp",
                    "classification": "proof",
                    "disposition": "eligible",
                    "executionRole": "direct_executable",
                    "declarationKind": "proof",
                    "action": "materialize",
                }],
            }],
        }
        self.manifest.write_text(json.dumps(self.manifest_value, sort_keys=True), encoding="utf-8")
        self.database = self.root / "index.sqlite3"
        self.connection = connect(self.database)
        import_manifest(self.connection, self.manifest, source_root=self.root)

    def tearDown(self) -> None:
        self.connection.close()
        self.temp.cleanup()

    @staticmethod
    def report(calls: int = 1, manifest_hash: str | None = None) -> dict[str, object]:
        return {
            "reportSchema": REPORT_SCHEMA,
            "manifestHash": manifest_hash,
            "aggregate": {"materializeCount": calls},
            "modules": [{
                "replayGuard": {"schema": 1},
                "declarationOracle": {"replayGuard": {"schema": 1}},
            }],
        }

    def test_current_identity_excludes_historical_verified_row(self) -> None:
        implementation, toolchain = campaign_worker._identities(self.manifest_value)
        plan_work(self.connection, implementation, toolchain)
        record_result(
            self.connection, "Mathlib/A.lean", {"old": True}, {"old": True},
            status="success", translated=True, verified=True,
            result=self.report(7, "old-manifest"),
        )
        artifact = self.root / "artifact.json"
        artifact.write_text("{}", encoding="utf-8")
        plan_work(self.connection, implementation, toolchain)
        record_result(
            self.connection, "Mathlib/A.lean", implementation, toolchain,
            status="success", translated=True, verified=True,
            result=self.report(3, hashlib.sha256(self.manifest.read_bytes()).hexdigest()), artifact_ref=str(artifact),
        )
        status = campaign_status.snapshot(self.database, self.manifest, source_root=self.root, minimum_free_bytes=0)
        self.assertEqual(status["exactCurrentVerifiedModules"], 1)
        self.assertEqual(status["exactCurrentVerifiedCalls"], 3)
        self.assertEqual(status["historicalVerifiedModules"], 1)
        self.assertEqual(status["historicalVerifiedResults"], 1)
        self.assertEqual(status["historicalVerifiedCalls"], 7)
        self.assertEqual(status["cachedVerifiedModules"], 0)  # campaign-wide acceptance hold remains authoritative
        self.assertEqual(status["manifest"]["identityMismatchedModules"], [])

    def test_incomplete_manifest_fails_closed(self) -> None:
        bad = self.root / "bad.json"
        value = dict(self.manifest_value)
        value.pop("implementationHashes")
        bad.write_text(json.dumps(value), encoding="utf-8")
        with self.assertRaisesRegex(campaign_status.StatusError, "implementationHashes"):
            campaign_status.snapshot(self.database, bad, source_root=self.root)

    def test_default_manifest_is_derived_from_read_only_history(self) -> None:
        before = self.connection.execute("SELECT COUNT(*) FROM result_cache").fetchone()[0]
        status = campaign_status.snapshot(self.database, source_root=self.root, minimum_free_bytes=0)
        self.assertEqual(status["manifest"]["sha256"], hashlib.sha256(self.manifest.read_bytes()).hexdigest())
        self.assertEqual(self.connection.execute("SELECT COUNT(*) FROM result_cache").fetchone()[0], before)

    def test_missing_manifest_history_fails_closed(self) -> None:
        empty = self.root / "empty.sqlite3"
        other = connect(empty)
        other.close()
        with self.assertRaisesRegex(campaign_status.StatusError, "no manifest history"):
            campaign_status.snapshot(empty, minimum_free_bytes=0)


if __name__ == "__main__":
    unittest.main()
