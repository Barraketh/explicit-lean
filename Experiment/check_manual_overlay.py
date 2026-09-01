#!/usr/bin/env python3
"""Focused protocol checks for :mod:`manual_overlay`."""

from __future__ import annotations

import hashlib
import json
import copy
from pathlib import Path
import tempfile
import unittest

import manual_overlay as overlay
import boundary_materialize_shard as materializer
from check_simp_engine_boundary_corpus import shard_report_fixture
import simp_engine_inventory as inventory


ENV = {
    "mathlibCommit": "1" * 40,
    "lean": {"version": "4.32.2", "commit": "2" * 40},
}
MODULE = "Mathlib/Test.lean"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class ManualOverlayChecks(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        source_dir = self.root / "Mathlib"
        source_dir.mkdir()
        self.source = b"example : True := by\n  simp\nexample : True := by\n  simp\n"
        (source_dir / "Test.lean").write_bytes(self.source)
        first = self.source.index(b"simp")
        second = self.source.index(b"simp", first + 1)
        self.ranges = [(first, first + 4), (second, second + 4)]
        self.database = self.root / "overrides.json"
        self.manifest = self.root / "manifest.json"
        self.write_files()

    def tearDown(self) -> None:
        self.temp.cleanup()

    def write_files(self, *, entries: list[dict[str, object]] | None = None, binding: object = None) -> None:
        first, _ = self.ranges
        oid = inventory.occurrence_id(MODULE, *first)
        if entries is None:
            entries = [{
                "module": MODULE,
                "moduleSourceSha256": digest(self.source),
                "occurrence": oid,
                "startByte": first[0],
                "endByte": first[1],
                "source": "simp",
                "replacement": "rfl",
            }]
        db = {"kind": "simp_manual_overrides", "schema": 1, **ENV, "overrides": entries}
        # Keep the database's prescribed nesting for its Lean identity.
        db["lean"] = dict(ENV["lean"])
        self.database.write_text(json.dumps(db, sort_keys=True), encoding="utf-8")
        occurrences = []
        for start, end in self.ranges:
            occurrences.append({
                "id": inventory.occurrence_id(MODULE, start, end),
                "kind": "simp",
                "source": "simp",
                "startByte": start,
                "endByte": end,
                "syntaxKind": "Lean.Parser.Tactic.simp",
                "executionRole": "direct_executable",
                "declarationKind": "none",
                "action": "materialize",
            })
        manifest = {
            "kind": "simp_engine_boundary_manifest",
            "reportSchema": 2,
            "allowUnresolved": False,
            **ENV,
            "manualOverrides": binding if binding is not None else {
                "sha256": digest(self.database.read_bytes()), "schema": 1,
            },
            "occurrenceCount": len(occurrences),
            "modules": [{"module": MODULE, "sourceHash": digest(self.source), "occurrences": occurrences}],
        }
        self.manifest.write_text(json.dumps(manifest, sort_keys=True), encoding="utf-8")

    def load(self) -> overlay.Overlay:
        return overlay.load_overlay(self.manifest, self.database, source_root=self.root)

    def test_load_identity_apply_and_shift(self) -> None:
        value = self.load()
        self.assertEqual(value.counts, {"modules": 1, "canonicalOccurrences": 2, "manualOverrides": 1, "untouchedOccurrences": 1})
        self.assertEqual(tuple(value.entries_by_module()), (MODULE,))
        identity = value.canonical_identity()
        self.assertEqual(identity, overlay.canonical_json(value.identity()))
        self.assertEqual(json.loads(identity)["database"]["sha256"], digest(self.database.read_bytes()))
        patched = value.apply(MODULE)
        self.assertIn(b"rfl\n    -- Original simp:\n    -- simp", patched)
        shifted = value.shifted_occurrences(MODULE)
        self.assertEqual(len(shifted), 1)
        row = shifted[0]
        self.assertEqual(row["canonicalId"], inventory.occurrence_id(MODULE, *self.ranges[1]))
        self.assertEqual(row["id"], inventory.occurrence_id(MODULE, row["startByte"], row["endByte"]))
        self.assertGreater(row["startByte"], self.ranges[1][0])
        self.assertEqual(row["action"], "materialize")

    def test_rejects_bad_database_binding(self) -> None:
        self.write_files(binding={"sha256": "0" * 64, "schema": 1})
        with self.assertRaisesRegex(RuntimeError, "database hash"):
            self.load()

    def test_rejects_nonexact_range_and_nested_supported_occurrence(self) -> None:
        first, second = self.ranges
        oid = inventory.occurrence_id(MODULE, first[0], second[1])
        bad = [{
            "module": MODULE, "moduleSourceSha256": digest(self.source), "occurrence": oid,
            "startByte": first[0], "endByte": second[1],
            "source": self.source[first[0]:second[1]].decode(), "replacement": "rfl",
        }]
        self.write_files(entries=bad)
        with self.assertRaisesRegex(RuntimeError, "exactly one manifest occurrence"):
            self.load()

    def test_rejects_stale_canonical_source(self) -> None:
        (self.root / "Mathlib" / "Test.lean").write_bytes(self.source.replace(b"True", b"False", 1))
        with self.assertRaisesRegex(RuntimeError, "canonical source hash"):
            self.load()

    def test_sparse_load_preserves_full_global_identity(self) -> None:
        value = json.loads(self.manifest.read_text())
        value["moduleFileCount"] = 1
        self.manifest.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
        full = self.load()
        sparse = overlay._load_overlay_projected(
            self.manifest, self.database, source_root=self.root,
            manifest_value=value, manifest_bytes=self.manifest.read_bytes(),
            module_records={MODULE: value["modules"][0]},
        )
        self.assertEqual(sparse.identity(), full.identity())
        self.assertEqual(sparse.counts["canonicalOccurrences"], 2)

    def test_composite_report_keeps_manual_ids_out_of_recorder_evidence(self) -> None:
        report = shard_report_fixture()
        module = report["modules"][0]
        identity = {
            "kind": "simp_manual_overlay",
            "schema": 2,
            "database": {
                "sha256": "a" * 64,
                "schema": 1,
                "environment": {
                    "mathlibCommit": report["mathlibCommit"], "lean": report["lean"]
                },
            },
            "environment": {
                "mathlibCommit": report["mathlibCommit"], "lean": report["lean"]
            },
            "counts": {
                "modules": 1, "canonicalOccurrences": 3,
                "manualOverrides": 1, "untouchedOccurrences": 2,
            },
        }
        mappings = []
        for index, occurrence in enumerate(module["occurrenceResults"]):
            mappings.append({
                "canonicalId": f"canonical-{index}",
                "effectiveId": occurrence["occurrence"],
                "kind": "simp", "source": "simp",
                "canonicalStartByte": 20 + index * 10,
                "canonicalEndByte": 24 + index * 10,
                "effectiveStartByte": 40 + index * 10,
                "effectiveEndByte": 44 + index * 10,
            })
        module["manualOverlay"] = {
            "identity": identity,
            "canonicalSource": {"path": "/tmp/canonical.lean", "sha256": "canonical-hash"},
            "effectiveBase": copy.deepcopy(module["original"]),
            "finalComposite": {
                "path": module["materialized"]["path"],
                "sha256": module["materialized"]["sha256"],
            },
            "manualIds": ["manual-occurrence"],
            "manualReplacements": [{
                "canonicalId": "manual-occurrence", "kind": "simp", "source": "simp",
                "canonicalStartByte": 10, "canonicalEndByte": 14,
                "effectiveStartByte": 10, "effectiveEndByte": 80,
                "replacementSha256": "b" * 64, "renderedSha256": "c" * 64,
            }],
            "ordinaryOccurrenceMap": mappings,
            "canonicalOracleInvocation": {
                "path": "/tmp/canonical-oracle-invocation.json", "sha256": "invocation-hash"
            },
            "canonicalDeclarationOracle": copy.deepcopy(module["declarationOracle"]),
        }
        module["canonicalTotalCount"] = 3
        module["manualReplacementCount"] = 1
        report["manualOverlay"] = identity
        report["canonicalTotalCount"] = 3
        report["manualReplacementCount"] = 1
        report["aggregate"]["canonicalTotalCount"] = 3
        report["aggregate"]["manualReplacementCount"] = 1
        self.assertIs(materializer.validate_shard_shape(report), report)

        impossible_counts = copy.deepcopy(report)
        impossible_identity = impossible_counts["manualOverlay"]
        impossible_identity["counts"] = {
            "modules": 999,
            "canonicalOccurrences": 0,
            "manualOverrides": 0,
            "untouchedOccurrences": 0,
        }
        impossible_counts["modules"][0]["manualOverlay"]["identity"] = impossible_identity
        with self.assertRaisesRegex(RuntimeError, "exceeds global manual overlay identity"):
            materializer.validate_shard_shape(impossible_counts)

        forged = copy.deepcopy(report)
        forged["modules"][0]["manualOverlay"]["manualIds"] = ["occurrence"]
        forged["modules"][0]["manualOverlay"]["manualReplacements"][0]["canonicalId"] = "occurrence"
        with self.assertRaisesRegex(RuntimeError, "leaked into recorder"):
            materializer.validate_shard_shape(forged)


if __name__ == "__main__":
    unittest.main()
