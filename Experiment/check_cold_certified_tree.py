#!/usr/bin/env python3
"""Focused controls for the cold tree plan and resumable sequential runner."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import cold_certified_tree as tree
import certified_module as base


def write_json(path: Path, value: object) -> str:
    payload = json.dumps(value, sort_keys=True, indent=2).encode() + b"\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(payload)
    return hashlib.sha256(payload).hexdigest()


class ColdTreeControls(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="cold-tree-controls-")
        self.root = Path(self.temp.name)
        self.sources = self.root / "sources"
        self.sources.mkdir()
        self.source_a = self.sources / "Mathlib/A.lean"
        self.source_b = self.sources / "Mathlib/B.lean"
        self.source_a.parent.mkdir()
        self.source_a.write_text("theorem a : True := True.intro\n")
        self.source_b.write_text("import Mathlib.A\ntheorem b : True := True.intro\n")
        self.manifest = self.root / "manifest.json"
        self.depmap = self.root / "dependencies.json"
        self.source_hashes = {"Mathlib/A.lean": base.sha256(self.source_a), "Mathlib/B.lean": base.sha256(self.source_b)}
        write_json(self.manifest, {"kind": "simp_engine_boundary_manifest", "reportSchema": 2,
                                   "allowDirty": False, "allowUnresolved": False,
                                   "allowUnclassified": False, "modules": [
                                       {"module": "Mathlib/A.lean", "sourceHash": self.source_hashes["Mathlib/A.lean"], "sourcePath": str(self.source_a)},
                                       {"module": "Mathlib/B.lean", "sourceHash": self.source_hashes["Mathlib/B.lean"], "sourcePath": str(self.source_b)}]})
        write_json(self.depmap, {"Mathlib/A.lean": {"sourceHash": self.source_hashes["Mathlib/A.lean"], "dependencies": []},
                                 "Mathlib/B.lean": {"sourceHash": self.source_hashes["Mathlib/B.lean"], "dependencies": ["Mathlib.A"]}})

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_stable_plan_and_input_hashes(self) -> None:
        plan = tree.build_plan(self.manifest, self.depmap, source_root=self.sources)
        self.assertEqual(plan.order, ("Mathlib/A.lean", "Mathlib/B.lean"))
        self.assertEqual(tree.verify_plan(plan).plan_hash, plan.plan_hash)
        plan_file = self.root / "plan.json"
        self.assertEqual(tree.write_plan(plan_file, plan), base.sha256(plan_file))
        self.assertEqual(tree.verify_plan(json.loads(plan_file.read_text())).plan_hash, plan.plan_hash)
        value = plan.result()
        value["order"] = list(reversed(value["order"]))
        with self.assertRaisesRegex(RuntimeError, "plan hash mismatch"):
            tree.verify_plan(value)

    def test_rejects_dirty_unjoined_cycle_and_source_mismatch(self) -> None:
        dirty = json.loads(self.manifest.read_text())
        dirty["allowDirty"] = True
        dirty_path = self.root / "dirty.json"
        write_json(dirty_path, dirty)
        with self.assertRaisesRegex(RuntimeError, "dirty"):
            tree.build_plan(dirty_path, self.depmap, source_root=self.sources)

        missing = json.loads(self.depmap.read_text())
        del missing["Mathlib/B.lean"]
        missing_path = self.root / "missing.json"
        write_json(missing_path, missing)
        with self.assertRaisesRegex(RuntimeError, "incomplete"):
            tree.build_plan(self.manifest, missing_path, source_root=self.sources)

        cycle = json.loads(self.depmap.read_text())
        cycle["Mathlib/A.lean"]["dependencies"] = ["Mathlib.B"]
        cycle_path = self.root / "cycle.json"
        write_json(cycle_path, cycle)
        with self.assertRaisesRegex(RuntimeError, "cycle"):
            tree.build_plan(self.manifest, cycle_path, source_root=self.sources)

        changed = self.source_a.read_bytes() + b"-- changed\n"
        self.source_a.write_bytes(changed)
        with self.assertRaisesRegex(RuntimeError, "source hash mismatch"):
            tree.build_plan(self.manifest, self.depmap, source_root=self.sources)

    def test_runner_writes_and_resumes_immutable_checkpoints(self) -> None:
        plan = tree.build_plan(self.manifest, self.depmap, source_root=self.sources)
        checkpoints = self.root / "checkpoints"
        checkpoints.mkdir()
        calls: list[str] = []

        def certify(module, node, dependencies):
            calls.append(module)
            family = {}
            output = self.root / "artifacts" / module
            output.mkdir(parents=True)
            for suffix in base.SUFFIXES:
                artifact = output / (Path(module).stem.removesuffix(".lean") + suffix)
                artifact.write_bytes((module + suffix).encode())
                family[str(artifact)] = base.sha256(artifact)
            fake_records[module] = family
            receipt_path = self.root / "receipts" / (Path(module).stem + ".json")
            write_json(receipt_path, {"synthetic": module})
            return {"certification": {"path": str(receipt_path), "sha256": base.sha256(receipt_path)},
                    "artifactFamily": family, "isModule": True}

        fake_records = {}
        def fake_verify(cert):
            value = json.loads(cert.receipt_path.read_text())
            module = value["synthetic"]
            family = fake_records[module]
            return {"module": tree.dotted_module(module), "outputArtifactFamily": family}

        def fake_validate(path, checked_plan, *, expected_sha256=None):
            result = original_validate(path, checked_plan, expected_sha256=expected_sha256)
            fake_records[result["module"]] = result["artifactFamily"]
            return result

        original_validate = tree.validate_checkpoint
        with patch.object(tree.cold, "verify_certification", side_effect=fake_verify):
            # The first pass needs to register each produced family before its
            # checkpoint is revalidated.
            with patch.object(tree, "validate_checkpoint", side_effect=fake_validate):
                first = tree.run_tree(plan, checkpoint_root=checkpoints, certify=certify)
        self.assertEqual(calls, list(plan.order))
        self.assertEqual(first["status"], "completed")
        calls.clear()
        with patch.object(tree.cold, "verify_certification", side_effect=fake_verify):
            resumed = tree.run_tree(plan, checkpoint_root=checkpoints, certify=certify)
        self.assertEqual(calls, [])
        self.assertEqual(resumed["status"], "completed")

        checkpoint = checkpoints / "Mathlib/A.json"
        value = json.loads(checkpoint.read_text())
        value["planHash"] = "0" * 64
        checkpoint.write_text(json.dumps(value))
        with patch.object(tree.cold, "verify_certification", side_effect=fake_verify), self.assertRaisesRegex(RuntimeError, "plan hash"):
            tree.run_tree(plan, checkpoint_root=checkpoints, certify=certify)

    def test_dependency_map_hashed_keys_and_stray_checkpoint_rejected(self) -> None:
        values = json.loads(self.depmap.read_text())
        hashed = {f"{key}@{value['sourceHash']}": value for key, value in values.items()}
        hashed_path = self.root / "hashed-dependencies.json"
        write_json(hashed_path, hashed)
        plan = tree.build_plan(self.manifest, hashed_path, source_root=self.sources)
        self.assertEqual(plan.order[-1], "Mathlib/B.lean")
        stray = self.root / "checkpoints"
        stray.mkdir()
        write_json(stray / "old.json", {"stale": True})
        with self.assertRaisesRegex(RuntimeError, "unexpected or stale"):
            tree.run_tree(plan, checkpoint_root=stray)


if __name__ == "__main__":
    unittest.main()
