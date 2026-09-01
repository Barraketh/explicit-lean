#!/usr/bin/env python3
"""Focused controls for the cold tree plan and resumable sequential runner."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

import cold_certified_tree as tree
import certified_module as base
import cold_certified_module as cold


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
        forged = plan.result()
        del forged["modules"]["Mathlib/B.lean"]
        forged["order"] = ["Mathlib/A.lean"]
        forged["planHash"] = tree._plan_hash(forged)
        with self.assertRaisesRegex(RuntimeError, "canonical"):
            tree.verify_plan(forged)

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
        self.source_a.write_text("theorem a : True := True.intro\n")
        incomplete_sources = self.root / "incomplete-sources"
        (incomplete_sources / "Mathlib").mkdir(parents=True)
        (incomplete_sources / "Mathlib/A.lean").write_text("theorem a : True := True.intro\n")
        with self.assertRaisesRegex(RuntimeError, "applied source"):
            tree.build_plan(self.manifest, self.depmap, source_root=self.sources, applied_root=incomplete_sources)

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
            return {"module": tree.dotted_module(module), "isModule": True, "outputArtifactFamily": family}

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
        (stray / "old.json").unlink()
        (stray / "old.bin").write_bytes(b"stale")
        with self.assertRaisesRegex(RuntimeError, "unexpected or stale"):
            tree.run_tree(plan, checkpoint_root=stray)

    def test_production_bounded_lifecycle_and_exclusion_contract(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        manifest["moduleFileCount"] = 2
        manifest_path = self.root / "complete-manifest.json"
        write_json(manifest_path, manifest)
        plan = tree.build_plan(manifest_path, self.depmap, source_root=self.sources)
        self.assertTrue(plan.complete_corpus)
        checkpoint_root = self.root / "production-checkpoints"; checkpoint_root.mkdir()
        output_root = self.root / "production-output"; output_root.mkdir()
        staging = self.root / "production-staging"; staging.mkdir()
        receipt_root = self.root / "production-receipts"; receipt_root.mkdir()
        work_root = self.root / "production-work"; work_root.mkdir()
        runtime = self.root / "runtime"; runtime.mkdir()
        imports = SimpleNamespace(search_path=(output_root,), translated_olean_root=output_root)
        oracle_path = self.root / "oracle"; oracle_path.write_bytes(b"oracle")
        auditor_path = self.root / "auditor"; auditor_path.write_bytes(b"auditor")
        oracle_path.chmod(0o755); auditor_path.chmod(0o755)
        oracle = base.InputFile(oracle_path, base.sha256(oracle_path))
        auditor = base.InputFile(auditor_path, base.sha256(auditor_path))
        cert_records = {}

        def checked(item):
            if base.sha256(item.path) != item.sha256:
                raise RuntimeError("hash mismatch")
            return item

        def fake_certify(*, module, applied, **kwargs):
            folder = work_root / module.replace(".", "-"); folder.mkdir()
            family = {}
            for suffix in base.SUFFIXES:
                artifact = folder / (module.rsplit(".", 1)[-1] + suffix)
                artifact.write_bytes(module.encode() + suffix.encode())
                family[str(artifact)] = base.sha256(artifact)
            receipt_path = folder / "receipt.json"
            write_json(receipt_path, {"synthetic": module})
            record = {"module": module, "isModule": True, "importEnvironment": {"searchPath": [str(output_root)]},
                      "outputArtifactFamily": family, "applied": {"sha256": applied.sha256}}
            cert_records[str(receipt_path)] = record
            return cold.Certification(receipt_path, base.sha256(receipt_path), record)

        def fake_verify(cert, **kwargs):
            return cert_records[str(cert.receipt_path)]

        with patch.object(tree.base, "_checked_file", side_effect=checked), \
             patch.object(tree.cold, "certify_module", side_effect=fake_certify), \
             patch.object(tree.cold, "verify_certification", side_effect=fake_verify):
            report = tree.run_production_tree(plan, imports=imports, oracle=oracle, auditor=auditor,
                                              checkpoint_root=checkpoint_root, output_root=output_root,
                                              staging_parent=staging, receipt_root=receipt_root,
                                              work_parent=work_root)
        self.assertTrue(report["wholeMathlib"])
        self.assertEqual(report["publicationAudit"]["modules"], 2)
        self.assertEqual(report["status"], "completed")
        published_artifact = next(output_root.rglob("*.olean"))
        original_artifact = published_artifact.read_bytes()
        published_artifact.write_bytes(b"mutated")
        with patch.object(tree.base, "_checked_file", side_effect=checked), \
             patch.object(tree.cold, "verify_certification", side_effect=fake_verify):
            with self.assertRaisesRegex(RuntimeError, "hash mismatch"):
                tree.run_production_tree(plan, imports=imports, oracle=oracle, auditor=auditor,
                                          checkpoint_root=checkpoint_root, output_root=output_root,
                                          staging_parent=staging, receipt_root=receipt_root,
                                          work_parent=work_root)
        published_artifact.write_bytes(original_artifact)
        publication_receipt = next(receipt_root.rglob("*.json"))
        original_receipt = publication_receipt.read_bytes()
        publication_receipt.write_bytes(b"mutated receipt")
        with patch.object(tree.base, "_checked_file", side_effect=checked), \
             patch.object(tree.cold, "verify_certification", side_effect=fake_verify):
            with self.assertRaisesRegex(RuntimeError, "hash mismatch"):
                tree.run_production_tree(plan, imports=imports, oracle=oracle, auditor=auditor,
                                          checkpoint_root=checkpoint_root, output_root=output_root,
                                          staging_parent=staging, receipt_root=receipt_root,
                                          work_parent=work_root)
        publication_receipt.write_bytes(original_receipt)
        (receipt_root / "stale.bin").write_bytes(b"stale")
        with patch.object(tree.base, "_checked_file", side_effect=checked), \
             patch.object(tree.cold, "verify_certification", side_effect=fake_verify):
            with self.assertRaisesRegex(RuntimeError, "unexpected or stale"):
                tree.run_production_tree(plan, imports=imports, oracle=oracle, auditor=auditor,
                                          checkpoint_root=checkpoint_root, output_root=output_root,
                                          staging_parent=staging, receipt_root=receipt_root,
                                          work_parent=work_root)
        (receipt_root / "stale.bin").unlink()

        excluded_manifest = json.loads(manifest_path.read_text())
        excluded_manifest["modules"][1]["disposition"] = "excluded"
        excluded_path = self.root / "excluded.json"
        write_json(excluded_path, excluded_manifest)
        with self.assertRaisesRegex(RuntimeError, "excluded disposition"):
            tree.build_plan(excluded_path, self.depmap, source_root=self.sources)
        excluded_plan = tree.build_plan(excluded_path, self.depmap, source_root=self.sources,
                                        excluded_modules=["Mathlib/B.lean"])
        self.assertEqual(excluded_plan.excluded, ("Mathlib/B.lean",))


if __name__ == "__main__":
    unittest.main()
