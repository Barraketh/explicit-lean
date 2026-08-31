#!/usr/bin/env python3
"""Pure schema12 sidecar validation controls; no Lean or corpus work."""
import hashlib, json, tempfile, sys
from pathlib import Path
from unittest import TestCase, main
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_corpus as corpus_checks

class SidecarTests(TestCase):
    def test_recording_modes_are_explicit(self):
        self.assertEqual(materializer._recording_tactic("applied"), "simp_engine_boundary_record_applied")
        self.assertEqual(materializer._recording_tactic("stock"), "simp_engine_boundary_record")
        with self.assertRaises(ValueError): materializer._recording_tactic("replay")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.root = Path(self.tmp.name).resolve()
        self.path = self.root / "recording-invocation.json"
        self.source = self.root / "instrumented.lean"; self.source.write_bytes(b"source")
        runtime = self.root / "runtime"; runtime.write_bytes(b"runtime")
        nonce = "A" * 43
        self.data = {"kind":"boundary_compiler_invocation_v1", "module":"Mathlib.X",
            "source":str(self.source), "sourceSha256":hashlib.sha256(b"source").hexdigest(),
            "command":["lean", "X.lean"], "cwd":str(materializer.ROOT), "nonce":nonce,
            "timeoutSeconds":120, "runtime":str(runtime),
            "runtimeSha256":hashlib.sha256(runtime.read_bytes()).hexdigest(), "recordingMode":"applied"}
        self.path.write_text(json.dumps(self.data))
    def tearDown(self): self.tmp.cleanup()
    def ref(self): return {"path":str(self.path), "sha256":hashlib.sha256(self.path.read_bytes()).hexdigest()}
    def test_valid_and_mode_tamper(self):
        kwargs = {"expected_kind":"boundary_compiler_invocation_v1", "expected_command": self.data["command"], "expected_runtime": self.data["runtime"], "expected_timeout": 120}
        self.assertEqual(materializer._validate_invocation_ref(self.ref(), "sidecar", self.path, "Mathlib.X", "applied", {"source":str(self.source), "sourceSha256":self.data["sourceSha256"]}, **kwargs), "A" * 43)
        self.data["recordingMode"] = "stock"; self.path.write_text(json.dumps(self.data))
        with self.assertRaises(RuntimeError): materializer._validate_invocation_ref(self.ref(), "sidecar", self.path, "Mathlib.X", "applied", {"source":str(self.source), "sourceSha256":self.data["sourceSha256"]}, **kwargs)
    def test_extra_field_and_nonce_tamper_rejected(self):
        self.data["extra"] = True; self.path.write_text(json.dumps(self.data))
        kwargs = {"expected_kind":"boundary_compiler_invocation_v1", "expected_command": self.data["command"], "expected_runtime": self.data["runtime"], "expected_timeout": 120}
        with self.assertRaises(RuntimeError): materializer._validate_invocation_ref(self.ref(), "sidecar", self.path, "Mathlib.X", "applied", {}, **kwargs)

        self.data.pop("extra"); self.data["nonce"] = "bad"; self.path.write_text(json.dumps(self.data))
        with self.assertRaises(RuntimeError): materializer._validate_invocation_ref(self.ref(), "sidecar", self.path, "Mathlib.X", "applied", {}, **kwargs)

    def test_command_cwd_source_runtime_and_kind_tamper_rejected(self):
        kwargs = {"expected_kind":"boundary_compiler_invocation_v1", "expected_command": self.data["command"], "expected_runtime": self.data["runtime"], "expected_timeout": 120}
        source = {"source":str(self.source), "sourceSha256":self.data["sourceSha256"]}
        for field, value in (("command", ["lean"]), ("cwd", "/tmp"), ("source", str(self.root / "other.lean")),
                             ("runtimeSha256", "0" * 64), ("kind", "boundary_oracle_invocation_v1")):
            old = self.data.get(field); self.data[field] = value; self.path.write_text(json.dumps(self.data))
            with self.assertRaises(RuntimeError): materializer._validate_invocation_ref(self.ref(), "sidecar", self.path, "Mathlib.X", "applied", source, **kwargs)
            if old is None: self.data.pop(field)
            else: self.data[field] = old
            self.path.write_text(json.dumps(self.data))

    def test_compiler_receipt_precedes_launch(self):
        receipt = self.root / "compiler-invocation.json"
        environment, nonce = protocol.recording_subprocess_environment()
        runtime = Path(self.data["runtime"])
        launches = []

        def run(command, timeout, *, env):
            data = json.loads(receipt.read_bytes())
            self.assertEqual(data["command"], command)
            self.assertEqual(data["nonce"], nonce)
            self.assertEqual(data["sourceSha256"], materializer.sha256(self.source.read_bytes()))
            self.assertEqual(data["runtimeSha256"], materializer.sha256(runtime.read_bytes()))
            self.assertEqual(env[protocol.RUN_NONCE_ENV], nonce)
            launches.append(command)
            return 0, "", 0.0

        with patch.object(materializer, "_run_command", run):
            materializer._compile_copy(self.source, str(runtime), 120,
                env=environment, invocation_path=receipt, module="Mathlib.X", recording_mode="applied")
        self.assertEqual(len(launches), 1)

    def test_oracle_build_precedes_receipt_and_native_launch(self):
        binary = self.root / "oracle"
        binary.write_bytes(b"old binary")
        output = self.root / "oracle-output"
        output.mkdir()
        receipt = output / "oracle-invocation.json"
        applied = self.root / "applied.lean"
        applied.write_bytes(self.source.read_bytes())
        oracle_report = corpus_checks.shard_report_fixture()["modules"][0]["declarationOracle"]["report"]
        oracle_report["module"] = "Mathlib.X"
        stages = []

        def build(tool, target, path):
            self.assertEqual(tool, "oracle")
            self.assertEqual(path, binary)
            self.assertFalse(receipt.exists())
            binary.write_bytes(b"new binary")
            stages.append("built")

        def run(command, timeout, *, env):
            self.assertEqual(stages, ["built"])
            data = json.loads(receipt.read_bytes())
            self.assertEqual(command, ["lake", "env", str(binary), "Mathlib.X", str(self.source), str(applied)])
            self.assertEqual(data["command"], command)
            self.assertEqual(data["runtime"], str(binary))
            self.assertEqual(data["runtimeSha256"], materializer.sha256(b"new binary"))
            self.assertEqual(data["nonce"], env[protocol.RUN_NONCE_ENV])
            stages.append("launched")
            return 0, materializer.DECLARATION_ORACLE_MARKER + json.dumps(oracle_report) + "\n", 0.0

        with patch.object(materializer, "_oracle_runtime_path", lambda: binary), \
                patch.object(materializer.tool_cache, "_build", build), \
                patch.object(materializer, "_run_command", run):
            result = materializer.run_declaration_oracle("Mathlib/X.lean", self.source, applied,
                output, self.data["runtime"], 120)
        self.assertEqual(result["status"], "success")
        self.assertEqual(stages, ["built", "launched"])

if __name__ == "__main__": main()
