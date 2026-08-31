import hashlib, importlib.util, json, tempfile, unittest
from pathlib import Path
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("dedup", Path(__file__).with_name("certificate_storage.py"))
dedup = importlib.util.module_from_spec(spec); spec.loader.exec_module(dedup)

class T(unittest.TestCase):
    def case(self, *, is_module=True):
        td = tempfile.TemporaryDirectory(); root = Path(td.name).resolve(); work = root / "work"; work.mkdir()
        suffixes = dedup.SUFFIXES if is_module else dedup.SUFFIXES[:1]
        families = {}
        for family in dedup.FAMILIES:
            q = work / family; q.mkdir(); families[family] = {}
            for suffix in suffixes:
                data = (b"stock" if family.endswith("stock") else b"applied") + suffix.encode()
                path = q / "M"; path = path.with_suffix(suffix); path.write_bytes(data)
                families[family][str(path)] = hashlib.sha256(data).hexdigest()
        receipt = {"kind": "simp_engine_cold_certified_module", "schema": 1,
                   "status": "certified_in_quarantine", "module": "M", "isModule": is_module,
                   "quarantine": str(work / "ordinary-applied"), "artifactFamilies": families}
        rp = work / "receipt.json"; rp.write_text(json.dumps(receipt)); return td, work, rp

    def test_separate_stock_applied_groups_and_repeat(self):
        td, work, rp = self.case(); self.addCleanup(td.cleanup)
        with patch.object(dedup, "_verify") as verify:
            first = dedup.deduplicate(rp)
            second = dedup.deduplicate(rp)
            self.assertEqual(first["paths"], 16)
            self.assertEqual(second["paths"], 0)
            self.assertGreater(first["logicalBytes"], first["physicalBytes"])
            self.assertGreater(first["savedUniqueInodeBytes"], 0)
            self.assertEqual(second["logicalBytes"], first["logicalBytes"])
            self.assertEqual(second["physicalBytes"], first["physicalBytes"])
            self.assertEqual(second["savedUniqueInodeBytes"], 0)
            self.assertEqual(verify.call_count, 4)
        for suffix in dedup.SUFFIXES:
            for side in ("stock", "applied"):
                names = [work / f / ("M" + suffix) for f in dedup.GROUPS[side]]
                self.assertEqual(len({p.stat().st_ino for p in names}), 1)
            self.assertNotEqual((work / "ordinary-stock" / ("M" + suffix)).read_bytes(),
                                (work / "ordinary-applied" / ("M" + suffix)).read_bytes())

    def test_nonmodule_has_one_artifact(self):
        td, _, rp = self.case(is_module=False); self.addCleanup(td.cleanup)
        with patch.object(dedup, "_verify"):
            self.assertEqual(dedup.deduplicate(rp)["paths"], 4)

    def test_preflight_failures_leave_bytes_and_temp_clean(self):
        td, work, rp = self.case(); self.addCleanup(td.cleanup)
        before = {p: p.read_bytes() for p in work.rglob("M.*")}
        poison = work / "audited-stock" / ".M.olean.dedup-tmp"; poison.write_bytes(b"x")
        with patch.object(dedup, "_verify"), self.assertRaises(dedup.DedupError): dedup.deduplicate(rp)
        self.assertEqual(before, {p: p.read_bytes() for p in work.rglob("M.*")})
        poison.unlink()
        with patch.object(dedup, "_verify"), self.assertRaises(OSError): dedup.deduplicate(rp, fail_after=1)
        self.assertEqual(before, {p: p.read_bytes() for p in work.rglob("M.*")})
        self.assertFalse(list(work.rglob("*.dedup-tmp")))

    def test_escape_and_ancestor_symlink_and_missing_rejected(self):
        td, work, rp = self.case(); self.addCleanup(td.cleanup)
        data = json.loads(rp.read_text()); key = next(iter(data["artifactFamilies"]["ordinary-stock"]))
        data["artifactFamilies"]["ordinary-stock"][str(Path(key).parent / ".." / Path(key).name)] = data["artifactFamilies"]["ordinary-stock"].pop(key)
        rp.write_text(json.dumps(data))
        with patch.object(dedup, "_verify"), self.assertRaises(dedup.DedupError): dedup.deduplicate(rp)
        td2, work2, rp2 = self.case(); self.addCleanup(td2.cleanup)
        missing = work2 / "bridge-stock" / "M.olean"; missing.unlink()
        with patch.object(dedup, "_verify"), self.assertRaises(dedup.DedupError): dedup.deduplicate(rp2)
        td3, work3, rp3 = self.case(); self.addCleanup(td3.cleanup)
        original = work3 / "bridge-stock" / "M.olean"; original.unlink()
        original.parent.rename(work3 / "bridge-stock-real"); (work3 / "bridge-stock").symlink_to(work3 / "bridge-stock-real")
        with patch.object(dedup, "_verify"), self.assertRaises(dedup.DedupError): dedup.deduplicate(rp3)

    def test_production_verifier_is_gate_and_receipt_unchanged(self):
        td, _, rp = self.case(); self.addCleanup(td.cleanup); original = rp.read_bytes()
        with patch.object(dedup, "_verify", side_effect=dedup.DedupError("invalid receipt")), self.assertRaises(dedup.DedupError): dedup.deduplicate(rp)
        self.assertEqual(rp.read_bytes(), original)

if __name__ == "__main__": unittest.main()
