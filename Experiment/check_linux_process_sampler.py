#!/usr/bin/env python3
from pathlib import Path
import tempfile
import unittest

import linux_process_sampler as sampler


class LinuxProcessSamplerTest(unittest.TestCase):
    def _process(self, root: Path, pid: int, ppid: int, rss_kib: int, command: str) -> None:
        path = root / str(pid)
        path.mkdir()
        (path / "status").write_text(
            f"Name:\t{command}\nPid:\t{pid}\nPPid:\t{ppid}\nVmRSS:\t{rss_kib} kB\n"
        )
        (path / "cmdline").write_bytes(command.encode() + b"\0--fixture\0")

    def test_process_tree_and_categories(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            self._process(root, 100, 1, 10, "python3")
            self._process(root, 101, 100, 20, "lean")
            self._process(root, 102, 100, 5, "lake")
            self._process(root, 103, 102, 7, "python")
            self._process(root, 999, 1, 99, "lean")
            measured = sampler.ProcessTreeSampler(root)
            measured.observe(100)
            result = measured.result()
            self.assertEqual(result["processTreePeakAggregateRssBytes"], 42 * 1024)
            self.assertEqual(result["categories"]["python"]["peakAggregateRssBytes"], 17 * 1024)
            self.assertEqual(result["categories"]["python"]["observedPids"], [100, 103])
            self.assertEqual(result["categories"]["lean"]["peakSingleProcessRssBytes"], 20 * 1024)
            self.assertEqual(result["categories"]["lean"]["observedPids"], [101])

    def test_races_and_malformed_entries_are_ignored(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "self").mkdir()
            broken = root / "123"
            broken.mkdir()
            (broken / "status").write_text("Name:\tbroken\n")
            self.assertEqual(sampler.read_processes(root), [])


if __name__ == "__main__":
    unittest.main()
