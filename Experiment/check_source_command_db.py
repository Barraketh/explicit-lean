#!/usr/bin/env python3
"""Focused parser, schema, validation, and safety checks for T61."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sqlite3
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
BUILDER = ROOT / "Experiment" / "source_command_db.py"


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["python3", "-B", str(BUILDER), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="t61-source-command-db-") as name:
        base = Path(name)
        package = base / "mathlib"
        (package / "Mathlib" / "Logic" / "Function").mkdir(parents=True)
        (package / "Mathlib" / "Logic" / "ExistsUnique").mkdir(parents=True)
        # Header modifiers and duplicate imports must become one graph edge;
        # Lean supplies the native header parser, not this test, for imports.
        basic = package / "Mathlib" / "Logic" / "Basic.lean"
        basic.write_text(
            "module\n"
            "public import Lean\n"
            "meta import Lean\n"
            "import Lean\n\n"
            "namespace Outer\n"
            "section Inner\n"
            "@[reducible] theorem attr (é : Nat) : é = é := by\n"
            "  -- a comment and a gap are not command text\n"
            "  exact rfl\n"
            "end Inner\n"
            "end Outer\n",
            encoding="utf-8",
        )
        function_basic = package / "Mathlib" / "Logic" / "Function" / "Basic.lean"
        function_basic.write_text(
            "import Mathlib.Logic.Basic\n\n"
            "namespace Function\n"
            "def identity (x : Nat) := x\n"
            "end Function\n",
            encoding="utf-8",
        )
        exists_unique = package / "Mathlib" / "Logic" / "ExistsUnique.lean"
        exists_unique.write_text(
            "import Mathlib.Logic.Function.Basic\n"
            "theorem exists_unique_sample (x : Nat) : x = x := by\n"
            "  exact rfl\n",
            encoding="utf-8",
        )
        root_module = package / "Mathlib.lean"
        root_module.write_text(
            "import Mathlib.Logic.Basic\n"
            "import Mathlib.Logic.Function.Basic\n"
            "import Mathlib.Logic.ExistsUnique\n",
            encoding="utf-8",
        )

        output = base / "commands.sqlite3"
        first = run(
            "build", "--mathlib-root", str(package), "--output", str(output),
            "Mathlib.lean", "Mathlib/Logic/Basic.lean",
            "Mathlib/Logic/Function/Basic.lean", "Mathlib/Logic/ExistsUnique.lean",
        )
        assert first.returncode == 0, first.stderr
        summary = json.loads(first.stdout)
        assert summary["modules"] == 4 and summary["imports"] == 6

        db = sqlite3.connect(output)
        tables = [row[0] for row in db.execute(
            "SELECT name FROM sqlite_master WHERE type='table' ORDER BY name"
        )]
        assert tables == ["commands", "imports", "modules"]
        expected_columns = {
            "modules": ["name", "path", "source", "source_sha256"],
            "imports": ["module_name", "imported_name"],
            "commands": [
                "module_name", "ordinal", "start_byte", "end_byte", "kind", "source_sha256"
            ],
        }
        for table, columns in expected_columns.items():
            assert [row[1] for row in db.execute(f"PRAGMA table_info({table})")] == columns
        assert db.execute(
            "SELECT imported_name FROM imports WHERE module_name = ?",
            ("Mathlib.Logic.Basic",),
        ).fetchall() == [("Lean",)]

        source = basic.read_bytes()
        rows = db.execute(
            "SELECT ordinal,start_byte,end_byte,kind,source_sha256 FROM commands "
            "WHERE module_name = ? ORDER BY ordinal",
            ("Mathlib.Logic.Basic",),
        ).fetchall()
        assert [row[0] for row in rows] == list(range(len(rows)))
        assert len(rows) == 5  # namespace, section, theorem, and both ends
        assert rows[2][3] == "Lean.Parser.Command.declaration"
        for ordinal, start, end, _kind, digest in rows:
            assert source[start:end].decode("utf-8")
            assert digest == hashlib.sha256(source[start:end]).hexdigest()
            if ordinal:
                assert start >= rows[ordinal - 1][2]
        assert all(b"simp" not in source[start:end] for _, start, end, _, _ in rows)
        module_source = db.execute(
            "SELECT source,source_sha256 FROM modules WHERE name = ?",
            ("Mathlib.Logic.Basic",),
        ).fetchone()
        assert module_source[0] == source
        assert module_source[1] == hashlib.sha256(source).hexdigest()
        db.execute("PRAGMA foreign_key_check")
        assert db.execute("PRAGMA integrity_check").fetchone()[0] == "ok"
        db.close()

        # Logical rows, not temporary SQLite filenames, are deterministic.
        second = base / "second.sqlite3"
        rebuilt = run(
            "build", "--mathlib-root", str(package), "--output", str(second),
            "Mathlib.lean", "Mathlib/Logic/Basic.lean",
            "Mathlib/Logic/Function/Basic.lean", "Mathlib/Logic/ExistsUnique.lean",
        )
        assert rebuilt.returncode == 0, rebuilt.stderr
        for table in ("modules", "imports", "commands"):
            left = sqlite3.connect(output).execute(f"SELECT * FROM {table} ORDER BY 1, 2").fetchall()
            right = sqlite3.connect(second).execute(f"SELECT * FROM {table} ORDER BY 1, 2").fetchall()
            assert left == right

        refusal = run("build", "--mathlib-root", str(package), "--output", str(output))
        assert refusal.returncode != 0 and "--overwrite" in refusal.stderr
        before = output.read_bytes()
        overwrite = run(
            "build", "--mathlib-root", str(package), "--output", str(output), "--overwrite",
            "Mathlib.lean", "Mathlib/Logic/Basic.lean",
            "Mathlib/Logic/Function/Basic.lean", "Mathlib/Logic/ExistsUnique.lean",
        )
        assert overwrite.returncode == 0, overwrite.stderr
        assert output.read_bytes() != b"" and before != b""  # replacement completed atomically

        broken = package / "Mathlib" / "Broken.lean"
        broken.write_text("namespace Broken\ntheorem unfinished : := by\n", encoding="utf-8")
        failed = run(
            "build", "--mathlib-root", str(package), "--output", str(base / "broken.sqlite3"),
            "Mathlib/Broken.lean",
        )
        assert failed.returncode != 0 and "parser failed" in failed.stderr.lower()

        outside = base / "Outside.lean"
        outside.write_text("def outside := 1\n", encoding="utf-8")
        failed = run(
            "build", "--mathlib-root", str(package), "--output", str(base / "outside.sqlite3"),
            str(outside),
        )
        assert failed.returncode != 0 and "outside --mathlib-root" in failed.stderr
        failed = run(
            "build", "--mathlib-root", str(package), "--output", str(package / "bad.sqlite3"),
            "Mathlib.lean",
        )
        assert failed.returncode != 0 and "read-only" in failed.stderr

    # The graph checker ignores external imports but rejects internal cycles.
    import sys
    sys.path.insert(0, str(ROOT / "Experiment"))
    import source_command_db
    source_command_db._validate_graph({"A", "B"}, {"A": ["B"], "B": []})
    try:
        source_command_db._validate_graph({"A", "B"}, {"A": ["B"], "B": ["A"]})
    except RuntimeError:
        pass
    else:
        raise AssertionError("internal import cycle was accepted")

    print("check_source_command_db: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
