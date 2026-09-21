#!/usr/bin/env python3
"""Focused parser, schema, validation, and safety checks for T61."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import signal
import time
import sqlite3
import subprocess
import sys
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
            "import Lean\n"
            "public import Lean\n"
            "meta import Lean\n"
            "public meta import Lean\n"
            "import all Lean\n\n"
            "namespace Outer\n"
            "\n"
            "-- between namespace and section: λ é\n"
            "\n"
            "section Inner\n"
            "\n"
            "-- between section and theorem: β\n"
            "@[reducible] theorem attr (é : Nat) : é = é := by\n"
            "  exact rfl\n"
            "\n"
            "-- between theorem and end: γ\n"
            "end Inner\n"
            "\n"
            "-- between end commands: δ\n"
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
            "--batch-size", "1", "--jobs", "2",
            "Mathlib.lean", "Mathlib/Logic/Basic.lean",
            "Mathlib/Logic/Function/Basic.lean", "Mathlib/Logic/ExistsUnique.lean",
        )
        assert first.returncode == 0, first.stderr
        progress = [json.loads(line) for line in first.stderr.splitlines()]
        assert progress[0]["event"] == "resume"
        progress_rows = [row for row in progress if row["event"] == "progress"]
        assert len(progress_rows) == 4
        assert all(row["completed_batches"] >= 1 for row in progress_rows)
        assert all(row["total_batches"] == 4 for row in progress_rows)
        assert all(row["modules_per_second"] is not None for row in progress_rows)
        assert all(row["eta_seconds"] is not None for row in progress_rows)
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
        ).fetchall() == [("Lean",)]  # five differently-modified imports, one name edge

        source = basic.read_bytes()
        header_end = source.index(b"namespace Outer")
        assert source[:header_end].decode("utf-8") == (
            "module\n"
            "import Lean\n"
            "public import Lean\n"
            "meta import Lean\n"
            "public meta import Lean\n"
            "import all Lean\n\n"
        )
        rows = db.execute(
            "SELECT ordinal,start_byte,end_byte,kind,source_sha256 FROM commands "
            "WHERE module_name = ? ORDER BY ordinal",
            ("Mathlib.Logic.Basic",),
        ).fetchall()
        assert [row[0] for row in rows] == list(range(len(rows)))
        assert len(rows) == 5  # namespace, section, theorem, and both ends
        assert rows[2][3] == "Lean.Parser.Command.declaration"
        expected_commands = [
            b"namespace Outer",
            b"section Inner",
            "@[reducible] theorem attr (é : Nat) : é = é := by\n  exact rfl".encode(),
            b"end Inner",
            b"end Outer",
        ]
        assert [source[start:end] for _, start, end, _, _ in rows] == expected_commands
        for ordinal, start, end, _kind, digest in rows:
            assert source[start:end].decode("utf-8")
            assert digest == hashlib.sha256(source[start:end]).hexdigest()
            if ordinal:
                assert start >= rows[ordinal - 1][2]
                gap = source[rows[ordinal - 1][2]:start]
                assert gap and b"-- between" in gap
                assert b"\xce" in gap  # Unicode comment bytes stay in the module BLOB gap
                assert gap not in [source[a:b] for _, a, b, _, _ in rows]
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

        # Resumption is transactionally visible after an observed progress line.
        resume_package = base / "resume-mathlib"
        (resume_package / "Mathlib").mkdir(parents=True)
        resume_files = []
        for number in range(1, 6):
            relative = f"Mathlib/Fixture{number}.lean"
            path = resume_package / relative
            path.write_text(
                f"import Lean\nnamespace Fixture{number}\n"
                f"theorem sample{number} (x : Nat) : x = x := by\n"
                "  exact rfl\n"
                f"end Fixture{number}\n",
                encoding="utf-8",
            )
            resume_files.append(relative)

        def interrupt_after_progress(output: Path) -> tuple[set[str], list[dict[str, object]]]:
            process = subprocess.Popen(
                [
                    "python3", "-B", str(BUILDER), "build",
                    "--mathlib-root", str(resume_package),
                    "--output", str(output), "--batch-size", "2", "--jobs", "2",
                    *resume_files,
                ],
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                bufsize=1,
            )
            progress: list[dict[str, object]] = []
            assert process.stderr is not None
            for line in process.stderr:
                payload = json.loads(line)
                progress.append(payload)
                if payload["event"] == "progress":
                    assert 0 < payload["completed_modules"] < len(resume_files)
                    assert payload["modules_per_second"] is not None
                    assert payload["eta_seconds"] is not None
                    process.send_signal(signal.SIGINT)
                    break
            process.wait(timeout=60)
            assert process.stdout is not None
            process.stdout.read()
            process.stderr.read()
            assert process.returncode == 130
            assert progress and progress[0]["event"] == "resume"
            assert not output.exists()
            partial = Path(f"{output}.partial")
            assert partial.exists()
            partial_connection = sqlite3.connect(partial)
            try:
                names = {
                    row[0] for row in partial_connection.execute("SELECT name FROM modules")
                }
            finally:
                partial_connection.close()
            assert 0 < len(names) < len(resume_files)
            return names, progress

        def logical_rows(path: Path, table: str) -> list[tuple[object, ...]]:
            connection = sqlite3.connect(path)
            try:
                return connection.execute(f"SELECT * FROM {table} ORDER BY 1, 2").fetchall()
            finally:
                connection.close()

        interrupted_output = base / "resumed.sqlite3"
        completed_names, _progress = interrupt_after_progress(interrupted_output)
        partial = Path(f"{interrupted_output}.partial")
        partial_db = sqlite3.connect(partial)
        assert partial_db.execute("PRAGMA foreign_key_check").fetchall() == []
        assert partial_db.execute("PRAGMA integrity_check").fetchone()[0] == "ok"
        assert partial_db.execute("SELECT count(*) FROM modules").fetchone()[0] == len(completed_names)
        assert {
            row[0] for row in partial_db.execute("SELECT name FROM modules")
        } == completed_names
        partial_db.close()

        resumed = run(
            "build", "--mathlib-root", str(resume_package), "--output", str(interrupted_output),
            "--batch-size", "2", "--jobs", "2", *resume_files,
        )
        assert resumed.returncode == 0, resumed.stderr
        resume_progress = [json.loads(line) for line in resumed.stderr.splitlines()]
        assert resume_progress[0]["event"] == "resume"
        assert resume_progress[0]["already_complete"] == len(completed_names)
        assert not partial.exists() and interrupted_output.exists()

        uninterrupted_output = base / "uninterrupted.sqlite3"
        uninterrupted = run(
            "build", "--mathlib-root", str(resume_package), "--output", str(uninterrupted_output),
            "--batch-size", "2", "--jobs", "2", *resume_files,
        )
        assert uninterrupted.returncode == 0, uninterrupted.stderr
        for table in ("modules", "imports", "commands"):
            assert logical_rows(interrupted_output, table) == logical_rows(uninterrupted_output, table)

        stale_output = base / "stale.sqlite3"
        stale_names, _ = interrupt_after_progress(stale_output)
        stale_module = sorted(stale_names)[0]
        stale_source = resume_package / Path(stale_module.replace(".", "/") + ".lean")
        original_source = stale_source.read_bytes()
        stale_source.write_bytes(original_source + b"\n-- source drift\n")
        stale = run(
            "build", "--mathlib-root", str(resume_package), "--output", str(stale_output),
            "--batch-size", "2", "--jobs", "2", *resume_files,
        )
        stale_source.write_bytes(original_source)
        assert stale.returncode != 0 and "partial source drift" in stale.stderr
        assert not stale_output.exists() and Path(f"{stale_output}.partial").exists()

        extra_output = base / "extra.sqlite3"
        interrupt_after_progress(extra_output)
        extra_partial = Path(f"{extra_output}.partial")
        extra_db = sqlite3.connect(extra_partial)
        extra_source = b"def extra := 1\n"
        extra_db.execute(
            "INSERT INTO modules(name,path,source,source_sha256) VALUES (?, ?, ?, ?)",
            ("Mathlib.Extra", "Mathlib/Extra.lean", extra_source, hashlib.sha256(extra_source).hexdigest()),
        )
        extra_db.commit()
        extra_db.close()
        extra = run(
            "build", "--mathlib-root", str(resume_package), "--output", str(extra_output),
            "--batch-size", "2", "--jobs", "2", *resume_files,
        )
        assert extra.returncode != 0 and "extra module" in extra.stderr
        assert not extra_output.exists()

        malformed_output = base / "malformed.sqlite3"
        malformed_names, _ = interrupt_after_progress(malformed_output)
        malformed_module = sorted(malformed_names)[0]
        malformed_partial = Path(f"{malformed_output}.partial")
        malformed_db = sqlite3.connect(malformed_partial)
        malformed_db.execute(
            "UPDATE commands SET source_sha256 = 'bad' WHERE module_name = ? AND ordinal = 0",
            (malformed_module,),
        )
        malformed_db.commit()
        malformed_db.close()
        malformed = run(
            "build", "--mathlib-root", str(resume_package), "--output", str(malformed_output),
            "--batch-size", "2", "--jobs", "2", *resume_files,
        )
        assert malformed.returncode != 0 and "slice hash mismatch" in malformed.stderr
        assert not malformed_output.exists()
        restarted = run(
            "build", "--discard-partial", "--mathlib-root", str(resume_package),
            "--output", str(malformed_output), "--batch-size", "2", "--jobs", "2", *resume_files,
        )
        assert restarted.returncode == 0, restarted.stderr
        assert malformed_output.exists() and not Path(f"{malformed_output}.partial").exists()

    # Exercise deterministic out-of-order completion and peer cancellation with
    # real process groups, without adding a production extractor special case.
    sys.path.insert(0, str(ROOT / "Experiment"))
    import source_command_db
    with tempfile.TemporaryDirectory(prefix="t61-source-command-workers-") as worker_name:
        worker_dir = Path(worker_name)
        worker = worker_dir / "worker.py"
        worker.write_text(
            "import json, sys, time\n"
            "from pathlib import Path\n"
            "path = sys.argv[1]\n"
            "stem = Path(path).stem\n"
            "if stem == 'fail':\n"
            "    print('not-json', flush=True)\n"
            "    raise SystemExit(1)\n"
            "if stem == 'slow':\n"
            "    time.sleep(1.0)\n"
            "elif stem == 'fast':\n"
            "    time.sleep(0.01)\n"
            "print(json.dumps({'path': path, 'imports': [], 'commands': []}), flush=True)\n",
            encoding="utf-8",
        )
        original_extractor_command = source_command_db._extractor_command
        source_command_db._extractor_command = lambda paths: [
            sys.executable, str(worker), *(str(path) for path in paths)
        ]
        try:
            source_command_db._CANCEL_REQUESTED.clear()
            completion_order: list[int] = []
            source_command_db._run_extraction_batches(
                [(1, [worker_dir / "slow.lean"]), (2, [worker_dir / "fast.lean"])],
                2,
                lambda batch, _paths, _records: completion_order.append(batch),
            )
            assert completion_order == [2, 1]
            assert not source_command_db._ACTIVE_PROCESSES

            source_command_db._CANCEL_REQUESTED.clear()
            started = time.monotonic()
            try:
                source_command_db._run_extraction_batches(
                    [(1, [worker_dir / "fail.lean"]), (2, [worker_dir / "slow.lean"])],
                    2,
                    lambda _batch, _paths, _records: None,
                )
            except RuntimeError as error:
                assert "malformed extractor output" in str(error)
            else:
                raise AssertionError("failed extractor batch was accepted")
            assert time.monotonic() - started < 3.0
            assert not source_command_db._ACTIVE_PROCESSES
        finally:
            source_command_db._CANCEL_REQUESTED.clear()
            source_command_db._extractor_command = original_extractor_command

    # The graph checker ignores external imports but rejects internal cycles.
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
