#!/usr/bin/env python3
"""Check command compatibility and real descendant cleanup without Lean builds."""

from __future__ import annotations

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

import boundary_materialize_shard as shard
import check_simp_engine_boundary_scope as scope
import check_simp_engine_boundary_source as source
import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as inventory
from process_runner import run_process


TREE_SCRIPT = """
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

root = Path(sys.argv[1])
role = sys.argv[2]
exit_root = sys.argv[3] == 'exit'
signal.signal(signal.SIGTERM, signal.SIG_IGN)
record = {'role': role, 'pid': os.getpid(), 'group': os.getpgrp()}
(root / (role + '.json')).write_text(json.dumps(record))
print(json.dumps(record), flush=True)
print(role + '-stderr', file=sys.stderr, flush=True)
if role != 'grandchild':
    next_role = 'child' if role == 'root' else 'grandchild'
    child = subprocess.Popen([sys.executable, __file__, str(root), next_role, sys.argv[3]])
    if role == 'root' and exit_root:
        sys.exit(0)
    child.wait()
else:
    # A surviving grandchild would keep changing this artifact after timeout.
    with (root / 'heartbeat').open('ab', buffering=0) as stream:
        until = time.monotonic() + 30
        while time.monotonic() < until:
            stream.write(b'.')
            time.sleep(0.02)
"""


def python_command(code: str) -> list[str]:
    return [sys.executable, "-c", code]


def test_completed_process_contract(root: Path) -> None:
    command = python_command(
        "import os,sys; print(os.getcwd()); print(os.environ['RUNNER_TEST']); "
        "print(sys.stdin.read()); print('diagnostic', file=sys.stderr); sys.exit(7)"
    )
    options = dict(
        cwd=root,
        env={**os.environ, "RUNNER_TEST": "environment preserved"},
        input="input preserved",
        capture_output=True,
        text=True,
        timeout=5,
    )
    expected = subprocess.run(command, **options)
    actual = run_process(command, **options)
    assert vars(actual) == vars(expected)
    try:
        run_process(command, check=True, **options)
    except subprocess.CalledProcessError as error:
        assert (error.cmd, error.returncode, error.stdout, error.stderr) == (
            command, expected.returncode, expected.stdout, expected.stderr
        )
    else:
        raise AssertionError("check=True accepted a failing command")
    binary = run_process(
        python_command("import sys; sys.stdout.buffer.write(sys.stdin.buffer.read())"),
        input=b"\x00\xff\n",
        capture_output=True,
        timeout=5,
    )
    assert (binary.returncode, binary.stdout, binary.stderr) == (0, b"\x00\xff\n", b"")
    signalled = run_process(
        python_command("import os,signal; os.kill(os.getpid(), signal.SIGTERM)"),
        timeout=5,
    )
    assert signalled.returncode == -signal.SIGTERM


def test_descendant_timeout(root: Path, *, exit_root: bool) -> None:
    root.mkdir()
    script = root / "tree.py"
    script.write_text(TREE_SCRIPT)
    command = [sys.executable, str(script), str(root), "root", "exit" if exit_root else "wait"]
    try:
        started = time.monotonic()
        try:
            run_process(command, timeout=1, capture_output=True, text=True)
        except subprocess.TimeoutExpired as error:
            assert error.cmd == command and error.timeout == 1
            assert isinstance(error.stdout, bytes) and isinstance(error.stderr, bytes)
            records = [json.loads(line) for line in error.stdout.splitlines()]
            assert {item["role"] for item in records} == {"root", "child", "grandchild"}
            assert set(error.stderr.splitlines()) == {
                b"root-stderr", b"child-stderr", b"grandchild-stderr"
            }
        else:
            raise AssertionError("descendant tree did not time out")
        assert time.monotonic() - started < 5, "timeout cleanup blocked on a descendant"
        root_pid = next(item["pid"] for item in records if item["role"] == "root")
        assert all(item["group"] == root_pid for item in records)
        assert root_pid != os.getpgrp()

        # The runner must reap its direct child. The OS adopts/reaps descendants;
        # a transient zombie is dead, but a live orphan is a regression.
        try:
            os.waitpid(root_pid, os.WNOHANG)
        except ChildProcessError:
            pass
        else:
            raise AssertionError("runner did not reap its immediate child")
        pids = ",".join(str(item["pid"]) for item in records)
        deadline = time.monotonic() + 2
        while True:
            states = subprocess.run(
                ["ps", "-o", "pid=,stat=", "-p", pids],
                capture_output=True, text=True, timeout=5,
            )
            assert states.returncode in (0, 1), states.stderr
            alive = [line for line in states.stdout.splitlines() if not line.split()[1].startswith("Z")]
            if not alive or time.monotonic() >= deadline:
                break
            time.sleep(0.02)
        assert not alive, f"running orphan(s) after timeout: {alive}"
        heartbeat = (root / "heartbeat").read_bytes()
        assert heartbeat
        time.sleep(0.1)
        assert (root / "heartbeat").read_bytes() == heartbeat, "orphan kept writing"
    finally:
        # Also clean up if the regression fails, without hiding the failure.
        record_path = root / "root.json"
        if record_path.exists():
            group = json.loads(record_path.read_text())["group"]
            if group != os.getpgrp():
                try:
                    os.killpg(group, signal.SIGKILL)
                except ProcessLookupError:
                    pass


def test_production_adapters(root: Path) -> None:
    output = "out\nerr\n"
    body = "import sys; print('out', flush=True); print('err', file=sys.stderr, flush=True)"
    success = python_command(body)
    failure = python_command(body + "; sys.exit(7)")
    for run in (inventory.run, shard._run_command):
        for command, expected_code in ((success, 0), (failure, 7)):
            code, captured, elapsed = run(command, timeout=5)
            assert (code, captured) == (expected_code, output) and elapsed >= 0
    for run in (scope.run, source.run):
        assert run(success, timeout=5) == output
        try:
            run(failure, timeout=5)
        except RuntimeError as error:
            assert str(error) == output
        else:
            raise AssertionError("adapter accepted a failing command")

    timeout_command = python_command(body + "; import time; time.sleep(30)")
    for run in (inventory.run, shard._run_command):
        code, captured, _elapsed = run(timeout_command, timeout=0.5)
        assert code == 124
        assert captured == output + "\nexplicit-lean: compilation timed out\n"
    for run in (scope.run, source.run):
        try:
            run(timeout_command, timeout=0.5)
        except subprocess.TimeoutExpired as error:
            assert error.cmd == timeout_command
            assert error.stdout == output.encode() and error.stderr is None
        else:
            raise AssertionError("adapter swallowed TimeoutExpired")

    # Exercise the fixed inventory launcher path without starting Lean or Lake.
    launcher = root / "Experiment" / "lean_toolchain_cache.py"
    launcher.parent.mkdir()
    launcher.write_text(
        "import json,os,sys\n"
        "assert sys.argv[1] == 'inventory'\n"
        "assert os.getpid() == os.getsid(0)\n"
        "print(json.dumps({'source': 'simp'}))\n"
        "print('SIMP_ENGINE_INVENTORY_FULL_FALLBACK file=' + sys.argv[2])\n"
        "print('separate diagnostic', file=sys.stderr)\n"
    )
    original_root = corpus.ROOT
    corpus.ROOT = root
    try:
        path = root / "Input.lean"
        assert corpus.inventory_batch([path], timeout=5) == ([{"source": "simp"}], [str(path)])
    finally:
        corpus.ROOT = original_root
    assert "Experiment/process_runner.py" in corpus.implementation_hashes()


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="process-runner-") as raw:
        root = Path(raw).resolve()
        test_completed_process_contract(root)
        test_descendant_timeout(root / "live-launcher", exit_root=False)
        test_descendant_timeout(root / "exited-launcher", exit_root=True)
        test_production_adapters(root)
    print("process runner: compatibility, adapters, and child/grandchild timeout checks passed")


if __name__ == "__main__":
    main()
