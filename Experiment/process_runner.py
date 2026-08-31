"""POSIX subprocess runner whose timeout also stops launcher descendants."""

from __future__ import annotations

import os
import signal
import subprocess
from typing import Any


def run_process(
    *popenargs: Any,
    input: Any = None,
    capture_output: bool = False,
    timeout: float | None = None,
    check: bool = False,
    **kwargs: Any,
) -> subprocess.CompletedProcess[Any]:
    """Run like ``subprocess.run``, owning a fresh POSIX session.

    On timeout or interrupted communication, kill the whole process group and
    reap the immediate child before raising. Descendants inherit the group;
    deliberately detached sessions/groups are outside this contract. Orphaned
    descendants are reaped by the OS, since they are not this process's children.
    Preserve POSIX TimeoutExpired's partial byte output, even in text mode.

    Session/group options are reserved so callers cannot accidentally target
    their own process group during cleanup.
    """
    if os.name != "posix":
        raise RuntimeError("run_process requires POSIX process groups")
    if "start_new_session" in kwargs or "process_group" in kwargs:
        raise ValueError("run_process owns the child session and process group")
    if input is not None:
        if kwargs.get("stdin") is not None:
            raise ValueError("stdin and input arguments may not both be used")
        kwargs["stdin"] = subprocess.PIPE
    if capture_output:
        if kwargs.get("stdout") is not None or kwargs.get("stderr") is not None:
            raise ValueError("stdout and stderr may not be used with capture_output")
        kwargs["stdout"] = subprocess.PIPE
        kwargs["stderr"] = subprocess.PIPE

    with subprocess.Popen(*popenargs, start_new_session=True, **kwargs) as process:
        try:
            stdout, stderr = process.communicate(input, timeout=timeout)
        except BaseException:
            # Kill even if the launcher exited: descendants can still be alive
            # and holding its output pipes open. Do not gate this on poll().
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            raise
        returncode = process.poll()
        if check and returncode:
            raise subprocess.CalledProcessError(
                returncode, process.args, output=stdout, stderr=stderr
            )
        return subprocess.CompletedProcess(process.args, returncode, stdout, stderr)
