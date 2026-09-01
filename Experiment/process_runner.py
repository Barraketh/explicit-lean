"""POSIX subprocess runner whose timeout also stops launcher descendants."""

from __future__ import annotations

import os
import signal
import subprocess
import time
from typing import Any, Callable


class ProcessResourceLimitExceeded(RuntimeError):
    """A caller-supplied resource guard stopped a process group."""

    def __init__(
        self, cmd: Any, detail: str, stdout: Any = None, stderr: Any = None,
    ) -> None:
        super().__init__(detail)
        self.cmd = cmd
        self.detail = detail
        self.stdout = stdout
        self.stderr = stderr


def run_process(
    *popenargs: Any,
    input: Any = None,
    capture_output: bool = False,
    timeout: float | None = None,
    check: bool = False,
    resource_guard: Callable[[int], str | None] | None = None,
    resource_poll_interval: float = 1.0,
    **kwargs: Any,
) -> subprocess.CompletedProcess[Any]:
    """Run like ``subprocess.run``, owning a fresh POSIX session.

    On timeout or interrupted communication, interrupt the process group first
    so a Python launcher using this runner can clean up its own child group.
    After a short grace period, unconditionally kill the group and reap the
    immediate child before raising. Descendants normally inherit the group;
    detached processes that do not cooperate with interruption are outside this
    contract. Orphaned descendants are reaped by the OS.
    Preserve POSIX TimeoutExpired's partial byte output, even in text mode.

    When ``resource_guard`` is supplied, poll it with the owned session leader
    PID. A nonempty failure detail interrupts and then kills the same process
    group, captures its final output, and raises
    ``ProcessResourceLimitExceeded``. The callback may observe host-wide state;
    this is how an outer campaign worker can stop nested runners that own their
    own descendant groups.

    Session/group options are reserved so callers cannot accidentally target
    their own process group during cleanup.
    """
    if os.name != "posix":
        raise RuntimeError("run_process requires POSIX process groups")
    if "start_new_session" in kwargs or "process_group" in kwargs:
        raise ValueError("run_process owns the child session and process group")
    if resource_poll_interval <= 0:
        raise ValueError("resource poll interval must be positive")
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
            if resource_guard is None:
                stdout, stderr = process.communicate(input, timeout=timeout)
            else:
                deadline = None if timeout is None else time.monotonic() + timeout
                pending_input = input
                while True:
                    detail = resource_guard(process.pid)
                    if detail is not None:
                        raise ProcessResourceLimitExceeded(process.args, detail)
                    wait = resource_poll_interval
                    if deadline is not None:
                        remaining = deadline - time.monotonic()
                        if remaining <= 0:
                            raise subprocess.TimeoutExpired(process.args, timeout)
                        wait = min(wait, remaining)
                    try:
                        stdout, stderr = process.communicate(pending_input, timeout=wait)
                        break
                    except subprocess.TimeoutExpired as error:
                        pending_input = None
                        if deadline is not None and time.monotonic() >= deadline:
                            raise subprocess.TimeoutExpired(
                                process.args, timeout, output=error.stdout,
                                stderr=error.stderr,
                            )
        except BaseException as error:
            # Nested users own separate groups. SIGKILL alone would kill their
            # Python wrapper before its exception handler can stop its compiler.
            # SIGINT raises KeyboardInterrupt in those wrappers, unwinding the
            # same cleanup path recursively. The hard-kill fallback still bounds
            # non-cooperative commands in the group we own.
            try:
                try:
                    os.killpg(process.pid, signal.SIGINT)
                except ProcessLookupError:
                    pass
                try:
                    process.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    pass
            finally:
                # Kill even if the launcher exited: descendants can still hold
                # its output pipes. A second interrupt must not skip this step.
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
            if isinstance(error, ProcessResourceLimitExceeded):
                # The process and every pipe-holding descendant are gone, so
                # collect the complete diagnostic stream before propagating
                # the distinct resource failure to the campaign worker.
                error.stdout, error.stderr = process.communicate()
            raise
        returncode = process.poll()
        if check and returncode:
            raise subprocess.CalledProcessError(
                returncode, process.args, output=stdout, stderr=stderr
            )
        return subprocess.CompletedProcess(process.args, returncode, stdout, stderr)
