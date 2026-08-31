#!/usr/bin/env python3
"""Read Codex allowance telemetry and apply the user's campaign spend policy.

This only calls initialize and account/rateLimits/read; it never starts a model
turn, buys credits, or consumes a reset. Exit 0 permits a new bounded work batch;
exit 3 means do not dispatch more work. The backend remains the usage authority.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import select
import subprocess
import tempfile
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
POLICY = ROOT / "tracking/campaign.json"
STATE = ROOT / ".lake/search-free-mathlib/budget-state.json"


def read_account_limits(timeout: float = 25) -> dict[str, Any]:
    """Use a short-lived local protocol process with the existing login."""
    with tempfile.TemporaryFile() as stderr:
        process = subprocess.Popen(
            ["codex", "app-server", "--stdio"], cwd=ROOT,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=stderr,
        )
        assert process.stdin is not None and process.stdout is not None
        buffered = b""
        deadline = time.monotonic() + timeout

        def send(value: dict[str, Any]) -> None:
            process.stdin.write((json.dumps(value) + "\n").encode())
            process.stdin.flush()

        def receive(identifier: int) -> dict[str, Any]:
            nonlocal buffered
            while time.monotonic() < deadline:
                while b"\n" in buffered:
                    line, buffered = buffered.split(b"\n", 1)
                    if not line:
                        continue
                    message = json.loads(line)
                    if message.get("id") != identifier:
                        continue
                    if "error" in message:
                        raise RuntimeError("account usage request was rejected")
                    result = message.get("result")
                    if not isinstance(result, dict):
                        raise RuntimeError("account usage response is not an object")
                    return result
                remaining = max(0, deadline - time.monotonic())
                ready, _, _ = select.select([process.stdout], [], [], remaining)
                if ready:
                    chunk = os.read(process.stdout.fileno(), 65536)
                    if not chunk:
                        raise RuntimeError("local account usage connection closed")
                    buffered += chunk
                    if len(buffered) > 2_000_000:
                        raise RuntimeError("account usage response exceeds limit")
            raise TimeoutError("account usage request timed out")

        try:
            send({"id": 1, "method": "initialize", "params": {
                "clientInfo": {"name": "explicit_lean_budget", "version": "1"}
            }})
            receive(1)
            send({"method": "initialized"})
            send({"id": 2, "method": "account/rateLimits/read"})
            return receive(2)
        finally:
            process.terminate()
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()


def _integer(value: object, label: str) -> int:
    if type(value) is not int:
        raise ValueError(f"{label} must be an integer")
    return value


def evaluate(policy: dict[str, Any], snapshot: dict[str, Any], now: datetime) -> dict[str, Any]:
    if now.tzinfo is None:
        raise ValueError("budget time must be timezone-aware")
    end = datetime.fromisoformat(policy["deadline"])
    if now >= end:
        return {"decision": "deadline_reached", "canDispatch": False}
    budget = policy["budget"]
    initial_reset = _integer(budget["initialWindowResetsAt"], "initial reset")
    maximum = _integer(budget["nextWindowMaximumPercent"], "maximum percent")
    stop = _integer(budget["nextWindowDispatchStopPercent"], "dispatch stop")
    if not 0 < stop < maximum <= 25:
        raise ValueError("next-window policy must preserve headroom below the 25% cap")
    keyed = snapshot.get("rateLimitsByLimitId")
    rate = keyed.get("codex") if isinstance(keyed, dict) else None
    if rate is None:
        rate = snapshot.get("rateLimits")
    if not isinstance(rate, dict) or rate.get("limitId") != "codex":
        raise ValueError("no unambiguous codex allowance bucket")
    if rate.get("spendControlReached") or rate.get("rateLimitReachedType"):
        return {"decision": "backend_limit_reached", "canDispatch": False}
    windows = [rate.get(name) for name in ("primary", "secondary")]
    weekly = [window for window in windows if isinstance(window, dict)
              and window.get("windowDurationMins") == 10080]
    if len(weekly) != 1:
        raise ValueError("expected exactly one weekly Codex allowance window")
    window = weekly[0]
    used = _integer(window.get("usedPercent"), "used percent")
    resets = _integer(window.get("resetsAt"), "reset timestamp")
    if not 0 <= used <= 100 or resets <= now.timestamp() or resets < initial_reset:
        raise ValueError("weekly usage window is stale or invalid")
    # A changed reset boundary is treated as the limited window even if it
    # arrives earlier than expected. The campaign never authorizes extra resets.
    next_window = resets > initial_reset or now.timestamp() >= initial_reset
    threshold = stop if next_window else 99
    short_limit = any(
        isinstance(window, dict) and window.get("windowDurationMins") != 10080
        and _integer(window.get("usedPercent"), "short-window usage") >= 99
        for window in windows if window is not None
    )
    permit = used < threshold and not short_limit
    return {
        "decision": "continue" if permit else "wait_for_allowance",
        "canDispatch": permit,
        "window": "next_limited" if next_window else "current",
        "usedPercent": used,
        "dispatchStopPercent": threshold,
        "userMaximumPercent": maximum if next_window else 100,
        "resetsAt": resets,
        "resetsAtUtc": datetime.fromtimestamp(resets, timezone.utc).isoformat(),
        "smallBatchesOnly": next_window and used >= stop - 3,
        "maximumNewAgents": 1 if next_window and used >= stop - 3 else 3,
    }


def check() -> dict[str, Any]:
    now = datetime.now(timezone.utc)
    try:
        policy = json.loads(POLICY.read_text())
        if now >= datetime.fromisoformat(policy["deadline"]):
            result = {"decision": "deadline_reached", "canDispatch": False}
        else:
            result = evaluate(policy, read_account_limits(), now)
    except (OSError, ValueError, KeyError, TypeError, RuntimeError, TimeoutError) as error:
        result = {"decision": "unknown_usage", "canDispatch": False,
                  "detail": str(error)[:300]}
    result["checkedAt"] = now.isoformat()
    STATE.parent.mkdir(parents=True, exist_ok=True)
    # This is a current diagnostic snapshot, never an authorization override.
    with tempfile.NamedTemporaryFile(mode="w", dir=STATE.parent, delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(result, stream, indent=2)
        stream.write("\n")
    try:
        temporary.replace(STATE)
    finally:
        temporary.unlink(missing_ok=True)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check"])
    parser.parse_args()
    result = check()
    print(json.dumps(result, indent=2))
    return 0 if result["canDispatch"] else 3


if __name__ == "__main__":
    raise SystemExit(main())
