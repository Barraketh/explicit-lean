#!/usr/bin/env python3
"""Read Codex rate-limit telemetry and enforce the campaign end time.

This only calls initialize and account/rateLimits/read; it never starts a model
turn, buys credits, or consumes a reset. Dispatch follows the account's actual
rate-limit availability rather than a project-specific percentage allowance.
Exit 0 permits a new bounded work batch; exit 3 means do not dispatch more work.
The backend remains the usage authority.
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


def _campaign_end(policy: dict[str, Any]) -> datetime:
    """Return the earliest explicit campaign deadline/not-after boundary."""
    if not isinstance(policy, dict):
        raise ValueError("campaign policy is not an object")
    ends = []
    for name in ("deadline", "notAfter"):
        value = policy.get(name)
        if value is None:
            continue
        if not isinstance(value, str):
            raise ValueError(f"{name} must be an ISO-8601 string")
        end = datetime.fromisoformat(value)
        if end.tzinfo is None:
            raise ValueError(f"{name} must include a timezone")
        ends.append(end)
    if not ends:
        raise ValueError("campaign deadline/not-after is missing")
    return min(ends)


def evaluate(policy: dict[str, Any], snapshot: dict[str, Any], now: datetime) -> dict[str, Any]:
    if now.tzinfo is None:
        raise ValueError("budget time must be timezone-aware")
    end = _campaign_end(policy)
    if now >= end:
        return {"decision": "deadline_reached", "canDispatch": False}
    ordinary_usage_allowed = snapshot.get("ordinaryUsageAllowed", True)
    if type(ordinary_usage_allowed) is not bool:
        raise ValueError("ordinaryUsageAllowed must be a boolean")
    if not ordinary_usage_allowed:
        return {"decision": "ordinary_usage_not_allowed", "canDispatch": False}
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
    if not 0 <= used <= 100 or resets <= now.timestamp():
        raise ValueError("weekly usage window is stale or invalid")
    short_limit = False
    for candidate in windows:
        if candidate is None or candidate is window:
            continue
        if not isinstance(candidate, dict):
            raise ValueError("rate-limit window is not an object")
        short_used = _integer(candidate.get("usedPercent"), "short-window usage")
        if not 0 <= short_used <= 100:
            raise ValueError("short-window usage is outside 0..100")
        short_limit = short_limit or short_used >= 100
    # Percentages are telemetry about the backend window, not a project cap.
    # Permit work until the account reports that the weekly or a short window
    # is exhausted; backend limit flags above remain authoritative as well.
    permit = used < 100 and not short_limit
    return {
        "decision": "continue" if permit else "wait_for_allowance",
        "canDispatch": permit,
        "window": "weekly",
        "usedPercent": used,
        "resetsAt": resets,
        "resetsAtUtc": datetime.fromtimestamp(resets, timezone.utc).isoformat(),
    }


def check() -> dict[str, Any]:
    now = datetime.now(timezone.utc)
    try:
        policy = json.loads(POLICY.read_text())
        if now >= _campaign_end(policy):
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
