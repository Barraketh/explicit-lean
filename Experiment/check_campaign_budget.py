#!/usr/bin/env python3
"""Exercise the authorization boundary without account access or model usage."""
from copy import deepcopy
from datetime import datetime, timezone

from campaign_budget import evaluate

RESET = int(datetime(2026, 9, 7, 7, tzinfo=timezone.utc).timestamp())
NOW = datetime(2026, 9, 1, tzinfo=timezone.utc)
POLICY = {"deadline": "2026-09-08T00:00:00-07:00", "budget": {
    "initialWindowResetsAt": RESET, "nextWindowMaximumPercent": 25,
    "nextWindowDispatchStopPercent": 22,
}}


def snapshot(used=1, resets=RESET):
    return {"rateLimits": {"limitId": "codex", "primary": {
        "windowDurationMins": 10080, "usedPercent": used, "resetsAt": resets,
    }}}


def main():
    assert evaluate(POLICY, snapshot(98), NOW)["canDispatch"]
    assert not evaluate(POLICY, snapshot(99), NOW)["canDispatch"]
    following = RESET + 7 * 86400
    for percent in [0, 18, 19, 21]:
        result = evaluate(POLICY, snapshot(percent, following), NOW)
        assert result["canDispatch"] and result["window"] == "next_limited"
        assert result["maximumNewAgents"] == (1 if percent >= 19 else 3)
    for percent in [22, 24, 25, 99, 100]:
        assert not evaluate(POLICY, snapshot(percent, following), NOW)["canDispatch"]
    assert evaluate(POLICY, {}, datetime(2026, 9, 9, tzinfo=timezone.utc))["decision"] == "deadline_reached"
    reached = snapshot()
    reached["rateLimits"]["spendControlReached"] = True
    assert not evaluate(POLICY, reached, NOW)["canDispatch"]
    keyed = snapshot(1)
    keyed["rateLimitsByLimitId"] = {"codex": snapshot(25, following)["rateLimits"]}
    assert not evaluate(POLICY, keyed, NOW)["canDispatch"]
    short = snapshot()
    short["rateLimits"]["secondary"] = {"usedPercent": 100, "windowDurationMins": 300}
    assert not evaluate(POLICY, short, NOW)["canDispatch"]
    for mutation in [
        lambda x: x["rateLimits"].update(limitId="other"),
        lambda x: x["rateLimits"]["primary"].update(usedPercent=True),
        lambda x: x["rateLimits"]["primary"].update(usedPercent=-1),
        lambda x: x["rateLimits"]["primary"].update(usedPercent=101),
        lambda x: x["rateLimits"]["primary"].update(resetsAt=0),
        lambda x: x["rateLimits"]["primary"].update(windowDurationMins=300),
        lambda x: x["rateLimits"].update(secondary=deepcopy(x["rateLimits"]["primary"])),
    ]:
        malformed = snapshot()
        mutation(malformed)
        try:
            evaluate(POLICY, malformed, NOW)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted malformed usage: {malformed}")
    print("campaign budget: reset boundaries, cap, headroom, stale/missing data and backend limits: ok")


if __name__ == "__main__":
    main()
