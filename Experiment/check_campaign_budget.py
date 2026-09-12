#!/usr/bin/env python3
"""Exercise the authorization boundary without account access or model usage."""
from copy import deepcopy
from datetime import datetime, timezone

from campaign_budget import _campaign_end, _parse_iso8601, evaluate

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
    zulu = "2026-09-08T00:00:00Z"
    assert _parse_iso8601(zulu) == datetime(2026, 9, 8, tzinfo=timezone.utc)
    assert _campaign_end({"deadline": zulu}) == datetime(2026, 9, 8, tzinfo=timezone.utc)
    assert evaluate({"deadline": zulu}, snapshot(1), NOW)["canDispatch"]
    # The legacy percentage fields are intentionally ignored. Account
    # availability, not the former 25% project allowance, controls dispatch.
    for percent in [0, 18, 22, 24, 25, 98, 99]:
        result = evaluate(POLICY, snapshot(percent), NOW)
        assert result["canDispatch"] and result["window"] == "weekly"
        assert "dispatchStopPercent" not in result
        assert "maximumNewAgents" not in result
    assert not evaluate(POLICY, snapshot(100), NOW)["canDispatch"]
    following = RESET + 7 * 86400
    for percent in [0, 18, 22, 24, 25, 99]:
        result = evaluate(POLICY, snapshot(percent, following), NOW)
        assert result["canDispatch"] and result["window"] == "weekly"
    for percent in [100]:
        assert not evaluate(POLICY, snapshot(percent, following), NOW)["canDispatch"]
    # A policy with no legacy budget block remains valid; its explicit deadline
    # is still required and still gates dispatch.
    assert evaluate({"deadline": POLICY["deadline"]}, snapshot(99), NOW)["canDispatch"]
    allowed = snapshot(99)
    allowed["ordinaryUsageAllowed"] = True
    assert evaluate(POLICY, allowed, NOW)["canDispatch"]
    denied = snapshot(1)
    denied["ordinaryUsageAllowed"] = False
    assert evaluate(POLICY, denied, NOW) == {
        "decision": "ordinary_usage_not_allowed", "canDispatch": False}
    assert evaluate(POLICY, {"ordinaryUsageAllowed": False}, NOW)["decision"] == \
        "ordinary_usage_not_allowed"
    assert evaluate({"deadline": "2026-09-10T00:00:00Z",
                     "notAfter": "2026-09-02T00:00:00Z"},
                    snapshot(99), NOW)["canDispatch"]
    assert evaluate({"deadline": "2026-09-01T00:00:00Z",
                     "notAfter": "2026-09-10T00:00:00Z"},
                    {}, NOW)["decision"] == "deadline_reached"
    assert evaluate(POLICY, {}, datetime(2026, 9, 9, tzinfo=timezone.utc))["decision"] == "deadline_reached"
    reached = snapshot()
    reached["rateLimits"]["spendControlReached"] = True
    assert not evaluate(POLICY, reached, NOW)["canDispatch"]
    keyed = snapshot(1)
    keyed["rateLimitsByLimitId"] = {"codex": snapshot(99, following)["rateLimits"]}
    assert evaluate(POLICY, keyed, NOW)["canDispatch"]
    short = snapshot()
    short["rateLimits"]["secondary"] = {"usedPercent": 99, "windowDurationMins": 300}
    assert evaluate(POLICY, short, NOW)["canDispatch"]
    short["rateLimits"]["secondary"]["usedPercent"] = 100
    assert not evaluate(POLICY, short, NOW)["canDispatch"]
    for mutation in [
        lambda x: x["rateLimits"].update(limitId="other"),
        lambda x: x["rateLimits"]["primary"].update(usedPercent=True),
        lambda x: x["rateLimits"]["primary"].update(usedPercent=-1),
        lambda x: x["rateLimits"]["primary"].update(usedPercent=101),
        lambda x: x["rateLimits"]["primary"].update(resetsAt=0),
        lambda x: x["rateLimits"]["primary"].update(windowDurationMins=300),
        lambda x: x["rateLimits"].update(secondary=deepcopy(x["rateLimits"]["primary"])),
        lambda x: x["rateLimits"].update(secondary={"usedPercent": -1, "windowDurationMins": 300}),
        lambda x: x.update(ordinaryUsageAllowed="false"),
    ]:
        malformed = snapshot()
        mutation(malformed)
        try:
            evaluate(POLICY, malformed, NOW)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted malformed usage: {malformed}")
    print("campaign budget: deadline, account availability, stale/missing data and backend limits: ok")


if __name__ == "__main__":
    main()
