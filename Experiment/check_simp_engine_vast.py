#!/usr/bin/env python3
"""Check total Vast shard assignment, offer selection, and SSH parsing."""

from __future__ import annotations

import simp_engine_vast as vast
import simp_engine_vast_worker as worker


def offer(identifier: int, machine: int, price: float, cores: float, ghz: float) -> dict:
    return {
        "id": identifier,
        "machine_id": machine,
        "dph_total": price,
        "cpu_cores_effective": cores,
        "cpu_ghz": ghz,
    }


def main() -> None:
    assignments = [
        shard
        for index in range(16)
        for shard in worker.assigned_shards(index, 16, 256)
    ]
    if sorted(assignments) != list(range(256)) or len(assignments) != len(set(assignments)):
        raise RuntimeError("Vast workers do not cover every shard exactly once")
    offers = [
        offer(1, 10, 0.10, 16, 3.0),
        offer(2, 10, 0.08, 16, 4.0),
        offer(3, 11, 0.12, 24, 3.2),
        offer(4, 12, 0.30, 32, 4.0),
    ]
    selected = vast.select_offers(offers, 2, 0.20, 0.25)
    if {value["machine_id"] for value in selected} != {10, 11}:
        raise RuntimeError("Vast offer selection did not enforce unique machines")
    if sum(value["dph_total"] for value in selected) > 0.25:
        raise RuntimeError("Vast offer selection exceeded the price guard")
    if vast.parse_ssh_url("ssh://root@example.test:12345") != ("example.test", 12345):
        raise RuntimeError("Vast SSH URL parsing changed")
    if vast.parse_jsonish("{'success': True}") != {"success": True}:
        raise RuntimeError("Vast legacy CLI response parsing changed")
    print("schema-16 Vast scheduler: 256 shards covered once, host and price guards: ok")


if __name__ == "__main__":
    main()
