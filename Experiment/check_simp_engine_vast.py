#!/usr/bin/env python3
"""Check total Vast shard assignment, offer selection, and SSH parsing."""

from __future__ import annotations

import simp_engine_vast as vast
import simp_engine_vast_worker as worker


def offer(
    identifier: int,
    machine: int,
    price: float,
    cores: float,
    ghz: float,
    ram_mb: float = 128_000,
) -> dict:
    return {
        "id": identifier,
        "machine_id": machine,
        "dph_total": price,
        "cpu_cores_effective": cores,
        "cpu_ghz": ghz,
        "cpu_ram": ram_mb,
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
    selected = vast.select_offers(offers, 2, 0.20, 0.25, 120_000, 1)
    if {value["machine_id"] for value in selected} != {10, 11}:
        raise RuntimeError("Vast offer selection did not enforce unique machines")
    if sum(value["dph_total"] for value in selected) > 0.25:
        raise RuntimeError("Vast offer selection exceeded the price guard")
    under_memory = offer(5, 13, 0.01, 64, 5.0, 64_000)
    selected = vast.select_offers(
        offers + [under_memory], 2, 0.20, 0.25, 120_000, 1
    )
    if under_memory in selected:
        raise RuntimeError("Vast offer selection admitted an under-memory host")
    large_score = vast.offer_score(offer(6, 14, 0.10, 64, 4.0), 1)
    right_sized_score = vast.offer_score(offer(7, 15, 0.10, 4, 4.0), 1)
    if large_score != right_sized_score:
        raise RuntimeError("idle cores changed the single-process offer score")
    if vast.state_progress([
        {"completedShards": [1, 2], "failedShards": []},
        {"completedShards": [3], "failedShards": [4]},
    ]) != (3, 1):
        raise RuntimeError("Vast progress accounting changed")
    if vast.parse_ssh_url("ssh://root@example.test:12345") != ("example.test", 12345):
        raise RuntimeError("Vast SSH URL parsing changed")
    if vast.parse_jsonish("{'success': True}") != {"success": True}:
        raise RuntimeError("Vast legacy CLI response parsing changed")
    defaults = vast.parser().parse_args(["run", "--output-dir", "unused"])
    if defaults.concurrency != 1 or defaults.minimum_ram_gb_per_process != 120:
        raise RuntimeError("Vast memory-isolation defaults changed")
    print(
        "schema-16 Vast scheduler: 256 shards covered once; "
        "memory, host, progress, and price guards: ok"
    )


if __name__ == "__main__":
    main()
