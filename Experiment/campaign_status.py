#!/usr/bin/env python3
"""Read compact campaign status without invoking Lean or changing the index."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sqlite3
from urllib.parse import quote

from boundary_materialize_shard import REPORT_SCHEMA

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DATABASE = ROOT / ".lake/search-free-mathlib/translation-index.sqlite3"


def snapshot(database: Path) -> dict[str, object]:
    campaign = json.loads((ROOT / "tracking/campaign.json").read_text())
    required_schema = max(REPORT_SCHEMA, campaign["coverage"]["minimumAcceptedReportSchema"])
    path = database.resolve()
    connection = sqlite3.connect(f"file:{quote(str(path))}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        connection.execute("BEGIN")
        module_count, unresolved = connection.execute(
            "SELECT COUNT(*),COALESCE(SUM(unresolved_count),0) FROM modules"
        ).fetchone()
        occurrence_count = connection.execute("SELECT COUNT(*) FROM occurrences").fetchone()[0]
        states = dict(connection.execute(
            "SELECT COALESCE(q.state,'unplanned'),COUNT(*) FROM modules m "
            "LEFT JOIN work_queue q ON q.module=m.module GROUP BY COALESCE(q.state,'unplanned')"
        ).fetchall())
        results = connection.execute(
            "SELECT m.module,r.artifact_ref,"
            "json_extract(r.result_json,'$.aggregate.materializeCount') AS calls,"
            "json_extract(r.result_json,'$.reportSchema') AS report_schema,"
            "json_extract(r.result_json,'$.modules[0].replayGuard.schema') AS replay_schema,"
            "json_extract(r.result_json,'$.modules[0].declarationOracle.replayGuard.schema') AS oracle_replay_schema "
            "FROM modules m JOIN work_queue q ON q.module=m.module "
            "JOIN result_cache r ON r.cache_key=q.cache_key "
            "WHERE q.state='succeeded' AND r.status='success' "
            "AND r.translation_status='verified_translated' "
            "AND r.source_hash=m.source_hash AND r.analysis_identity=m.analysis_identity "
            "ORDER BY m.module"
        ).fetchall()
        present = [row for row in results if row["artifact_ref"] and Path(row["artifact_ref"]).is_file()]
        validation_hold = campaign["coverage"].get("validationHold")
        guarded = [row for row in present if not validation_hold
                   and row["report_schema"] == required_schema
                   and row["replay_schema"] == 1 and row["oracle_replay_schema"] == 1]
        provisional = [row for row in present if row not in guarded]
        active = [dict(row) for row in connection.execute(
            "SELECT module,worker,lease_expires_at FROM work_queue WHERE state='running' ORDER BY module"
        )]
        failures = [dict(row) for row in connection.execute(
            "SELECT q.module,r.status,r.translation_status,r.failure,r.log_ref "
            "FROM work_queue q JOIN result_cache r ON r.cache_key=q.cache_key "
            "WHERE q.state='failed' OR r.translation_status='candidate_translated' "
            "ORDER BY q.module LIMIT 30"
        )]
        return {
            "updatedAt": datetime.now(timezone.utc).isoformat(),
            "database": str(path), "indexedModules": module_count,
            "indexedSourceCalls": occurrence_count, "unresolvedCalls": unresolved,
            "queueStates": states,
            "cachedVerifiedModules": len(guarded),
            "cachedVerifiedCalls": sum(int(row["calls"] or 0) for row in guarded),
            "provisionalCachedModules": len(provisional),
            "provisionalCachedCalls": sum(int(row["calls"] or 0) for row in provisional),
            "missingVerifiedReportFiles": len(results) - len(present),
            "verificationScope": (f"Acceptance on hold: {validation_hold} " if validation_hold else "") + f"Frozen per-module results against stock imports; not full translated-tree closure. Accepted counts require campaign report schema {required_schema} (implemented producer: {REPORT_SCHEMA}), including replay-error checks, declaration comparison and boundary state guards. Earlier cached results are provisional until revalidated. Report existence is checked here; full evidence integrity is checked by acceptance tooling.",
            "active": active, "failuresAndPartialResults": failures,
        }
    finally:
        connection.close()


def markdown(status: dict[str, object]) -> str:
    lines = [
        "# Search-free Mathlib campaign", "",
        f"Updated {status['updatedAt']}", "",
        f"- Indexed: {status['indexedSourceCalls']:,} calls in {status['indexedModules']:,} modules.",
        f"- Accepted per-module verification: {status['cachedVerifiedCalls']:,} translated calls in {status['cachedVerifiedModules']:,} modules.",
        f"- Provisional cache awaiting current semantic checks: {status['provisionalCachedCalls']:,} calls in {status['provisionalCachedModules']:,} modules.",
        f"- Unresolved source classifications: {status['unresolvedCalls']}.",
        f"- Missing cached report files: {status['missingVerifiedReportFiles']}.", "",
        str(status["verificationScope"]), "",
        "Queue: " + ", ".join(f"{key}={value}" for key, value in sorted(status["queueStates"].items())),
        "", "## Active modules", "",
    ]
    lines.extend(f"- `{row['module']}` ({row['worker']})" for row in status["active"])
    if not status["active"]:
        lines.append("No active module lease.")
    lines.extend(["", "## Failures and partial results", ""])
    for row in status["failuresAndPartialResults"]:
        detail = str(row["failure"] or row["translation_status"]).replace("\n", " ").replace("`", "'")
        lines.append(f"- `{row['module']}`: {detail}")
    if not status["failuresAndPartialResults"]:
        lines.append("None recorded for the current queue.")
    lines.extend(["", "Regenerate with `python3 Experiment/campaign_status.py --markdown`.", ""])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", type=Path, default=DEFAULT_DATABASE)
    parser.add_argument("--markdown", action="store_true")
    args = parser.parse_args()
    result = snapshot(args.database)
    print(markdown(result) if args.markdown else json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
