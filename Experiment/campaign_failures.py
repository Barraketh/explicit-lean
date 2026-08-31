#!/usr/bin/env python3
"""Group current cached failures by observed diagnostics, without running Lean.

Families are triage hints, not established root causes or acceptance decisions.
The implementation identity and log hash keep old-runtime failures distinct
from current implementation evidence.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sqlite3
from urllib.parse import quote

from campaign_status import DEFAULT_DATABASE


def classify(text: str) -> str:
    for needle, family in (
        ("non-private declaration name set differs", "declaration_names"),
        ("declaration_type_mismatch", "declaration_types"),
        ("boundary_expr_unresolved_universe", "unresolved_universes"),
        ("unpaired_fresh_expression_mvar", "fresh_expression_variables"),
        ("unpaired_fresh_constant", "fresh_constants"),
        ("expression constant is unavailable without generation", "missing_replay_constants"),
        ("boundary_matcher_unsupported_extra_declaration", "matcher_extra_declarations"),
        ("Lean.backwardDefeqAttr", "backward_defeq_tags"),
    ):
        if needle in text:
            return family
    codes = re.findall(r"\b(boundary_[a-z_]+|declaration_[a-z_]+|environment_delta_mismatch):", text)
    return codes[-1] if codes else "unclassified"


def snapshot(database: Path) -> dict[str, object]:
    path = database.resolve()
    connection = sqlite3.connect(f"file:{quote(str(path))}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        connection.execute("BEGIN")
        rows = connection.execute(
            "SELECT q.module,r.implementation_identity,r.failure,r.log_ref,"
            "(SELECT COUNT(*) FROM occurrences o WHERE o.module=q.module) AS source_calls "
            "FROM work_queue q JOIN modules m ON m.module=q.module "
            "JOIN result_cache r ON r.cache_key=q.cache_key "
            "WHERE q.state='failed' AND r.source_hash=m.source_hash "
            "AND r.analysis_identity=m.analysis_identity ORDER BY q.module"
        ).fetchall()
        failures = []
        for row in rows:
            log = Path(row["log_ref"]) if row["log_ref"] else None
            try:
                data = log.read_bytes() if log is not None else None
            except OSError:
                data = None
            text = data.decode("utf-8", errors="replace") if data is not None else str(row["failure"] or "")
            diagnostics = [line for line in text.splitlines()
                           if "boundary materialization shard failed:" in line]
            detail = diagnostics[-1] if diagnostics else text[-1500:]
            failures.append({
                "module": row["module"], "sourceCalls": row["source_calls"],
                "family": classify(detail), "detail": detail[:1500],
                "implementationIdentity": row["implementation_identity"],
                "log": str(log) if log is not None else None,
                "logSha256": hashlib.sha256(data).hexdigest() if data is not None else None,
                "logAvailable": data is not None,
            })
        counts = Counter(row["family"] for row in failures)
        return {
            "updatedAt": datetime.now(timezone.utc).isoformat(),
            "database": str(path), "failedModules": len(failures),
            "families": [{"family": family, "modules": count,
                          "sourceCalls": sum(row["sourceCalls"] for row in failures if row["family"] == family)}
                         for family, count in sorted(counts.items(), key=lambda item: (-item[1], item[0]))],
            "failures": failures,
            "limitation": "Diagnostic grouping only. Different implementation identities need separate reproduction; source-call totals are not counts of failing calls.",
        }
    finally:
        connection.close()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", type=Path, default=DEFAULT_DATABASE)
    args = parser.parse_args()
    print(json.dumps(snapshot(args.database), indent=2))


if __name__ == "__main__":
    main()
