#!/usr/bin/env python3
"""Import recovered Erdős attempts with one pinned producer source per event.

The generic Vela importer accepts one ``--source-ref`` for an import batch.
Recovered work spans several repositories, commits, and paths, so this wrapper
partitions the reviewed ledger into single-record batches.  It never creates a
signing key: ``--apply`` still requires ``VELA_AGENT_KEY_HEX`` to be present,
exactly as the underlying command does.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
from pathlib import Path
from typing import Any

import yaml


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEDGER = ROOT / "sources" / "recovered-attempt-ledger.v2.json"
DEFAULT_MAPPING = ROOT / "sources" / "recovered-attempt-import-map.yaml"
DEFAULT_SOURCES = ROOT / "sources" / "recovered-attempts.yaml"
ACTOR = "agent:erdos-history-import"


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected an object")
    return value


def load_yaml(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        value = yaml.safe_load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected an object")
    return value


def source_ref(record: dict[str, Any]) -> str:
    source = record["source"]
    return f"{source['repository']}@{source['commit']}:{source['path']}"


def import_batches(
    ledger_path: Path, mapping_path: Path, sources_path: Path
) -> list[tuple[dict[str, Any], dict[str, Any], str]]:
    ledger = load_json(ledger_path)
    mapping = load_yaml(mapping_path)
    sources = load_yaml(sources_path)

    attempts = ledger.get("records")
    mappings = mapping.get("mappings")
    records = sources.get("records")
    if not isinstance(attempts, list) or not isinstance(mappings, list):
        raise ValueError("recovered ledger or mapping has an invalid records list")
    if not isinstance(records, list):
        raise ValueError("recovered source manifest has an invalid records list")

    source_by_legacy_id = {
        record["record_id"]: record
        for record in records
        if record.get("classification") == "importable_attempt"
    }
    mapping_by_attempt_id = {entry["attempt_id"]: entry for entry in mappings}
    if len(source_by_legacy_id) != len(attempts):
        raise ValueError("importable source records do not match recovered ledger rows")
    if len(mapping_by_attempt_id) != len(attempts):
        raise ValueError("recovered mapping does not match recovered ledger rows")

    batches = []
    seen_legacy_ids: set[str] = set()
    for attempt in attempts:
        attempt_id = attempt.get("attempt_id")
        legacy_id = attempt.get("legacy_id")
        if legacy_id not in source_by_legacy_id:
            raise ValueError(f"{attempt_id}: unknown recovered legacy id {legacy_id!r}")
        if legacy_id in seen_legacy_ids:
            raise ValueError(f"duplicate recovered legacy id {legacy_id}")
        seen_legacy_ids.add(legacy_id)
        entry = mapping_by_attempt_id.get(attempt_id)
        if entry is None:
            raise ValueError(f"{attempt_id}: missing exhaustive mapping")

        batch_ledger = {
            "object": ledger["object"],
            "version": ledger["version"],
            "signed": ledger["signed"],
            "records": [attempt],
        }
        batch_mapping = {
            "schema": mapping["schema"],
            "exhaustive": True,
            "mappings": [entry],
        }
        batches.append(
            (batch_ledger, batch_mapping, source_ref(source_by_legacy_id[legacy_id]))
        )
    return batches


def run_import(
    *,
    vela: Path,
    frontier: Path,
    ledger_path: Path,
    mapping_path: Path,
    sources_path: Path,
    apply: bool,
) -> dict[str, Any]:
    if apply and not os.environ.get("VELA_AGENT_KEY_HEX"):
        raise ValueError("--apply requires the existing VELA_AGENT_KEY_HEX")

    reports: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="erdos-recovered-import-") as directory:
        temporary = Path(directory)
        for index, (ledger, mapping, pinned_source) in enumerate(
            import_batches(ledger_path, mapping_path, sources_path)
        ):
            batch_ledger = temporary / f"ledger-{index:03d}.json"
            batch_mapping = temporary / f"mapping-{index:03d}.json"
            batch_ledger.write_text(
                json.dumps(ledger, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
            batch_mapping.write_text(
                json.dumps(mapping, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
            command = [
                str(vela),
                "foundry",
                "attempt",
                "import",
                str(batch_ledger),
                str(frontier),
                "--actor",
                ACTOR,
                "--mapping",
                str(batch_mapping),
                "--source-ref",
                pinned_source,
                "--json",
            ]
            if apply:
                command.append("--apply")
            completed = subprocess.run(
                command,
                check=True,
                capture_output=True,
                text=True,
            )
            report = json.loads(completed.stdout)
            if not report.get("ok"):
                raise ValueError(f"import failed for {pinned_source}")
            reports.append(report)

    summary_fields = (
        "records_total",
        "import_records",
        "excluded",
        "ids_preserved",
        "ids_changed",
        "deposited",
        "already_imported",
        "already_present",
        "events_appended",
    )
    summary = {
        field: sum(report["summary"][field] for report in reports)
        for field in summary_fields
    }
    rows = []
    for report in reports:
        row = dict(report["reconciliation"][0])
        row["source_ref"] = report["source"]["source_ref"]
        rows.append(row)

    first_frontier = reports[0]["frontier"]
    last_frontier = reports[-1]["frontier"]
    return {
        "schema": "erdos-frontier.recovered-attempt-import-report.v1",
        "ok": True,
        "mode": "apply" if apply else "dry_run",
        "actor": ACTOR,
        "frontier": {
            "frontier_id": first_frontier["frontier_id"],
            "event_log_hash_before": first_frontier["event_log_hash_before"],
            "event_log_hash_after": last_frontier["event_log_hash_after"],
            "snapshot_hash_before": first_frontier["snapshot_hash_before"],
            "snapshot_hash_after": last_frontier["snapshot_hash_after"],
        },
        "summary": summary,
        "reconciliation": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--vela", type=Path, required=True)
    parser.add_argument("--frontier", type=Path, default=ROOT)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--mapping", type=Path, default=DEFAULT_MAPPING)
    parser.add_argument("--sources", type=Path, default=DEFAULT_SOURCES)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    report = run_import(
        vela=args.vela,
        frontier=args.frontier,
        ledger_path=args.ledger,
        mapping_path=args.mapping,
        sources_path=args.sources,
        apply=args.apply,
    )
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
