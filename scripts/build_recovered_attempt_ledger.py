#!/usr/bin/env python3
"""Build the unsigned Vela Attempt ledger for recovered Erdős work.

The source manifest is the review surface.  This script only projects records
classified as ``importable_attempt`` into the existing ``vela.attempt.v0.1``
wire shape; it never signs or applies an attempt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import yaml


ROOT = Path(__file__).resolve().parents[1]
SOURCE_PATH = ROOT / "sources" / "recovered-attempts.yaml"
REGISTRY_PATH = ROOT / "sources" / "work-registry.yaml"
LEDGER_PATH = ROOT / "sources" / "recovered-attempt-ledger.v2.json"
MAPPING_PATH = ROOT / "sources" / "recovered-attempt-import-map.yaml"

SOURCE_SCHEMA = "erdos-frontier.recovered-attempts.v1"
ATTEMPT_SCHEMA = "vela.attempt.v0.1"
MAPPING_SCHEMA = "vela.attempt-import-map.v1"
IMPORTABLE = "importable_attempt"
MIGRATION_ACTOR = "agent:erdos-history-import"
MIGRATION_RUN = "recovered-attempts.v1"


def load_yaml(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        value = yaml.safe_load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a YAML object")
    return value


def canonical_json_bytes(value: Any) -> bytes:
    """Match Vela's compact, recursively key-sorted canonical JSON."""

    return json.dumps(
        value,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def claim_digest(claim: str) -> str:
    return hashlib.sha256(claim.strip().encode("utf-8")).hexdigest()[:16]


def derive_attempt_id(attempt: dict[str, Any]) -> str:
    # ``legacy_id`` is reconciliation metadata understood by the importer,
    # not an Attempt field, and therefore is not part of Vela's serde-based
    # content-address preimage.
    preimage = {key: value for key, value in attempt.items() if key != "legacy_id"}
    preimage["attempt_id"] = ""
    preimage["signature"] = ""
    preimage["signer_pubkey_hex"] = ""
    digest = hashlib.sha256(canonical_json_bytes(preimage)).hexdigest()
    return f"vat_{digest[:16]}"


def source_evidence_key(record: dict[str, Any]) -> str:
    source = record["source"]
    declaration = source.get("declaration")
    suffix = f"#{declaration}" if declaration else ""
    return (
        f"source:{source['repository']}@{source['commit']}:{source['path']}"
        f"{suffix}@{source['sha256']}"
    )


def source_detail(record: dict[str, Any], evidence_key: str) -> str:
    axes = "; ".join(
        f"{field}={record[field]}"
        for field in (
            "mathematical_scope",
            "trust",
            "lifecycle",
            "location",
        )
    )
    return (
        f"recovered_record={record['record_id']}; evidence={evidence_key}; {axes}. "
        "Provenance only: accepted state and statement fidelity remain separate."
    )


def validate_source_record(record: dict[str, Any]) -> None:
    required = {
        "record_id",
        "problem",
        "classification",
        "claim",
        "source",
        "activity_type",
        "mathematical_scope",
        "trust",
        "lifecycle",
        "location",
        "method_families",
        "named_obstructions",
        "remaining_obligations",
    }
    missing = sorted(required - record.keys())
    if missing:
        raise ValueError(
            f"problem {record.get('problem', '?')}: missing fields {', '.join(missing)}"
        )
    if not isinstance(record["problem"], int) or not 1 <= record["problem"] <= 1217:
        raise ValueError(f"{record['record_id']}: invalid Erdős problem number")
    if not isinstance(record["claim"], str) or not record["claim"].strip():
        raise ValueError(f"{record['record_id']}: claim must be non-empty")
    for field in ("method_families", "named_obstructions", "remaining_obligations"):
        value = record[field]
        if not isinstance(value, list) or not all(
            isinstance(item, str) and item.strip() for item in value
        ):
            raise ValueError(f"{record['record_id']}: {field} must be a string list")

    expected_evidence_key = source_evidence_key(record)
    declared_evidence_key = record.get("evidence_key")
    if declared_evidence_key is not None and declared_evidence_key != expected_evidence_key:
        raise ValueError(
            f"{record['record_id']}: evidence_key mismatch; expected {expected_evidence_key}"
        )


def build_attempt(
    record: dict[str, Any], frontier_id: str, frontier_root: str
) -> dict[str, Any]:
    evidence_key = source_evidence_key(record)
    source = record["source"]
    attempt: dict[str, Any] = {
        "schema": ATTEMPT_SCHEMA,
        "attempt_id": "",
        "problem": record["problem"],
        "frontier": frontier_id,
        "kind": record["activity_type"],
        "claim": record["claim"],
        "detail": source_detail(record, evidence_key),
        "claimed_status": "provenance_only",
        "claim_digest": claim_digest(record["claim"]),
        "insight": (
            "Recovered activity record; accepted mathematical state and statement "
            "fidelity are evaluated separately."
        ),
        "provenance": {
            "proposer": MIGRATION_ACTOR,
            "run": MIGRATION_RUN,
        },
        "base_frontier_root": frontier_root,
        "target_obligation_id": f"erdos:{record['problem']}:recovered-activity",
        "statement_variant_id": f"erdos:{record['problem']}:source-scoped",
        "producer": {
            "system": source["repository"],
            "version": source["commit"],
            "config_digest": source["sha256"],
        },
        "signature": "",
        "signer_pubkey_hex": "",
    }
    for field in ("method_families", "remaining_obligations", "named_obstructions"):
        if record[field]:
            attempt[field] = record[field]
    if record.get("related_problems"):
        attempt["related_problems"] = record["related_problems"]

    attempt["attempt_id"] = derive_attempt_id(attempt)
    declared_attempt_id = record.get("attempt_id")
    if declared_attempt_id is not None and declared_attempt_id != attempt["attempt_id"]:
        raise ValueError(
            f"{record['record_id']}: attempt_id mismatch; expected {attempt['attempt_id']}"
        )
    # The importer carries this stable manifest join key into its import event
    # as source_legacy_id.  It makes the multi-repository ledger mechanically
    # splittable without weakening the Attempt wire schema.
    attempt["legacy_id"] = record["record_id"]
    return attempt


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    source = load_yaml(SOURCE_PATH)
    registry = load_yaml(REGISTRY_PATH)
    if source.get("schema") != SOURCE_SCHEMA:
        raise ValueError(f"{SOURCE_PATH}: expected schema {SOURCE_SCHEMA}")

    records = source.get("records")
    if not isinstance(records, list):
        raise ValueError(f"{SOURCE_PATH}: records must be a list")
    for record in records:
        if not isinstance(record, dict):
            raise ValueError(f"{SOURCE_PATH}: every record must be an object")
        validate_source_record(record)

    ordered = sorted(records, key=lambda row: (row["problem"], row["record_id"]))
    if ordered != records:
        raise ValueError(f"{SOURCE_PATH}: records must be sorted by problem and record_id")

    importable = [record for record in records if record["classification"] == IMPORTABLE]
    attempts = [
        build_attempt(
            record,
            registry["frontier_id"],
            registry["baseline_frontier_root"],
        )
        for record in importable
    ]
    attempt_ids = [attempt["attempt_id"] for attempt in attempts]
    if len(attempt_ids) != len(set(attempt_ids)):
        raise ValueError("recovered records produced duplicate Attempt ids")

    ledger = {
        "object": "CanopusAttemptLedger",
        "version": 2,
        "signed": False,
        "records": attempts,
    }
    mapping = {
        "schema": MAPPING_SCHEMA,
        "exhaustive": True,
        "mappings": [
            {
                "attempt_id": attempt["attempt_id"],
                "action": "import",
                "expected_attempt_id": attempt["attempt_id"],
                "reason": (
                    f"Recovered source record {record['record_id']}; provenance only, "
                    "not an accepted-state verdict."
                ),
            }
            for record, attempt in zip(importable, attempts, strict=True)
        ],
    }
    return ledger, mapping


def rendered_outputs() -> tuple[bytes, bytes]:
    ledger, mapping = build_outputs()
    ledger_bytes = (
        json.dumps(ledger, ensure_ascii=False, indent=2, sort_keys=False) + "\n"
    ).encode("utf-8")
    mapping_bytes = yaml.safe_dump(
        mapping,
        allow_unicode=True,
        default_flow_style=False,
        sort_keys=False,
        width=120,
    ).encode("utf-8")
    return ledger_bytes, mapping_bytes


def check_output(path: Path, expected: bytes) -> None:
    if not path.exists():
        raise ValueError(f"{path}: generated output is missing")
    actual = path.read_bytes()
    if actual != expected:
        raise ValueError(
            f"{path}: generated output is stale; run scripts/build_recovered_attempt_ledger.py"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail unless committed outputs are byte-identical to a fresh build",
    )
    args = parser.parse_args()
    ledger_bytes, mapping_bytes = rendered_outputs()
    if args.check:
        check_output(LEDGER_PATH, ledger_bytes)
        check_output(MAPPING_PATH, mapping_bytes)
        return 0

    LEDGER_PATH.write_bytes(ledger_bytes)
    MAPPING_PATH.write_bytes(mapping_bytes)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
