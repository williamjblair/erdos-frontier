import json
import hashlib
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[1]
RECOVERED_PATH = ROOT / "sources" / "recovered-attempts.yaml"
REGISTRY_PATH = ROOT / "sources" / "work-registry.yaml"
LEGACY_LEDGER_PATH = ROOT / "attack" / "attempt-ledger.v2.json"
RECOVERED_LEDGER_PATH = ROOT / "sources" / "recovered-attempt-ledger.v2.json"
RECOVERED_MAPPING_PATH = ROOT / "sources" / "recovered-attempt-import-map.yaml"
GENERATOR_PATH = ROOT / "scripts" / "build_recovered_attempt_ledger.py"

CLASSIFICATIONS = {"duplicate", "importable_attempt", "deferred_with_reason"}
ACTIVITY_TYPES = {
    "attempt",
    "computation",
    "theorem",
    "scout",
    "statement_edit",
    "proof_link_edit",
    "audit",
}
MATHEMATICAL_SCOPES = {
    "full",
    "partial",
    "conditional",
    "bounded",
    "variant",
    "not_applicable",
}
TRUST_LEVELS = {
    "declared",
    "recorded",
    "signed",
    "machine_reproduced",
    "lean_attested",
}
LIFECYCLES = {"active", "banked", "paused", "superseded", "historical"}
LOCATIONS = {
    "current_commit",
    "non_main_ref",
    "git_history_only",
    "dirty_local_overlay",
}
SHA256_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
COMMIT_RE = re.compile(r"[0-9a-f]{40}\Z")
ATTEMPT_ID_RE = re.compile(r"vat_[0-9a-f]{16}\Z")


def load_yaml(path: Path):
    with path.open(encoding="utf-8") as handle:
        return yaml.safe_load(handle)


def canonical_json_bytes(value):
    return json.dumps(
        value,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def derive_attempt_id(attempt):
    preimage = {key: value for key, value in attempt.items() if key != "legacy_id"}
    preimage["attempt_id"] = ""
    preimage["signature"] = ""
    preimage["signer_pubkey_hex"] = ""
    return "vat_" + hashlib.sha256(canonical_json_bytes(preimage)).hexdigest()[:16]


def source_evidence_key(record):
    source = record["source"]
    declaration = f"#{source['declaration']}" if source.get("declaration") else ""
    return (
        f"source:{source['repository']}@{source['commit']}:{source['path']}"
        f"{declaration}@{source['sha256']}"
    )


def test_recovered_attempts_cover_the_two_inventory_addition_sets_exactly():
    recovered = load_yaml(RECOVERED_PATH)
    registry = load_yaml(REGISTRY_PATH)

    assert recovered["schema"] == "erdos-frontier.recovered-attempts.v1"
    assert set(recovered) == {"schema", "records"}

    records = recovered["records"]
    problems = [record["problem"] for record in records]
    current = set(registry["inventory"]["current_artifact_additions"])
    history = set(registry["inventory"]["history_only_campaigns"])

    assert len(records) == 31
    assert len(problems) == len(set(problems))
    assert set(problems) == current | history
    assert current.isdisjoint(history)


def test_recovered_targets_are_not_duplicates_of_numbered_legacy_attempts():
    recovered = load_yaml(RECOVERED_PATH)
    with LEGACY_LEDGER_PATH.open(encoding="utf-8") as handle:
        ledger = json.load(handle)

    numbered_legacy = {
        record["problem"]
        for record in ledger["records"]
        if 1 <= record["problem"] <= 1217
    }
    recovered_problems = {record["problem"] for record in recovered["records"]}

    assert recovered_problems.isdisjoint(numbered_legacy)
    assert Counter(record["classification"] for record in recovered["records"]) == {
        "importable_attempt": 30,
        "deferred_with_reason": 1,
    }


def test_recovered_attempt_records_use_orthogonal_status_axes_and_pinned_sources():
    recovered = load_yaml(RECOVERED_PATH)

    for record in recovered["records"]:
        assert set(record) >= {
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
        assert record["classification"] in CLASSIFICATIONS
        assert isinstance(record["claim"], str) and record["claim"].strip()
        assert record["activity_type"] in ACTIVITY_TYPES
        assert record["mathematical_scope"] in MATHEMATICAL_SCOPES
        assert record["trust"] in TRUST_LEVELS
        assert record["lifecycle"] in LIFECYCLES
        assert record["location"] in LOCATIONS
        assert record["location"] != "dirty_local_overlay"
        assert record["evidence_key"] == source_evidence_key(record)
        if record["classification"] == "importable_attempt":
            assert ATTEMPT_ID_RE.fullmatch(record["attempt_id"])
        else:
            assert "attempt_id" not in record

        for field in ("method_families", "named_obstructions", "remaining_obligations"):
            assert isinstance(record[field], list)
            assert all(isinstance(item, str) and item.strip() for item in record[field])

        source = record["source"]
        assert set(source) >= {"repository", "commit", "path", "sha256"}
        assert COMMIT_RE.fullmatch(source["commit"])
        assert SHA256_RE.fullmatch(source["sha256"])
        assert source["path"] and not source["path"].startswith("/")
        assert "/Users/" not in record["claim"]


def test_duplicate_and_deferred_classifications_are_auditable():
    recovered = load_yaml(RECOVERED_PATH)

    for record in recovered["records"]:
        if record["classification"] == "duplicate":
            assert record.get("reason")
            assert re.fullmatch(r"vat_[0-9a-f]{16}", record["duplicate_of_attempt_id"])
        elif record["classification"] == "deferred_with_reason":
            assert record.get("reason")
            assert "duplicate_of_attempt_id" not in record
        else:
            assert "duplicate_of_attempt_id" not in record


def test_erdos_773_is_deferred_without_promoting_a_timeout_to_a_claim():
    recovered = load_yaml(RECOVERED_PATH)
    record = next(record for record in recovered["records"] if record["problem"] == 773)

    assert record["classification"] == "deferred_with_reason"
    assert record["claim"] == "largest Sidon subset of the first n perfect squares"
    assert "timeout" in record["reason"]


def test_recovered_import_artifacts_remain_one_to_one_and_source_pinned():
    recovered = load_yaml(RECOVERED_PATH)
    mapping = load_yaml(RECOVERED_MAPPING_PATH)
    with RECOVERED_LEDGER_PATH.open(encoding="utf-8") as handle:
        ledger = json.load(handle)

    importable = {
        record["record_id"]: record
        for record in recovered["records"]
        if record["classification"] == "importable_attempt"
    }
    mappings = {entry["attempt_id"]: entry for entry in mapping["mappings"]}

    assert len(ledger["records"]) == len(importable) == len(mappings) == 30
    for attempt in ledger["records"]:
        source_record = importable[attempt["legacy_id"]]
        assert mappings[attempt["attempt_id"]]["expected_attempt_id"] == attempt["attempt_id"]
        source = source_record["source"]
        pinned_ref = f"{source['repository']}@{source['commit']}:{source['path']}"
        assert "@" in pinned_ref and ":" in pinned_ref
        assert not pinned_ref.startswith("/")


def test_generated_unsigned_ledger_is_an_exact_projection_of_importable_records():
    recovered = load_yaml(RECOVERED_PATH)
    with RECOVERED_LEDGER_PATH.open(encoding="utf-8") as handle:
        ledger = json.load(handle)

    assert {key: ledger[key] for key in ("object", "version", "signed")} == {
        "object": "CanopusAttemptLedger",
        "version": 2,
        "signed": False,
    }
    importable = [
        record
        for record in recovered["records"]
        if record["classification"] == "importable_attempt"
    ]
    assert len(ledger["records"]) == len(importable) == 30
    assert [attempt["problem"] for attempt in ledger["records"]] == [
        record["problem"] for record in importable
    ]

    for source_record, attempt in zip(importable, ledger["records"], strict=True):
        assert attempt["schema"] == "vela.attempt.v0.1"
        assert attempt["legacy_id"] == source_record["record_id"]
        assert attempt["attempt_id"] == source_record["attempt_id"]
        assert attempt["attempt_id"] == derive_attempt_id(attempt)
        assert attempt["claim"] == source_record["claim"]
        assert attempt["claim_digest"] == hashlib.sha256(
            attempt["claim"].strip().encode("utf-8")
        ).hexdigest()[:16]
        assert attempt["signature"] == ""
        assert attempt["signer_pubkey_hex"] == ""
        assert attempt["claimed_status"] == "provenance_only"
        assert attempt["base_frontier_root"] == (
            "sha256:f55a9d986d525f30333cffd91f0cb4e1e1c186efb6d547212b4c2f3041013214"
        )
        assert source_record["evidence_key"] in attempt["detail"]
        assert attempt["producer"] == {
            "system": source_record["source"]["repository"],
            "version": source_record["source"]["commit"],
            "config_digest": source_record["source"]["sha256"],
        }


def test_generated_mapping_is_exhaustive_and_preserves_all_attempt_ids():
    with RECOVERED_LEDGER_PATH.open(encoding="utf-8") as handle:
        ledger = json.load(handle)
    mapping = load_yaml(RECOVERED_MAPPING_PATH)

    assert mapping["schema"] == "vela.attempt-import-map.v1"
    assert mapping["exhaustive"] is True
    assert len(mapping["mappings"]) == 30
    assert [entry["attempt_id"] for entry in mapping["mappings"]] == [
        attempt["attempt_id"] for attempt in ledger["records"]
    ]
    assert all(entry["action"] == "import" for entry in mapping["mappings"])
    assert all(
        entry["expected_attempt_id"] == entry["attempt_id"]
        for entry in mapping["mappings"]
    )


def test_recovered_ledger_generator_is_byte_deterministic():
    subprocess.run(
        [sys.executable, str(GENERATOR_PATH), "--check"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )


def test_python_attempt_id_rule_matches_vela_cross_implementation_vector():
    attempt = {
        "schema": "vela.attempt.v0.1",
        "attempt_id": "",
        "problem": 1,
        "frontier": "f",
        "kind": "k",
        "claim": "c",
        "claim_digest": "2e7d2c03a9507ae2",
        "signature": "",
        "signer_pubkey_hex": "",
    }
    assert derive_attempt_id(attempt) == "vat_0008df5d18b5bdea"
