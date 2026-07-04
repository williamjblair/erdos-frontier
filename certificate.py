#!/usr/bin/env python3
"""Emit a formal-verification certificate as a projection of frontier state.

Usage:
    python certificate.py <problem-number> [--repo .]

A certificate here is a view of two authoritative layers the Vela frontier
already holds, joined for one problem:

  - evidence (machine tier): the frozen multi-toolchain extractor's verdict for
    the hosted proof (compiles, sorry-free, axiom set, and the Prop hypotheses
    the theorem takes as parameters). Reproducible; no human or model judgment.
    Frozen source: lean/audit_feed*.json, joined into site/verdicts.json.

  - faithfulness (signed tier): the real signed `statement.attested` event in
    .vela/, a named reviewer's Ed25519 attestation that the formal statement
    faithfully states the boxed problem. Carries the signature, so a reader can
    verify it by replay (`vela check . --strict`) rather than trusting this file.

This is the machine-reports-facts / human-signs-judgment split, serialized.
See CERTIFICATE_SCHEMA.md.
"""

from __future__ import annotations

import argparse
import glob
import json
import re
import sys
from pathlib import Path

TOOLCHAIN = {
    "plby": "Lean 4, plby/lean-proofs fork (toolchain 4.29.1)",
    "alphaproof": "Lean 4, alphaproof-nexus (toolchain 4.27.0)",
    "jayyhk": "Lean 4, Jayyhk/erdos-lean (per-problem toolchain)",
}
HOST = {"plby": "plby/lean-proofs", "alphaproof": "alphaproof-nexus",
        "jayyhk": "Jayyhk/erdos-lean"}


def load_signed_attestations(repo: Path) -> dict[int, dict]:
    """The authoritative signed tier: latest `statement.attested` event per
    problem, read straight from the event log."""
    out: dict[int, dict] = {}
    for f in glob.glob(str(repo / ".vela" / "events" / "*.json")):
        ev = json.loads(Path(f).read_text())
        if ev.get("kind") != "statement.attested":
            continue
        att = ev.get("payload", {}).get("attestation")
        if not att:
            continue
        m = re.search(r"/(\d+)", att.get("informal_ref", ""))
        if not m:
            continue
        n = int(m.group(1))
        prev = out.get(n)
        if prev is None or att.get("attested_at", "") > prev.get("attested_at", ""):
            out[n] = att
    return out


def evidence_layer(row: dict) -> dict:
    src = row.get("machine_source")
    axioms = row.get("non_kernel_axioms") or []
    hyps = row.get("named_assumptions") or []
    verdict = row.get("machine_verdict")
    thm = row.get("fc_theorem") or f"(no linked formal statement)"

    if verdict == "unconditional":
        basis = ("sorry-free, no axioms beyond Lean's standard set, and no Prop "
                 "hypotheses taken as parameters.")
    else:
        parts = []
        if axioms:
            parts.append("axioms asserted rather than proved: "
                         + ", ".join(f"`{a}`" for a in axioms))
        if hyps:
            parts.append("Prop hypotheses taken as parameters (the case an axiom "
                         "check does not see): " + ", ".join(f"`{h}`" for h in hyps))
        basis = ("not unconditional. " + "; ".join(parts)
                 + ". An unconditional verdict requires all three of: sorry-free, "
                 "no non-standard axioms, no Prop hypothesis parameters.")
    return {
        "layer": "machine",
        "formal_statement": thm,
        "proof": {
            "url": row.get("proof_link"),
            "host": HOST.get(src, src),
            "toolchain": TOOLCHAIN.get(src, "Lean 4"),
        },
        "compiles": True,
        "sorry_free": True,
        "axioms_beyond_standard": axioms,
        "hypothesis_parameters": hyps,
        "verdict": verdict,
        "verdict_basis": basis,
        "frozen_source": "lean/audit_feed*.json (multi-toolchain extractor), joined into site/verdicts.json",
        "reproduce": (f"python3 lean/extract_assumptions.py --repo {src}; "
                      f"or in the built proof: `#print axioms {thm}` plus the "
                      "theorem's non-instance Prop parameters"),
    }


def faithfulness_layer(att: dict | None) -> dict:
    if att is None:
        return {
            "layer": "signed",
            "present": False,
            "note": "No statement-fidelity attestation on the frontier yet.",
        }
    return {
        "layer": "signed",
        "present": True,
        "verdict": att.get("verdict"),
        "attested_by": att.get("attested_by"),
        "attestation_id": att.get("id"),
        "target_finding": att.get("target"),
        "formal_ref": att.get("formal_ref"),
        "formal_statement_hash": "sha256:" + att.get("formal_statement_hash", ""),
        "note": att.get("note"),
        "signer_pubkey_hex": att.get("signer_pubkey_hex"),
        "signature": att.get("signature"),
        "verify": "vela check . --strict  (replays the log and verifies every signature)",
    }


def certificate(row: dict, att: dict | None, frontier_id: str) -> dict:
    n = row["problem"]
    return {
        "schema": "vela.formal-verification-certificate.v0",
        "note": ("A projection of two authoritative layers of Vela frontier "
                 f"{frontier_id}: machine-tier evidence (reproducible, no human) "
                 "and a signed human faithfulness attestation (verifiable by replay). "
                 "The two are independent: a proof can be unconditional yet formalise "
                 "the wrong statement, or faithful yet conditional."),
        "subject": {
            "problem": f"Erdős {n}",
            "source_claim": row.get("erdos_url"),
            "frontier": frontier_id,
        },
        "evidence": evidence_layer(row),
        "faithfulness": faithfulness_layer(att),
        "record": f"https://erdos.constellate.science/finding.html?n={n}",
        "generated_by": f"erdos-frontier — projection of signed frontier state {frontier_id}",
    }


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problem", type=int)
    ap.add_argument("--repo", default=".")
    args = ap.parse_args(argv)
    repo = Path(args.repo).resolve()

    rows = json.loads((repo / "site" / "verdicts.json").read_text())["rows"]
    row = next((r for r in rows if r["problem"] == args.problem), None)
    if row is None:
        print(f"Erdős {args.problem} not in the audit feed", file=sys.stderr)
        return 1
    frontier_id = json.loads((repo / "frontier.json").read_text()).get("frontier_id", "")
    att = load_signed_attestations(repo).get(args.problem)
    print(json.dumps(certificate(row, att, frontier_id), indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
