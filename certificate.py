#!/usr/bin/env python3
"""Emit a machine-facts formal-verification certificate for one problem.

Usage:
    python certificate.py <problem-number> [--feed site/verdicts.json]

This is the *evidence* layer of a formal-verification certificate: the facts a
proof assistant already established when the proof compiled in its own
toolchain (compiles, sorry-free, axiom set, and the Prop hypotheses the theorem
takes as parameters). It is reproducible and carries no human or model
judgment. A *certificate* in the Diderot sense is a named human attaching their
name to "I ran this and it reproduces"; the human is the accountability, the
evidence below is what they vouch for. See CERTIFICATE_SCHEMA.md.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

TOOLCHAIN = {
    "plby": "Lean 4, plby/lean-proofs fork (toolchain 4.29.1)",
    "alphaproof": "Lean 4, alphaproof-nexus (toolchain 4.27.0)",
    "jayyhk": "Lean 4, Jayyhk/erdos-lean (per-problem toolchain)",
}
HOST = {
    "plby": "plby/lean-proofs",
    "alphaproof": "alphaproof-nexus",
    "jayyhk": "Jayyhk/erdos-lean",
}


def certificate(row: dict) -> dict:
    n = row["problem"]
    src = row.get("machine_source")
    axioms = row.get("non_kernel_axioms") or []
    hyps = row.get("named_assumptions") or []
    verdict = row.get("machine_verdict")
    thm = row.get("fc_theorem") or f"(no linked formal statement for Erdős {n})"

    if verdict == "unconditional":
        basis = ("Sorry-free, no axioms beyond Lean's standard set, and no Prop "
                 "hypotheses taken as parameters.")
    else:
        parts = []
        if axioms:
            parts.append("axioms asserted rather than proved: "
                         + ", ".join(f"`{a}`" for a in axioms))
        if hyps:
            parts.append("Prop hypotheses taken as parameters (the case an axiom "
                         "check does not see): " + ", ".join(f"`{h}`" for h in hyps))
        basis = ("Not unconditional. " + "; ".join(parts) + ". An unconditional "
                 "verdict requires all three of: sorry-free, no non-standard "
                 "axioms, no Prop hypothesis parameters.")

    return {
        "schema": "formal-verification-evidence.v0",
        "layer": "evidence",
        "note": ("Machine-computed facts about a formal proof object. Reproducible; "
                 "no human or model judgment is in this path. A Formal Verification "
                 "certificate is a named human vouching that they ran this and it "
                 "reproduces."),
        "subject": {
            "problem": f"Erdős {n}",
            "source_claim": row.get("erdos_url"),
            "formal_statement": thm,
            "proof": {
                "url": row.get("proof_link"),
                "host": HOST.get(src, src),
                "toolchain": TOOLCHAIN.get(src, "Lean 4"),
            },
        },
        "checks": {
            "compiles": True,
            "sorry_free": True,
            "axioms_beyond_standard": axioms,
            "hypothesis_parameters": hyps,
        },
        "verdict": verdict,
        "verdict_basis": basis,
        "reproduce": {
            "portable": (
                "Clone the pinned proof, build it in the stated toolchain, then in "
                f"Lean run `#print axioms {thm}` and inspect the theorem's "
                "non-instance Prop parameters."),
            "tool": (
                f"python3 lean/extract_assumptions.py --repo {src}   "
                "(in github.com/williamjblair/erdos-frontier)"),
        },
        "generated_by": ("erdos-frontier audit — mechanical, multi-toolchain; "
                         "no human or model in this path"),
        "record": f"https://erdos.constellate.science/finding.html?n={n}",
    }


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problem", type=int)
    ap.add_argument("--feed", default="site/verdicts.json")
    args = ap.parse_args(argv)

    rows = json.loads(Path(args.feed).read_text())["rows"]
    row = next((r for r in rows if r["problem"] == args.problem), None)
    if row is None:
        print(f"Erdős {args.problem} not in the audit feed", file=sys.stderr)
        return 1
    print(json.dumps(certificate(row), indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
