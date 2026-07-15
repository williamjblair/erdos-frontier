#!/usr/bin/env python3
"""Emit human-review match-check packets for problems needing a statement audit.

A packet is a markdown artifact with three panels for a reviewer to compare:

  1. Upstream statement   — the boxed problem on erdosproblems.com (LaTeX view).
  2. FC theorem           — the Formal Conjectures file for this problem.
  3. Hosted theorem(s)    — the hosted Lean proof source(s) and their state.

The reviewer reads all three and decides whether the formal theorem faithfully
states the boxed problem. Packets are written to packets/match-check/erdos_<n>.md.

Reuses the audit's own row builders (row_for_problem / build_fc /
build_proofs / proof_url) so the packet never drifts from the computed status.

Usage:
    python match_packet.py 214            # one problem
    python match_packet.py                # all rows needing a match-check
    python match_packet.py --draft 24 93  # campaign drafts (statements/<n>/)

`--draft` makes panel 2 the staged draft statement and surfaces the drafter's
divergence notes. The packet is review material only; it never signs or records
a verdict.
"""

from __future__ import annotations

import json
from pathlib import Path
import sys

from erdos_frontier import (
    SOURCE_LABEL,
    load_live_status,
)


# Buckets whose statement/theorem relation has not been settled and so benefit
# from a human-readable comparison packet.
PACKET_BUCKETS = {
    "needs-human-match-check",
    "mismatch",
    "hypothesis-conditional",
}

PACKET_DIR = Path("packets/match-check")


def render_packet(row: dict) -> str:
    problem = row["problem"]
    out: list[str] = []
    out.append(f"# Match-check packet — Erdős problem {problem}\n")
    if row.get("discrepancy"):
        out.append("> **Discrepancy** — the frozen AI-contributions wiki records this as a "
                   "full solution, but the hosted Lean proof is conditional. The resolution "
                   "decision (L3) at the bottom is the point of this packet.\n")
    out.append(f"Computed bucket: `{row['bucket']}`")
    fidelity = row.get("fidelity")
    if fidelity:
        out.append(
            f"Signed verdict: `{fidelity.get('verdict')}` "
            f"({fidelity.get('source')}, {fidelity.get('reviewer') or 'unknown'})"
        )
    override = row.get("override")
    if override and override.get("reason"):
        out.append(f"Override note: {override['reason']}")
    out.append("")

    machine = row.get("machine")
    if machine:
        out.append("## Machine evidence (L1) — deterministic, no human/model judgment\n")
        out.append(f"- Verdict: `{machine.get('verdict')}`")
        if machine.get("non_kernel_axioms"):
            out.append(f"- Non-kernel axioms: `{', '.join(machine['non_kernel_axioms'])}` "
                       "(visible to `#print axioms`)")
        if machine.get("named_assumptions"):
            out.append("- **Undischarged named assumptions** (theorem parameters — "
                       "`#print axioms` cannot see these):")
            for a in machine["named_assumptions"]:
                out.append(f"  - `{a}`")
            out.append("  → the proof is conditional on the above; it is NOT an "
                       "unconditional resolution even if kernel-clean.")
        out.append("")

    wiki = row.get("wiki")
    if wiki and wiki.get("outcome_label"):
        out.append("## Wiki claim (frozen AI-contributions wiki, 2026-06-30)\n")
        out.append(f"- Recorded outcome: {wiki['outcome_label']}")
        if wiki.get("ai_systems"):
            out.append(f"- AI systems: {', '.join(wiki['ai_systems'])}")
        if wiki.get("humans"):
            out.append(f"- Humans: {', '.join(wiki['humans'])}")
        out.append("")

    out.append("## 1. Upstream statement\n")
    out.append(f"- Boxed problem: {row['erdos_url']}")
    out.append(f"- LaTeX source: {row['latex_url']}")
    out.append(f"- Upstream state: `{row['erdos_state']}`\n")

    out.append("## 2. FC theorem\n")
    fc = row.get("fc") or {}
    if fc.get("path"):
        out.append(f"- File: `{fc['path']}`")
        out.append(
            "- View: "
            f"https://github.com/google-deepmind/formal-conjectures/blob/main/{fc['path']}"
        )
        out.append(f"- Linked formal_proof: {'yes' if fc.get('linked') else 'no'}")
    else:
        out.append("- No Formal Conjectures file for this problem yet.")
    out.append("")

    out.append("## 3. Hosted theorem signature(s)\n")
    if row["proof_links"]:
        for link in row["proof_links"]:
            label = SOURCE_LABEL.get(link["source"], link["source"])
            flags = []
            if link.get("complete"):
                flags.append("complete")
            if link.get("conditional"):
                flags.append("conditional")
            if link.get("partial"):
                flags.append("partial")
            state = link.get("state") or "?"
            out.append(f"- {label} — state `{state}` ({', '.join(flags) or 'unflagged'})")
            out.append(f"  - {link['url']}")
    else:
        out.append("- No hosted Lean proof source for this problem.")
    out.append("")

    out.append("## Decision — statement fidelity (L2)\n")
    out.append(
        "- [ ] faithful — the formal theorem states the boxed problem; safe to link.\n"
        "- [ ] variant — proves a weaker/variant statement; do not link as complete.\n"
        "- [ ] unfaithful — does not prove the boxed problem; mismatch.\n"
    )
    if row.get("discrepancy"):
        out.append("## Decision — resolution (L3): does the conditional proof justify "
                   "“formally solved”?\n")
        out.append(
            "- [ ] solved — the proof is unconditional after all; the machine flag is wrong "
            "(if so, clear the problem in `staging_cleared.yaml` only after confirming).\n"
            "- [ ] conditional — established ONLY under the named assumption; record as "
            "conditional, not as a solve.\n"
            "- [ ] not-solved — the assumption is the crux; this does not resolve the boxed "
            "problem.\n"
            "- [ ] needs-source-update — the boxed problem/answer text needs revision first.\n"
        )
    return "\n".join(out)


def write_packet(row: dict, root: str | Path = ".") -> Path:
    out_dir = Path(root) / PACKET_DIR
    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / f"erdos_{row['problem']}.md"
    path.write_text(render_packet(row))
    return path


def select_rows(payload: dict, problem: int | None) -> list[dict]:
    if problem is not None:
        return [row for row in payload["rows"] if row["problem"] == problem]
    # Priority review set: every discrepancy (wiki records solved, the proof is
    # conditional — the highest-value judgments) plus the unsettled statement
    # buckets. Discrepancies span buckets the bucket filter alone misses (an
    # axiom-conditional proof sits in `docstring`, not `hypothesis-conditional`).
    rows = [row for row in payload["rows"]
            if row.get("discrepancy") or row["bucket"] in PACKET_BUCKETS]
    # discrepancies first
    return sorted(rows, key=lambda r: (not r.get("discrepancy"), r["problem"]))


DRAFT_DIR = Path("statements")
DRAFT_PACKET_DIR = Path("packets/draft-review")


def render_draft_packet(problem: int, row: dict | None) -> str:
    """The S3 fidelity packet for a STAGED campaign draft."""
    ddir = DRAFT_DIR / str(problem)
    draft = json.loads((ddir / "draft.json").read_text())
    lean = (ddir / f"{problem}.lean").read_text()
    out: list[str] = []
    out.append(f"# Draft-review packet — Erdős problem {problem}\n")
    out.append(f"Campaign draft (statements/{problem}/). The verdict you sign is "
               "hash-bound to the exact draft bytes below — any post-sign edit "
               "invalidates it and must re-gate.\n")
    out.append(f"- Upstream state: `{draft.get('upstream_state')}`")
    out.append(f"- Machine verdict on the hosted proof: `{draft.get('machine_verdict')}` "
               f"(source `{draft.get('machine_source')}`)")
    out.append(f"- formal_proof link allowed: `{draft.get('link_allowed')}`\n")

    out.append("## 1. Upstream statement (the boxed problem)\n")
    out.append(f"- https://www.erdosproblems.com/{problem}")
    out.append(f"- LaTeX: https://www.erdosproblems.com/latex/{problem}")
    out.append(f"- Full verbatim text: `statements/{problem}/inputs.md`\n")

    out.append("## 2. THE DRAFT (judge this)\n")
    out.append("```lean")
    out.append(lean.rstrip())
    out.append("```\n")

    notes = draft.get("divergence_notes") or []
    out.append("## Drafter's divergence notes (vs the hosted theorems)\n")
    if notes:
        for n in notes:
            out.append(f"- {n}")
    else:
        out.append("- _none recorded — verify that is actually true_")
    out.append("")

    out.append("## 3. Hosted theorem(s) — the shape priors\n")
    for h in draft.get("hosted") or []:
        out.append(f"- {h.get('source')}: {h.get('url')}")
    out.append(f"- Extracts inlined in `statements/{problem}/inputs.md`\n")

    out.append("## Decision — statement fidelity of THE DRAFT (L2)\n")
    out.append(
        "- [ ] faithful — the draft states the boxed problem; submit.\n"
        "- [ ] variant — needs redraft (say what diverges).\n"
        "- [ ] unfaithful — reject (record why in campaign.yaml).\n")
    return "\n".join(out)


def draft_main(problems: list[int]) -> int:
    DRAFT_PACKET_DIR.mkdir(parents=True, exist_ok=True)
    for n in problems:
        ddir = DRAFT_DIR / str(n)
        if not (ddir / f"{n}.lean").exists():
            print(f"!! {n}: no staged draft")
            continue
        draft = json.loads((ddir / "draft.json").read_text())
        if draft.get("status") not in ("drafted", "gated"):
            print(f"!! {n}: draft status is {draft.get('status')!r} (want drafted/gated)")
            continue
        gates = ddir / "gates.json"
        if not (gates.exists() and json.loads(gates.read_text()).get("passed")):
            print(f"!! {n}: mechanical gates not green — run scripts/gate_draft.sh {n}")
            continue
        path = DRAFT_PACKET_DIR / f"erdos_{n}.md"
        path.write_text(render_draft_packet(n, None))
        print(f"wrote {path}")
    return 0


def main(argv: list[str]) -> int:
    if len(argv) > 1 and argv[1] == "--draft":
        return draft_main([int(a) for a in argv[2:]])
    problem = int(argv[1]) if len(argv) > 1 else None
    payload = load_live_status()
    rows = select_rows(payload, problem)
    if not rows:
        target = f"problem {problem}" if problem is not None else "the match-check buckets"
        print(f"No rows found for {target}.")
        return 0
    for row in rows:
        path = write_packet(row)
        print(f"wrote {path}")
    if problem is None:
        write_index(rows)
    return 0


def write_index(rows: list[dict], root: str | Path = ".") -> Path:
    """A reviewer worklist: discrepancies (wiki=solved, proof conditional) first."""
    disc = [r for r in rows if r.get("discrepancy")]
    other = [r for r in rows if not r.get("discrepancy")]
    out = ["# Review queue\n",
           "Human-signed L2 (statement fidelity) + L3 (resolution) verdicts. The "
           "machine layer is done; these are the judgments only a key-holder makes. "
           "No AI signs.\n"]
    out.append(f"## Discrepancies — priority ({len(disc)})\n")
    out.append("Wiki records a full solution; the hosted Lean proof is conditional.\n")
    for r in sorted(disc, key=lambda r: r["problem"]):
        m = r.get("machine") or {}
        on = ", ".join(m.get("named_assumptions") or m.get("non_kernel_axioms") or [])
        out.append(f"- **[{r['problem']}](packets/match-check/erdos_{r['problem']}.md)** "
                   f"— wiki: {(r.get('wiki') or {}).get('outcome_label')}; conditional on `{on}`")
    out.append(f"\n## Other unsettled statements ({len(other)})\n")
    for r in sorted(other, key=lambda r: r["problem"]):
        out.append(f"- [{r['problem']}](packets/match-check/erdos_{r['problem']}.md) — `{r['bucket']}`")
    path = Path(root) / PACKET_DIR / "README.md"
    path.write_text("\n".join(out) + "\n")
    print(f"wrote {path}")
    return path


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
