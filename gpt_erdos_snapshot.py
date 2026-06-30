#!/usr/bin/env python3
"""Parse neelsomani/gpt-erdos's Findings classification into a claim registry.

gpt-erdos is an independent, human-curated record of GPT-5.2-Pro candidate solutions
to Erdős problems, classified by how each holds up (new proof, literature, hidden
constraints, conditional on a conjecture, subtle error, ...). It is a CLAIMS source,
not a proof corpus — its value here is cross-referencing an independent human review
against this audit's mechanical proof verdicts. We snapshot the README (frozen at the
recorded commit; the repo has not changed since 2026-01-25) and re-derive the registry
offline; fc_sync_status reads only the JSON.

Source: neelsomani/gpt-erdos README "Findings" table (commit 21b48ae, 2026-01-25).
"""

from __future__ import annotations

import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
SRC = HERE / "gpt_erdos_snapshot" / "README.md"
OUT = HERE / "gpt_erdos_registry.json"

GPT_ERDOS_COMMIT = "21b48ae6b97279e9fe6781e3744e1cdd835e2cc1"
SNAPSHOT_AT = "2026-01-25"
SOURCE = "neelsomani/gpt-erdos README Findings table"

# Map the table's category labels to compact slugs. `conditional_conjecture` and
# `hidden_constraints` are the rows that bear on this audit's discrepancy view.
CATEGORY_SLUG = {
    "New proofs": "new_proof",
    "Exact literature solutions identified": "literature",
    "Partial literature extensions": "partial_literature",
    "Typos identified": "typo",
    "Solved as stated, hidden constraints": "hidden_constraints",
    "Valid but non-improving proofs": "non_improving",
    "Conditional on conjectures": "conditional_conjecture",
    "Subtle errors": "subtle_error",
}


def parse(md: str) -> dict[str, dict]:
    out: dict[str, dict] = {}
    in_findings = False
    for line in md.splitlines():
        if line.startswith("## "):
            in_findings = line.strip() == "## Findings"
            continue
        if not (in_findings and line.lstrip().startswith("|")):
            continue
        cells = [c.strip() for c in line.split("|")]
        cells = [c for c in cells if c != ""]
        if len(cells) < 3 or cells[0] in ("Category", "") or set(cells[0]) <= {"-", ":"}:
            continue
        category, _desc, problems = cells[0], cells[1], cells[-1]
        slug = CATEGORY_SLUG.get(category)
        if not slug:
            continue
        for num in re.findall(r"\b(\d+)\b", problems):
            out[num] = {"category": slug, "category_label": category}
    return out


def main() -> int:
    problems = parse(SRC.read_text(encoding="utf-8"))
    by_cat: dict[str, int] = {}
    for rec in problems.values():
        by_cat[rec["category"]] = by_cat.get(rec["category"], 0) + 1
    payload = {
        "schema": "gpt-erdos-claims.v1",
        "source": SOURCE,
        "commit": GPT_ERDOS_COMMIT,
        "snapshot_at": SNAPSHOT_AT,
        "note": "Independent human classification of GPT-5.2-Pro candidate solutions. "
                "A claims source for cross-reference, not a proof corpus.",
        "summary": {"problems": len(problems), "by_category": dict(sorted(by_cat.items()))},
        "problems": {k: problems[k] for k in sorted(problems, key=int)},
    }
    OUT.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {OUT.name}: {len(problems)} classified problems")
    print(f"  by_category: {payload['summary']['by_category']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
