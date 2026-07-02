#!/usr/bin/env python3
"""S4: turn signed campaign drafts into a ready-to-push FC branch. Never pushes.

Two subcommands, because the signed vsa_ hash-binds the exact draft bytes so
the formal_proof link must be present BEFORE the fidelity review:

  prepare <batch>   for each gated draft with link_allowed, insert the
                    `formal_proof using lean4 at "<pinned-url>"` attribute
                    (URL pinned to the source repo's current commit SHA, never
                    a floating main). Idempotent. Then re-gate + packet + sign.

  assemble <batch>  verify EVERY draft in the batch has a signed faithful vsa_
                    whose formal_statement_hash matches the current bytes, then
                    create the FC branch, copy the files, and write the PR body
                    (the #4319 format). Stops there — Will pushes + opens the PR.

Env: FC_DIR (default ~/personal/formal-conjectures).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys

import yaml

HERE = pathlib.Path(__file__).resolve().parent.parent
STAGING = HERE / "statements"
CAMPAIGN = HERE / "campaign.yaml"
FRONTIER_JSON = HERE / "frontier.json"
FC_DIR = pathlib.Path(__import__("os").environ.get("FC_DIR",
                      str(pathlib.Path.home() / "personal/formal-conjectures")))

# proof-source GitHub repos, for SHA pinning
SOURCE_REPOS = {"plby": "plby/lean-proofs", "jayyhk": "Jayyhk/erdos-lean",
                "vlp": "williamjblair/lean-proofs"}


def batch_problems(name: str) -> list[int]:
    camp = yaml.safe_load(CAMPAIGN.read_text())
    batch = next((b for b in camp.get("batches", []) if b["name"] == name), None)
    if not batch:
        sys.exit(f"batch {name!r} not in campaign.yaml")
    return batch["problems"]


def head_sha(repo: str) -> str:
    return subprocess.run(
        ["gh", "api", f"repos/{repo}/commits/HEAD", "--jq", ".sha"],
        capture_output=True, text=True, check=True).stdout.strip()


def pin_url(url: str, shas: dict) -> str:
    m = re.match(r"https://github\.com/([^/]+/[^/]+)/blob/main/(.+)", url)
    if not m:
        return url
    repo, path = m.group(1), m.group(2)
    if repo not in shas:
        shas[repo] = head_sha(repo)
    return f"https://github.com/{repo}/blob/{shas[repo]}/{path}"


def prepare(name: str) -> int:
    shas: dict = {}
    for n in batch_problems(name):
        ddir = STAGING / str(n)
        meta = json.loads((ddir / "draft.json").read_text())
        lean_path = ddir / f"{n}.lean"
        if not meta.get("link_allowed"):
            print(f"  -- {n}: link not allowed (machine verdict "
                  f"{meta.get('machine_verdict')}); statement-only")
            continue
        text = lean_path.read_text()
        if "formal_proof" in text:
            print(f"  ok {n}: formal_proof already present")
            continue
        # the machine-audited source is the one we link
        hosted = next((h for h in meta.get("hosted", [])
                       if h.get("source") == meta.get("machine_source")), None)
        if not hosted:
            print(f"  !! {n}: no hosted entry for machine source; skipping link")
            continue
        pinned = pin_url(hosted["url"], shas)
        new, count = re.subn(
            r"@\[category ([^\]]+?)\]",
            lambda m: f'@[category {m.group(1)},\n  formal_proof using lean4 at "{pinned}"]',
            text, count=1)
        if not count:
            print(f"  !! {n}: no @[category ...] attribute found")
            continue
        lean_path.write_text(new)
        print(f"  ok {n}: linked {pinned[:90]}…")
    print("\nnow: re-run scripts/gate_draft.sh <problems>, review each statements/<n>/inputs.md"
          " against its .lean, fill statements/<batch>-verdicts.json, then"
          " `vela review . --batch statements/<batch>-verdicts.json` and re-run assemble.")
    return 0


def signed_hashes() -> dict[str, dict]:
    """formal_statement_hash -> attestation, from the replayed frontier."""
    doc = json.loads(FRONTIER_JSON.read_text())
    out = {}
    for att in doc.get("statement_attestations", []) or []:
        h = att.get("formal_statement_hash")
        if h:
            out[h] = att
    return out


def assemble(name: str) -> int:
    problems = batch_problems(name)
    signed = signed_hashes()
    branch = f"erdos-campaign-{name}"
    ready, table = [], []
    for n in problems:
        ddir = STAGING / str(n)
        meta = json.loads((ddir / "draft.json").read_text())
        data = (ddir / f"{n}.lean").read_bytes()
        h = hashlib.sha256(data).hexdigest()
        att = signed.get(h)
        if not att or att.get("verdict") != "faithful":
            print(f"  !! {n}: NO signed faithful vsa_ for current bytes "
                  f"({'stale hash' if not att else att.get('verdict')}) — excluded")
            continue
        gates = json.loads((ddir / "gates.json").read_text())
        if not gates.get("passed"):
            print(f"  !! {n}: gates not green — excluded")
            continue
        ready.append(n)
        linked = "yes" if b"formal_proof" in data else "no (statement only)"
        div = "; ".join(meta.get("divergence_notes") or []) or "none recorded"
        table.append(f"| {n} | {meta.get('upstream_state')} | {linked} | {div[:220]} |")

    if not ready:
        sys.exit("nothing signed+gated to assemble")

    subprocess.run(["git", "-C", str(FC_DIR), "checkout", "main"], check=True,
                   capture_output=True)
    subprocess.run(["git", "-C", str(FC_DIR), "pull", "--ff-only", "origin", "main"],
                   check=True, capture_output=True)
    subprocess.run(["git", "-C", str(FC_DIR), "checkout", "-B", branch], check=True,
                   capture_output=True)
    for n in ready:
        dst = FC_DIR / "FormalConjectures" / "ErdosProblems" / f"{n}.lean"
        dst.write_bytes((STAGING / str(n) / f"{n}.lean").read_bytes())
        subprocess.run(["git", "-C", str(FC_DIR), "add", str(dst)], check=True)

    body = "\n".join([
        f"Adds Formal Conjectures statements for Erdős problems "
        f"{', '.join(str(n) for n in ready)}.",
        "",
        "Each statement was drafted from the boxed problem text on "
        "erdosproblems.com (docstrings verbatim), cross-checked against two "
        "independently hosted Lean proofs, and reviewed for statement fidelity "
        "before submission. `formal_proof` links (pinned to a commit) are "
        "included only where the hosted proof is unconditional under an axiom "
        "and hypothesis audit; divergences from the hosted formalizations are "
        "noted below.",
        "",
        "| problem | upstream state | proof linked | divergence notes |",
        "|---|---|---|---|",
        *table,
        "",
        "Part of #3998.",
    ])
    body_path = STAGING / f"_batch-{name}-pr-body.md"
    body_path.write_text(body + "\n")
    print(f"\nassembled {len(ready)}/{len(problems)} on branch {branch!r} in {FC_DIR}")
    print(f"PR body: {body_path}")
    print("\nWILL, from the FC checkout:")
    print(f"  git commit -m 'ErdosProblems: add {', '.join(str(n) for n in ready)} (#3998 sync)'")
    print(f"  git push -u fork {branch}")
    print(f"  gh pr create -R google-deepmind/formal-conjectures --head williamjblair:{branch} "
          f"--title 'ErdosProblems: add {', '.join(str(n) for n in ready)} (#3998 sync)' "
          f"--body-file {body_path}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["prepare", "assemble"])
    ap.add_argument("batch")
    args = ap.parse_args()
    return prepare(args.batch) if args.cmd == "prepare" else assemble(args.batch)


if __name__ == "__main__":
    sys.exit(main())
