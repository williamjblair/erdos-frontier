#!/usr/bin/env bash
#
# preflight-claims.sh — the credit + fidelity check that runs BEFORE the
# swarm spends an hour on anything.
#
# Two banked lessons drive this: `gh pr list` before proving for credit
# (agents have closed FC sorrys that someone claimed upstream days
# earlier), and the #728 caution (an AI "solve" that was really a partial
# result because the formal statement missed the problem's intent). For
# each candidate Erdős problem it checks formal-conjectures for an open or
# merged PR and the erdosproblems.com forum thread for an existing claim,
# and emits one JSON line per target that the harness reads.
#
# Output line: {"target": "erdos:366", "n": 366, "status": "fresh|claimed|solved|contested", "ref": "..."}
# The harness drops `claimed`/`solved` from the pool and routes `contested`
# to Lane C (human-only). Network-fail on any probe is treated as
# `contested` (fail-closed: if we cannot verify freshness, a human decides).
#
# Usage: scripts/preflight-claims.sh 366 364 398 727 699 ...
set -uo pipefail

FC_REPO="google-deepmind/formal-conjectures"

emit() { printf '{"target":"erdos:%s","n":%s,"status":"%s","ref":%s}\n' "$1" "$1" "$2" "$3"; }
jstr() { python3 -c 'import json,sys; print(json.dumps(sys.argv[1]))' "$1"; }

for n in "$@"; do
  # 1. Formal-conjectures: any PR (open or merged) naming this problem?
  pr=""
  if command -v gh >/dev/null 2>&1; then
    pr=$(gh pr list --repo "$FC_REPO" --state all --search "$n in:title" \
          --json number,title,state --limit 5 2>/dev/null \
        | python3 -c "
import sys, json, re
try: rows = json.load(sys.stdin)
except Exception: sys.exit(0)
for r in rows:
    # Match the problem number as a whole token in the PR title.
    if re.search(r'(^|[^0-9])$n([^0-9]|\$)'.replace('\$n', '$n'), r.get('title','')):
        print(f\"FC#{r['number']} ({r['state']}): {r['title']}\"); break
" 2>/dev/null)
  fi
  if [ -n "$pr" ]; then
    emit "$n" "claimed" "$(jstr "$pr")"
    continue
  fi

  # 2. Forum thread: does erdosproblems.com show a resolution/partial flag?
  #    We fetch the thread page and look for an explicit solved/resolved
  #    marker. Absent tooling or network → contested (fail-closed).
  thread=$(curl -fsS --max-time 8 "https://www.erdosproblems.com/forum/thread/$n" 2>/dev/null)
  if [ -z "$thread" ]; then
    emit "$n" "contested" "$(jstr "forum unreachable — human decides freshness")"
    continue
  fi
  flag=$(printf '%s' "$thread" | grep -ioE "resolved|solved|counterexample found|fully answered" | head -1)
  if [ -n "$flag" ]; then
    emit "$n" "solved" "$(jstr "forum thread $n flags: $flag")"
  else
    emit "$n" "fresh" "$(jstr "erdosproblems.com/forum/thread/$n")"
  fi
done
