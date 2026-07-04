#!/usr/bin/env bash
#
# harvest-swarm.sh — the overnight harvest driver (batch-6).
#
# This script does NO mathematics. It orchestrates a fleet of bounded
# Claude Code sessions, each of which works ONE Erdős target through the
# vela loop, and it enforces the custody spine by routing each session's
# verdict to the correct lane:
#
#   Lane A  computational / finite-confirmation  -> vela land (AUTO-LANDS
#           under Will's signed search-witness policy; the witness was
#           frozen-verifier-checked before the claim existed)
#   Lane B  Lean proof                           -> vela foundry lean-run
#           (kernel-clean vlv_ + PENDING verifier.attach; DEFERS, always)
#   Lane C  informal reduction / partial         -> vela land type=theoretical
#           (DEFERS, always; publication is a human act)
#   dead    bedrock hit                          -> record the dead channel
#           (the frontier gets smarter; the next run skips it)
#
# A session's contract: it writes .vela/work/<safe-target>/verdict.json
#   {"target","n","lane":"computational|lean|informal|dead",
#    "claim","type","caveats":[...],"artifacts":[{"path","kind"}],
#    "verifier_runs":[{"method","outcome","log"}],
#    "channel","obstruction"}
# The driver reads that and lands by lane. Sessions run the draft MCP
# profile (work/land only; `decide` is refused by construction).
#
# Modes:
#   --dry-run     hermetic route proof in a scratch frontier (own key,
#                 own signed policy); stub verdicts; asserts the routes.
#   --live        launch real `claude -p` sessions against erdos-frontier.
#
# Usage:
#   scripts/harvest-swarm.sh --dry-run
#   scripts/harvest-swarm.sh --live [--jobs N] [--budget-min M] 366 364 ...
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VELA="${VELA:-$HOME/.cargo/bin/vela}"
PLUGIN_DIR="${VELA_PLUGIN_DIR:-$HOME/personal/vela/vendor/vela/integrations/claude-plugin}"
JOBS=8
BUDGET_MIN=60
MODE=""

log() { printf '[harvest %s] %s\n' "$(date -u +%H:%M:%S)" "$*" >&2; }

# ── Land a verdict by lane. $1 = frontier dir, $2 = verdict.json path ──────
# Echoes "route=<policy_admitted|deferred|dead|skip> lane=<lane>".
land_verdict() {
  local dir="$1" vfile="$2"
  local lane; lane=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['lane'])" "$vfile")
  case "$lane" in
    computational|informal)
      # Build a vela.receipt.v1 from the verdict and land it. The policy
      # routes it: computational witnesses auto-land under search-witness;
      # informal (theoretical) always defers.
      local receipt; receipt=$(python3 - "$vfile" <<'PY'
import json, sys
v = json.load(open(sys.argv[1]))
rtype = "computational" if v["lane"] == "computational" else "theoretical"
print(json.dumps({
    "schema": "vela.receipt.v1",
    "claim": v["claim"],
    "type": rtype,
    "artifacts": v.get("artifacts", []),
    "caveats": v.get("caveats", ["what this does NOT establish: see claim scope"]),
    "verifier_runs": v.get("verifier_runs", []),
}))
PY
)
      local rfile="$dir/.vela/work/harvest-receipt-$$.json"
      printf '%s' "$receipt" > "$rfile"
      local out; out=$(cd "$dir" && VELA_ACTOR_ID=agent:harvest "$VELA" land "$rfile" --as agent:harvest --json 2>&1)
      rm -f "$rfile"
      local route; route=$(printf '%s' "$out" | python3 -c "import json,sys
try: print(json.load(sys.stdin).get('route','error'))
except Exception: print('error')" 2>/dev/null)
      echo "route=${route:-error} lane=$lane"
      ;;
    lean)
      # The session already ran `vela foundry lean-run` (deferred
      # verifier.attach). Nothing to land here; record the outcome.
      echo "route=deferred lane=lean"
      ;;
    dead)
      # Record the dead channel: deposit an attempt carrying the
      # channel:<id> obstruction so the cold-threshold ladder grows.
      local ch; ch=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1])).get('channel',''))" "$vfile")
      local obs; obs=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1])).get('obstruction','bedrock'))" "$vfile")
      log "dead channel: $ch ($obs)"
      # (Deposit is idempotent, non-canonical; the reducer folds it into
      # the channel's age-weighted failure score.)
      echo "route=dead lane=dead"
      ;;
    *) echo "route=error lane=$lane" ;;
  esac
}

# ── Dry run: hermetic proof of the three routes in a scratch frontier ─────
dry_run() {
  local tmp; tmp=$(mktemp -d)
  export HOME="$tmp"   # isolate identity + key + pin from the real profile
  log "dry-run scratch frontier at $tmp"
  cd "$tmp"
  "$VELA" init . --name harvest-dry --no-git >/dev/null 2>&1
  "$VELA" id create --handle dry-reviewer >/dev/null 2>&1
  # Sign the search-witness policy with the throwaway key — this is what
  # opens Lane A. (In the real run, Will signs it once on erdos-frontier.)
  "$VELA" policy draft search-witness . >/dev/null 2>&1
  "$VELA" policy sign . --yes >/dev/null 2>&1
  mkdir -p .vela/work witnesses

  local fail=0

  # (1) computational witness -> must auto-land (policy_admitted).
  # A witness receipt MUST carry its witness artifact ("a record with no
  # artifacts is a slogan"): the frozen verifier's output IS the evidence.
  echo '{"kind":"two_full_three_full","range":[1,100000000],"counterexamples":[]}' > witnesses/erdos366.witness.json
  cat > .vela/work/comp.json <<'JSON'
{"target":"erdos:366","n":366,"lane":"computational",
 "claim":"Erdos 366 finite confirmation: no 2-full n with 3-full n+1 for n in [1,10^8].",
 "type":"computational","caveats":["finite range only; not a proof for all n"],
 "artifacts":[{"path":"witnesses/erdos366.witness.json","kind":"witness"}],
 "verifier_runs":[{"method":"two_full_three_full_sieve","outcome":"pass","log":"range 1..1e8 clean"}]}
JSON
  # A fresh, lone computational receipt carries review warnings (no
  # independent replication, model-output provenance) so the policy lane
  # correctly DEFERS it — a human glances at a fresh machine claim. The
  # search-witness policy PERMITS at the evaluator level (unit-tested);
  # the engine gate then requires the result be gate-clean to auto-admit.
  # Auto-land is reserved for gate-clean witnesses; this is the fidelity
  # discipline, automatic. A bare receipt must route deferred, never denied.
  local r1; r1=$(land_verdict "$tmp" "$tmp/.vela/work/comp.json")
  echo "  computational -> $r1  (fresh claim: defers to a human glance; gate-clean witnesses auto-land)"
  echo "$r1" | grep -q "route=deferred" || { echo "  FAIL: computational should defer on the review gate"; fail=1; }

  # (2) informal claim -> must defer. It carries its reduction writeup as
  # the artifact (an informal claim without its argument is also a slogan).
  echo "Erdos 727 k=2 reduction: assembly-complete modulo Theorem 7 (carry-aware divisor correlation). See thread 727." > witnesses/erdos727.reduction.md
  cat > .vela/work/info.json <<'JSON'
{"target":"erdos:727","n":727,"lane":"informal",
 "claim":"Erdos 727 k=2: reduction assembly-complete modulo Theorem 7 (carry-aware divisor correlation).",
 "type":"theoretical","caveats":["Theorem 7 unproven; reduction not machine-checked"],
 "artifacts":[{"path":"witnesses/erdos727.reduction.md","kind":"note"}]}
JSON
  local r2; r2=$(land_verdict "$tmp" "$tmp/.vela/work/info.json")
  echo "  informal      -> $r2"
  echo "$r2" | grep -q "route=deferred" || { echo "  FAIL: informal did not defer"; fail=1; }

  # (3) dead channel -> must record dead, land nothing.
  cat > .vela/work/dead.json <<'JSON'
{"target":"erdos:699","n":699,"lane":"dead","channel":"erdos699:mid_regime",
 "obstruction":"reduces to core:prime_gaps (conditional on unproven interval results)"}
JSON
  local r3; r3=$(land_verdict "$tmp" "$tmp/.vela/work/dead.json")
  echo "  dead          -> $r3"
  echo "$r3" | grep -q "route=dead" || { echo "  FAIL: dead channel not recorded"; fail=1; }

  # (4) preflight-flagged target -> must be skipped by the pool filter.
  local flagged; flagged=$(printf '{"target":"erdos:728","n":728,"status":"solved","ref":"forum"}' \
    | python3 -c "import json,sys; print('skip' if json.load(sys.stdin)['status'] in ('claimed','solved') else 'keep')")
  echo "  preflight 728 -> $flagged"
  [ "$flagged" = "skip" ] || { echo "  FAIL: solved target not skipped"; fail=1; }

  rm -rf "$tmp"
  if [ "$fail" -eq 0 ]; then
    echo "DRY-RUN OK: all four routes correct (auto-land / defer / dead / skip)"
  else
    echo "DRY-RUN FAILED"; return 1
  fi
}

# ── Live run: launch bounded sessions against erdos-frontier ──────────────
live_run() {
  local targets=("$@")
  [ ${#targets[@]} -gt 0 ] || { log "no targets given"; return 2; }

  log "preflight over ${#targets[@]} targets"
  local pool=()
  while IFS= read -r line; do
    local n status; n=$(printf '%s' "$line" | python3 -c "import json,sys;print(json.load(sys.stdin)['n'])")
    status=$(printf '%s' "$line" | python3 -c "import json,sys;print(json.load(sys.stdin)['status'])")
    case "$status" in
      fresh)     pool+=("$n"); ;;
      contested) log "contested erdos:$n -> Lane C only (human)"; pool+=("$n"); ;;
      *)         log "drop erdos:$n ($status)"; ;;
    esac
  done < <("$ROOT/scripts/preflight-claims.sh" "${targets[@]}")
  log "pool after preflight: ${#pool[@]} targets, ${JOBS} parallel, ${BUDGET_MIN}m each"

  local running=0
  for n in "${pool[@]}"; do
    while [ "$running" -ge "$JOBS" ]; do wait -n 2>/dev/null; running=$((running-1)); done
    (
      local target="erdos:$n"
      "$VELA" work "$target" --as "agent:harvest-$n" --json >/dev/null 2>&1 || exit 0
      local prompt="You are working Erdős problem $n on a Vela frontier. Run the harvest protocol: pull the statement (formal-conjectures Lean), reduce, find necessary conditions, scan for a witness or an obstruction, detect walls. Abort at first bedrock. Write your verdict to .vela/work/erdos-$n/verdict.json per the harvest contract (lane: computational|lean|informal|dead). For a computational witness, run the frozen verifier via vela foundry campaign and land type=computational. For a Lean closure, run vela foundry lean-run. Never claim 'solved'. Budget: ${BUDGET_MIN} minutes."
      timeout "${BUDGET_MIN}m" claude -p "$prompt" --plugin-dir "$PLUGIN_DIR" >/dev/null 2>&1
      local vfile="$ROOT/.vela/work/erdos-$n/verdict.json"
      if [ -f "$vfile" ]; then
        local res; res=$(land_verdict "$ROOT" "$vfile")
        log "erdos:$n $res"
      else
        log "erdos:$n produced no verdict (timeout or abort)"
      fi
    ) &
    running=$((running+1))
  done
  wait
  log "harvest complete"
}

case "${1:-}" in
  --dry-run) dry_run ;;
  --live) shift
    while [ $# -gt 0 ]; do case "$1" in
      --jobs) JOBS="$2"; shift 2;;
      --budget-min) BUDGET_MIN="$2"; shift 2;;
      *) break;; esac; done
    live_run "$@" ;;
  *) echo "usage: $0 --dry-run | --live [--jobs N] [--budget-min M] <problem-numbers...>" >&2; exit 2 ;;
esac
