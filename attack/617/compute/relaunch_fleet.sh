#!/bin/zsh
# Relaunch the Erdős 617 solver fleet after a reboot/crash.
# Run from anywhere: ./relaunch_fleet.sh
# NOTE: kissat/smsg have no checkpoints — a relaunch restarts each
# leg's search from zero. Banked cube verdicts (runs/results.tsv,
# committed) are unaffected. Only relaunch legs that actually died:
#   pgrep -fl 'kissat|smsg'
set -e
cd "$(dirname "$0")"

launch() {
  local log="$1"; shift
  if pgrep -f "$*" > /dev/null; then
    echo "SKIP (already running): $*"
  else
    nohup "$@" > "runs/$log" 2>&1 &
    disown
    echo "LAUNCHED pid $!: $* -> runs/$log"
  fi
}

# Assumption-free K26 direct encoding (kissat, e7 bounded variant)
launch e7_bounded_kissat2.log ./tools/kissat/build/kissat --quiet runs/e7_bounded.cnf

# SMS direct K26 (vertex symmetry breaking)
launch sms_k26_main2.log ./tools/sat-modulo-symmetries/build/src/smsg -v 26 --dimacs runs/sms_r5_k26_cb.cnf

# SMS proof-ledger legs on K25 (silent + two loud legs)
launch sms_sum_main2.log  ./tools/sat-modulo-symmetries/build/src/smsg -v 25 --dimacs runs/sms_leg_sum_silent.cnf
launch sms_edges_main.log ./tools/sat-modulo-symmetries/build/src/smsg -v 25 --dimacs runs/sms_leg_edges_loud.cnf
launch sms_floor_main.log ./tools/sat-modulo-symmetries/build/src/smsg -v 25 --dimacs runs/sms_leg_floor_loud.cnf

echo "---"
pgrep -fl 'kissat|smsg' || true
