#!/bin/bash
# SMS lookahead cube-and-conquer for a renumbered K_25 leg.
# Phase 1 (generate): lookahead cubes to stdout ('a <lits> 0' lines).
# Phase 2 (conquer): each cube solved WITH the minimality propagator.
#
# usage: sms_cube_pipeline.sh gen <leg> <cutoff> [prerun_s]
#        sms_cube_pipeline.sh solve <leg> <from> <to> [timeout_s]
# files: runs/sms_leg_<leg>.cnf -> runs/sms_cubes_<leg>.icnf
set -e
cd /Users/williamblair/personal/lean-proofs/compute617
SMSG=tools/sat-modulo-symmetries/build/src/smsg
LEG=$2
case $1 in
  gen)
    CUT=$3; PRERUN=${4:-60}
    nice -n 12 $SMSG -v 25 --dimacs runs/sms_leg_$LEG.cnf \
      --assignment-cutoff $CUT --prerun $PRERUN \
      > runs/sms_cubes_${LEG}_raw.out 2>&1
    grep '^a ' runs/sms_cubes_${LEG}_raw.out > runs/sms_cubes_$LEG.icnf
    wc -l runs/sms_cubes_$LEG.icnf
    ;;
  solve)
    FROM=$3; TO=$4; TMO=${5:-600}
    nice -n 12 $SMSG -v 25 --dimacs runs/sms_leg_$LEG.cnf \
      --cube-file runs/sms_cubes_$LEG.icnf --cubes-range $FROM $TO \
      --cube-timeout $TMO
    ;;
  *) echo "usage: $0 gen|solve <leg> ..."; exit 1;;
esac
