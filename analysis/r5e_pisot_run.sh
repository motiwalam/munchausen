#!/bin/sh
# Round 5, questions 73 and 74: the Pisot census with every near-solution
# listed (offsets j x, j = 1..30; j = 1..10 for x = 12 as in section 21.4).
# usage: sh r5e_pisot_run.sh x0 x1 > data/r5e_pisot_list_<x0>_<x1>.txt
BIN="$(dirname "$0")/../fast/target/release/r3t_pisot"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-2}"
for x in $(seq "$1" "$2"); do
  J=30
  [ "$x" -ge 12 ] && J=10
  nice -n 10 "$BIN" search "$x" "$J" list
done
