#!/bin/sh
# Round 5, question 74: the full defect spectrum of the Pisot bases by
# brute force over every N <= Nmax (r3t_pisot defects), |D| <= 40 x.
# usage: sh r5e_pisot_defects.sh   (writes data/r5e_pisot_defects_x<x>.txt)
BIN="$(dirname "$0")/../fast/target/release/r3t_pisot"
OUT="$(dirname "$0")/data"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-2}"
for spec in 2:100000 3:1000000 4:1000000 5:1000000 6:10000000 7:3000000 8:30000000; do
  x=${spec%%:*}; n=${spec##*:}
  nice -n 10 "$BIN" defects "$x" "$n" $((40 * x)) > "$OUT/r5e_pisot_defects_x$x.txt"
done
