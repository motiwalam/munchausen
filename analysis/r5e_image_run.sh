#!/bin/sh
# Round 5, question 85: image and in-degrees of c -> multiset of S(c),
# bases 10 to 16 (dyn_cycles --image). Per-class tables go to
# data/r5e_image_b<b>_m<m>.txt, the summaries to stdout.
# usage: sh r5e_image_run.sh > data/r5e_image_summary.txt
BIN="$(dirname "$0")/../fast/target/release/dyn_cycles"
OUT="$(dirname "$0")/data"
for b in $(seq 10 16); do
  for m in 1 0; do
    nice -n 10 "$BIN" "$b" "$m" --image "$OUT/r5e_image_b${b}_m${m}.txt"
  done
done
