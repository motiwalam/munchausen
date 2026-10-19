#!/bin/sh
# Round 5, question 73: rerun r2c_cycles2 (section 23.3) for bases 4 to 16
# and keep every near-2-cycle line "two j n > s" with its base and
# convention, so that the near-2-cycles can be grouped by multiset.
# Journals go to $R5E_SCRATCH (they hold the class matrices).
# usage: sh r5e_cycles2_run.sh > data/r5e_cycles2_hits.txt
BIN="$(dirname "$0")/../fast/target/release/r2c_cycles2"
SCR="${R5E_SCRATCH:?set R5E_SCRATCH}"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-2}"
for b in $(seq 4 16); do
  for m in 0 1; do
    j="$SCR/cyc_${b}_${m}.txt"
    nice -n 10 "$BIN" "$b" "$m" 30 "$j" 2>/dev/null | grep '^summary'
    grep '^two ' "$j" | sed "s/^/b=$b m=$m /"
  done
done
