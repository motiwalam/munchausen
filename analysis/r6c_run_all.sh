#!/usr/bin/env bash
# Questions 104 and 105: the whole chain of GPU runs, one after another.
#
#   THREADS=5 nohup bash r6c_run_all.sh > data/r6c_runs/chain.log 2>&1 &
#
# Run it again after an interruption: finished shards are skipped.
set -u
here=$(cd "$(dirname "$0")" && pwd)
dir="$here/data/r6c_runs"
mkdir -p "$dir"
census() { bash "$here/r6c_census.sh" "$1" "$2" "$dir"; }
census 42 16
census 44 32
census 45 32
census 46 64
for b in 47 48 49 50 51 52 53 54 55; do
    bash "$here/r6c_census.sh" "$b" 4 "$dir/q105" --min-digits "$b" -m 1 --zscore 3.4 --zlaw cond
done
echo "$(date '+%F %T') chain done"
