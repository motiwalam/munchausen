#!/usr/bin/env bash
# Question 104: exact census of one base with the GPU, split into shards.
#
#   bash r6c_census.sh <base> <shards> <outdir> [extra fast options]
#
# The GPU path does not take --journal, so the shards are the unit of
# resumption: a shard whose log ends with "done in" is skipped when the
# script runs again. After the last shard, `fast merge` writes
# <outdir>/b<base>-merged.txt.
set -u
here=$(cd "$(dirname "$0")" && pwd)
fast="${FAST:-$here/../fast/target/release/fast}"
b=$1
n=$2
dir=$3
shift 3
mkdir -p "$dir"
for ((i = 0; i < n; i++)); do
    out="$dir/b$b-s$i.txt"
    log="$dir/b$b-s$i.log"
    if [[ -f "$log" ]] && grep -q "done in" "$log"; then
        continue
    fi
    echo "$(date '+%F %T') base $b shard $i/$n start" >> "$dir/b$b-driver.log"
    "$fast" search "$b" --hybrid -j "${THREADS:-6}" --shard "$i/$n" --shard-by size --progress "$@" > "$out" 2> "$log"
    echo "$(date '+%F %T') base $b shard $i/$n exit $? $(tail -n 1 "$log")" >> "$dir/b$b-driver.log"
done
files=()
for ((i = 0; i < n; i++)); do files+=("$dir/b$b-s$i.txt"); done
"$fast" merge "${files[@]}" > "$dir/b$b-merged.txt"
echo "$(date '+%F %T') base $b merged, exit $?" >> "$dir/b$b-driver.log"
