#!/usr/bin/env bash
# Question 107: the tables of r6c_pisot_class.py for x = 2, 4, 6 and 8.
set -eu
cd "$(dirname "$0")"
for x in 2 4 6; do
    python3 r6c_pisot_class.py "$x" 1000000 > "data/r6c_pisot_class_$x.txt"
done
python3 r6c_pisot_class.py 8 30000000 > data/r6c_pisot_class_8.txt
python3 r6c_pisot_report.py data/r6c_pisot_class_[2468].txt > data/r6c_pisot_report.txt
