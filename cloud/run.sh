#!/usr/bin/env bash
set -u
cd "$(dirname "$0")"
sudo apt-get update -q > /dev/null 2>&1
sudo apt-get install -y -q nauty python3-scipy python3-numpy > /dev/null 2>&1 || { echo "apt failed"; exit 1; }
G=$(command -v nauty-geng || command -v geng) || { echo "no geng"; exit 1; }
for n in 4 5 6 7 8; do "$G" -bfq "$n" | python3 dual3576.py 0.5 >> "$OUT/dual.txt"; done
for n in 9; do "$G" -bfcq "$n" | python3 dual3576.py 0.01 >> "$OUT/dual.txt"; done
echo "graphs printed: $(grep -c '^GRAPH' "$OUT/dual.txt")"
