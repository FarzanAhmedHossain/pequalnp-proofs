#!/usr/bin/env bash
# L-meta-9755 search shard: AND/OR/NOT circuit (every gate counts) for Petersen minus edge 0-1.
set -u
cd "$(dirname "$0")"
plan=(18:1:free 18:2:free 18:3:free 18:4:eq1 18:5:eq2 18:6:ge3 18:7:free 17:1:free)
p=${plan[$SHARD]}
IFS=: read -r g seed mode <<< "$p"
echo "shard $SHARD: $g gates, seed $seed, notmode $mode, cadical $CADICAL"
python3 nsearch.py "$g" "$seed" 57 "$mode" 2>&1 | tee "$OUT/search.txt"
