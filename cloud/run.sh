#!/usr/bin/env bash
# CYCLE_11 search shard: SHARD -> (gates for H, seed); the full circuit has 33 + gates.
set -u
cd "$(dirname "$0")"
plan=(42:1 42:2 42:3 41:1 41:2 41:3 40:1 40:2 40:3 39:1 39:2 39:3 39:4 38:1 38:2 38:3)
p=${plan[$SHARD]}
g=${p%%:*}
seed=${p##*:}
echo "shard $SHARD: H-circuit of $g gates (total $((g + 33))), seed $seed, cadical $CADICAL"
python3 gsearch.py "$g" "$seed" "${MINUTES:-320}" 2>&1 | tee "$OUT/search.txt"
