#!/usr/bin/env bash
# L-meta-9755 wave 2: incremental CEGAR with pysat solvers.
set -u
cd "$(dirname "$0")"
python3 -m pip install -q python-sat 2>&1 | tail -2
plan=(18:11:free:cadical195 18:12:free:glucose4 18:13:eq1:cadical195 18:14:eq1:maplechrono 18:15:eq2:cadical195 18:16:free:maplechrono 18:17:le3:glucose4 18:18:eq1:lingeling)
p=${plan[$SHARD]}
IFS=: read -r gg seed mode solver <<< "$p"
echo "shard $SHARD: $gg gates, seed $seed, notmode $mode, solver $solver"
python3 -u nsearch2.py "$gg" "$seed" 47 "$mode" "$solver" 2>&1 | tee "$OUT/search.txt"
