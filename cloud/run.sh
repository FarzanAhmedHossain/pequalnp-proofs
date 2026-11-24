#!/usr/bin/env bash
# Smoke test of the shard path: machine size and one tiny cadical solve.
echo "shard $SHARD of $SHARDS on $(nproc) cores"; free -m | head -2
printf 'p cnf 2 3\n1 2 0\n-1 2 0\n1 -2 0\n' > "$OUT/t.cnf"
"$CADICAL" -q "$OUT/t.cnf" > "$OUT/t.res"; echo "cadical exit $? ($(head -1 "$OUT/t.res"))"
