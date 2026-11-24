#!/usr/bin/env bash
# L-meta-3576 search shard: every bipartite 4-cycle-free graph on NMIN..NMAX vertices (geng -bf),
# split by geng's res/mod over SHARDS jobs.
set -u
cd "$(dirname "$0")"
. ./job.env
sudo apt-get update -q > /dev/null 2>&1
sudo apt-get install -y -q nauty python3-scipy python3-numpy > /dev/null 2>&1 || { echo "apt failed"; exit 1; }
G=$(command -v nauty-geng || command -v geng) || { echo "no geng"; exit 1; }
for n in $(seq "${NMIN:-2}" "${NMAX:-12}"); do
  echo "== n=$n $(date -u +%H:%M:%S)"
  "$G" -bfq "$n" "$SHARD/$SHARDS" | python3 search3576.py | tee -a "$OUT/result.txt"
done
echo "done $(date -u +%H:%M:%S)"
