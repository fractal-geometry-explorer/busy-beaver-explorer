#!/bin/bash
# usage: run.sh CUT  -- sigma-ceiling route tree in two parts, timed
cd "$(dirname "$0")/../csearch"
C=$1; s=$(date +%s)
SIGPRINT=46 ./rtree3b $C 0 2 20 > ../rt3/s${C}_0.txt 2> ../rt3/s${C}_0.err &
SIGPRINT=46 ./rtree3b $C 1 2 20 > ../rt3/s${C}_1.txt 2> ../rt3/s${C}_1.err
wait
echo "cut $C done in $(( $(date +%s) - s )) s" >> ../rt3/times.txt
