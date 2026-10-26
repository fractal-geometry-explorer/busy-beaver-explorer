#!/bin/bash
# usage: run_parts.sh K nparts splitlvl outdir   -- runs every part without a finished output, two at a time
K=$1; NP=$2; SL=$3; OUT=$4; mkdir -p $OUT
BIN=${BIN:-../csearch/nrefdfs2}
for p in $(seq 0 $((NP-1))); do grep -q "^totals:" $OUT/part_$p.txt 2>/dev/null || echo $p; done | \
  xargs -P 2 -I{} sh -c "s=\$(date +%s); $BIN $K {} $NP $SL > $OUT/part_{}.tmp 2> $OUT/part_{}.err && mv $OUT/part_{}.tmp $OUT/part_{}.txt; echo part {} \$(( \$(date +%s) - s )) s >> $OUT/times.txt"
echo ALLDONE >> $OUT/times.txt
