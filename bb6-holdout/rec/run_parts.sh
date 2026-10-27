#!/bin/bash
# usage: run_parts.sh CUT NPARTS SPLIT -- sigma-ceiling route tree in parts, two at a time, resumable (skips finished parts)
cd "$(dirname "$0")/../csearch"
C=$1; NP=$2; SP=$3; O=../rt3/c${C}; mkdir -p $O
for p in $(seq 0 $((NP-1))); do grep -q "most halvings" $O/p$p.err 2>/dev/null || echo $p; done | \
  xargs -P 2 -I{} sh -c "s=\$(date +%s); SIGPRINT=50 ./rtree3b $C {} $NP $SP > $O/p{}.tmp 2> $O/p{}.errtmp && mv $O/p{}.tmp $O/p{}.txt && mv $O/p{}.errtmp $O/p{}.err; echo part {} \$(( \$(date +%s) - s )) s >> $O/times.txt"
echo ALLDONE >> $O/times.txt
