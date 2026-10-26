#!/bin/bash
# usage: run_parts2.sh CUT NPARTS SPLIT "old_nparts:done,list" -- like run_parts.sh, two at a time, resumable; skips new parts
# whose subtrees a finished coarser part already covers (part q of NPARTS covers what old part q mod OLDN covered)
cd "$(dirname "$0")/../csearch"
C=$1; NP=$2; SP=$3; OLD=$4; O=../rt3/c${C}${OUTSUF:-}; mkdir -p $O
OLDN=${OLD%%:*}; DONE=",${OLD#*:},"
for p in $(seq 0 $((NP-1))); do
  if [ -n "$OLDN" ]; then r=$((p % OLDN)); case "$DONE" in *",$r,"*) continue;; esac; fi
  grep -q "most halvings" $O/q$p.err 2>/dev/null || echo $p
done | xargs -P 2 -I{} sh -c "s=\$(date +%s); SIGPRINT=${SIGPRINT:-20} ./rtree3d $C {} $NP $SP > $O/q{}.tmp 2> $O/q{}.errtmp && mv $O/q{}.tmp $O/q{}.txt && mv $O/q{}.errtmp $O/q{}.err; echo part q{} \$(( \$(date +%s) - s )) s >> $O/times.txt"
echo ALLDONE2 >> $O/times.txt
