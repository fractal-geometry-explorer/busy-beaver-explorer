#!/bin/bash
ulimit -s unlimited
IFS=$'\t' read -r f m bsz <<< "$1"
s=$(date +%s.%N)
out=$(timeout ${TO:-120} ./rdecider $bsz 2 10000000 $m 2>&1 | tail -1)
e=$(date +%s.%N)
printf '%s\t%s\tRWL%s\t%.1f\t%s\n' "$f" "$m" "$bsz" "$(echo "$e-$s"|bc)" "${out:-TIMEOUT}"
