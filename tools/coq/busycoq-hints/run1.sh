#!/bin/bash
# input line: fam \t tm \t cfg \t args
ulimit -s unlimited
IFS=$'\t' read -r f m k a <<< "$1"
s=$(date +%s.%N)
out=$(timeout ${TO:-90} ./hdecider --maxT ${MAXT:-300000} $a $m 2>&1 | tail -1)
rc=$?
e=$(date +%s.%N)
printf '%s\t%s\t%s\t%.1f\t%s\n' "$f" "$m" "$k" "$(echo "$e-$s"|bc)" "${out:-TIMEOUT}"
