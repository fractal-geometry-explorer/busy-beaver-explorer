#!/bin/bash
# Run a search split into parts (parts.h protocol), JOBS at a time, resumably: a part whose output already ends with
# its "done" line is skipped, so rerunning the same command after an interruption finishes the rest.
#
# usage: run_parts.sh NPARTS JOBS OUTDIR CMD [ARGS...]     (each part runs CMD ARGS... PART NPARTS)
# then:  python3 tools/py/merge_parts.py OUTDIR/part_*.txt
#
# Writes OUTDIR/part_P.txt (stdout), part_P.err (stderr) and one line per finished part in OUTDIR/times.txt.
set -e
NP=$1; JOBS=$2; OUT=$3; shift 3
[ $# -ge 1 ] || { echo "usage: run_parts.sh NPARTS JOBS OUTDIR CMD [ARGS...]" >&2; exit 1; }
mkdir -p "$OUT"
export OUT NP
for p in $(seq 0 $((NP - 1))); do
  grep -q "^done $p $NP\$" "$OUT/part_$p.txt" 2>/dev/null || echo "$p"
done | xargs -P "$JOBS" -I{} bash -c '
  p={}; s=$(date +%s)
  "$@" "$p" "$NP" > "$OUT/part_$p.tmp" 2> "$OUT/part_$p.err" && mv "$OUT/part_$p.tmp" "$OUT/part_$p.txt"
  echo "part $p $(( $(date +%s) - s )) s" >> "$OUT/times.txt"' _ "$@"
echo "all $NP parts in $OUT"
