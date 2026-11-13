#!/bin/bash
# Runs the whole independent check.  One core; about 2.5 minutes, plus 5 minutes with "full" (plain simulation of 14
# classes at B ~ 20000, 4.1e9 to 4.4e9 steps each).   usage: bash run_all.sh [full]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; export VBIN="${VBIN:-/tmp/claude-0/g09/verify11019}"; mkdir -p "$VBIN"
M=1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA
g++ -O2 -Wall -o "$VBIN/accel" "$HERE/accel.cpp" && g++ -O2 -Wall -o "$VBIN/plain" "$HERE/plain.cpp" || exit 1
fail=0
echo "== arrival from blank: plain, then accel (default; -K 12; -nojump)"
echo blank | "$VBIN/plain" $M 3000000000 20000 | cut -c1-140 > "$VBIN/blank.plain"; cat "$VBIN/blank.plain"
for o in "" "-K 12" "-nojump"; do echo blank | "$VBIN/accel" $o -minB 20000 $M | grep -v '^#' | cut -c1-140 | cmp - "$VBIN/blank.plain" && echo "accel $o: identical to plain" || fail=1; done
run(){ echo "== check.py $*"; python3 "$HERE/check.py" "$@" || fail=1; }
run static
run diff 400 1 3 300 100000000
run diff 150 2 300 2500 1000000000
run classes
run classes -K 12
run classes -big 500
run classes -K 18 -big 20
run nojump
run random 2000 7
run random 2000 8 -K 12 -big 30
run small 3000 9
run real
run halting "$HERE/halting_tails_from_notes.txt"
run selftest
[ "${1:-}" = full ] && run plainclass 14 31 0
[ $fail = 0 ] && echo "ALL CHECKS PASSED" || echo "SOME CHECK FAILED"
