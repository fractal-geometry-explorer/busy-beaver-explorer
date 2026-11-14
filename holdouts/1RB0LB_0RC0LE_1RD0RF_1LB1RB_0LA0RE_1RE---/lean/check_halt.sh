#!/bin/bash
# The halting proof (Halt.lean).  It first runs check.sh (kernel only), then compiles the checker (VisitCheck.lean,
# VisitSeg.lean) to native code and checks the ten segments VisitSeg1..10 and VisitRun (native_decide), then Halt.lean.
# The segments take 10 to 30 minutes each on one core, about 3 hours in all; they are independent, a finished one
# (out/VisitSegN.olean) is not redone, so the script can be restarted.  The word files VisitW*.lean hold the words at
# the segment boundaries; they were written by the checker itself (VisitGen.lean) and are checked by the segments.
# LEAN, LEANLIB as for tools/lean/check.sh; leanc is taken from the directory of the real lean binary.
set -e
cd "$(dirname "$0")"
./check.sh
S=../../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean
LEAN=${LEAN:-lean}
BIN="$(dirname "$(readlink -f "$(command -v "$LEAN")")")"
if [ -z "$LEANLIB" ]; then LEANLIB="$BIN/../lib/lean"; fi
T="$(cd ../../../tools/lean && pwd)"
O="$(pwd)/out"
export LEAN_PATH="$LEANLIB:$T/out:$O"
C="$O/c"; mkdir -p "$C"
(cd "$T" && for f in Basic Fin CTL ListFrame; do $LEAN TM/$f.lean -c "$C/TM_$f.c"; done && $LEAN TM.lean -c "$C/TM.c")
for f in VisitLaw VisitCheck; do (cd $S && $LEAN $f.lean -c "$C/$f.c"); done
(cd $S && $LEAN VisitSeg.lean -o "$O/VisitSeg.olean" -c "$C/VisitSeg.c")
"$BIN/leanc" -shared -O3 -fPIC -DLEAN_EXPORTING -o out/visit.so "$C"/*.c
for f in VisitW57000 VisitW80600 VisitW98700 VisitW114000 VisitW127400 VisitW139600 VisitW145300 VisitW150800 VisitW156100 VisitW161210 \
         VisitSeg1 VisitSeg2 VisitSeg3 VisitSeg4 VisitSeg5 VisitSeg6 VisitSeg7 VisitSeg8 VisitSeg9 VisitSeg10 VisitRun; do
  if [ -s "$O/$f.olean" ]; then echo "== $f (already checked)"; continue; fi
  echo "== $f"; (cd $S && $LEAN --load-dynlib="$O/visit.so" $f.lean -o "$O/$f.olean.tmp") && mv "$O/$f.olean.tmp" "$O/$f.olean"
done
echo "== Halt.lean"
$LEAN --load-dynlib=out/visit.so Halt.lean -o out/Halt.olean
echo "HALT CHECKED"
