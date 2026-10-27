#!/bin/bash
# Check the end-to-end theorem (run ./check.sh first):
#   1. the proved modules BB6/RouteTree.lean and BB6/CleanTree.lean (seconds);
#   2. the exit and endgame trees, evaluated by Lean's kernel (`decide +kernel`; no compiler is trusted): the
#      generated modules thm/ExitPieces*.lean and thm/EndgamePieces*.lean hold one theorem per subtree and compile in
#      parallel (JOBS at a time, default 4; about 1 GB of memory each), and thm/ExitTheorem.lean and
#      thm/EndgameTheorem.lean assemble them;
#   3. the BB6 modules compiled to a shared library (lean -c, leanc), loaded with --load-dynlib so that native_decide
#      runs the proved checks as native code (this adds the C compiler to the trusted base; without it the prefix
#      alone takes about an hour in Lean's interpreter);
#   4. the theorem files: the loop through its passes (thm/LoopTheorem.lean), the halts after the exit and the loop,
#      the blank-tape prefix (thm/Prefix.lean, about 4 minutes), the clean-tape tree (thm/CleanTheorem.lean,
#      generated from thm/clean_tree36.txt.gz by thm/gen_clean.py), and thm/EndToEnd.lean; prints the axioms of the
#      final theorems.
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean [JOBS=4] ./check_end.sh [--interpreted]
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
LEANC=${LEANC:-$(dirname "$LEAN")/leanc}
export LEAN_PATH="$LEANLIB:$PWD/out"
DEPTH=36
GAMMA=4294967296
JOBS=${JOBS:-4}
for f in RouteTree CleanTree; do echo "== BB6/$f.lean"; $LEAN BB6/$f.lean -o out/BB6/$f.olean; done
for f in ExitStart EndgameStart; do echo "== thm/$f.lean"; $LEAN thm/$f.lean -o out/$f.olean; done
PIECES=$(cd thm && ls ExitPieces*.lean EndgamePieces*.lean | sed 's/\.lean$//')
echo "== thm/ExitPieces*.lean, thm/EndgamePieces*.lean (kernel, $JOBS at a time)"
start=$(date +%s)
printf '%s\n' $PIECES | xargs -P "$JOBS" -I{} "$LEAN" thm/{}.lean -o out/{}.olean
echo "   $(( $(date +%s) - start )) s"
DYN=""
if [ "$1" != "--interpreted" ]; then
  MODS="Basic Cycles Rules Iter Rows Rows2 Marks Model Mid Pkt Pkt2 Gap2 Blk Contact Events PktRun Round SymForm SymRound SymSplit Meets HaltClose HaltStretch Loop RouteTree CleanTree"
  mkdir -p cbuild/so
  OBJS=""
  for f in $MODS; do
    if [ ! -f cbuild/so/$f.o ] || [ BB6/$f.lean -nt cbuild/so/$f.o ]; then
      $LEAN BB6/$f.lean -c cbuild/so/$f.c
      $LEANC -O2 -fPIC -DLEAN_EXPORTING -c cbuild/so/$f.c -o cbuild/so/$f.o
    fi
    OBJS="$OBJS cbuild/so/$f.o"
  done
  $LEANC -shared -o cbuild/so/libBB6all.so $OBJS
  DYN="--load-dynlib=cbuild/so/libBB6all.so"
fi
if [ ! -f thm/CleanTheorem.lean ] || [ thm/clean_tree$DEPTH.txt.gz -nt thm/CleanTheorem.lean ]; then
  gunzip -c thm/clean_tree$DEPTH.txt.gz > thm/clean_tree$DEPTH.txt
  python3 thm/gen_clean.py thm/clean_tree$DEPTH.txt thm/CleanTheorem.lean $DEPTH $GAMMA
fi
for f in EndgameTheorem ExitTheorem ExitHalt LoopTheorem LoopHalt Prefix CleanTheorem; do
  echo "== thm/$f.lean"
  start=$(date +%s)
  $LEAN $DYN thm/$f.lean -o out/$f.olean
  echo "   $(( $(date +%s) - start )) s"
done
echo "== thm/EndToEnd.lean"; $LEAN $DYN thm/EndToEnd.lean -o out/EndToEnd.olean
$LEAN thm/EndToEndAxioms.lean
echo "END TO END CHECKED"
