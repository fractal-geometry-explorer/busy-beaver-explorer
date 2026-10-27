#!/bin/bash
# Compile the route-tree builder ExploreRT.lean to a native binary (lean -c for every module, then leanc).
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./cbuild_rt.sh   (after ./check.sh and the RouteTree module)
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
LEANC=${LEANC:-$(dirname "$LEAN")/leanc}
export LEAN_PATH="$LEANLIB:$PWD/out"
mkdir -p cbuild
OBJS=""
for f in Basic Cycles Rules Iter Rows Rows2 Marks Model Mid Pkt Pkt2 Gap2 Blk Contact Events PktRun Round SymForm SymRound SymSplit RouteTree; do
  if [ ! -f cbuild/$f.o ] || [ BB6/$f.lean -nt cbuild/$f.o ]; then
    $LEAN BB6/$f.lean -c cbuild/$f.c
    $LEANC -O2 -c cbuild/$f.c -o cbuild/$f.o
  fi
  OBJS="$OBJS cbuild/$f.o"
done
$LEAN ExploreRT.lean -c cbuild/ExploreRT.c
$LEANC -O2 -c cbuild/ExploreRT.c -o cbuild/ExploreRT.o
$LEANC -o cbuild/ExploreRT cbuild/ExploreRT.o $OBJS
echo built cbuild/ExploreRT
