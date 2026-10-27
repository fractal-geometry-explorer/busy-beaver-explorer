#!/bin/bash
# Compile the clean-tape tree builder ExploreCT.lean to a native binary (lean -c for every module, then leanc).
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./cbuild_ct.sh   (after ./check.sh)
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
LEANC=${LEANC:-$(dirname "$LEAN")/leanc}
export LEAN_PATH="$LEANLIB:$PWD/out"
mkdir -p cbuild
OBJS=""
for f in Basic Cycles Rules Iter Rows Rows2 Marks Model Mid Pkt Pkt2 Gap2 Blk Contact Events PktRun Round SymForm SymRound SymSplit RouteTree CleanTree; do
  if [ ! -f cbuild/$f.o ] || [ BB6/$f.lean -nt cbuild/$f.o ]; then
    $LEAN BB6/$f.lean -c cbuild/$f.c
    $LEANC -O2 -c cbuild/$f.c -o cbuild/$f.o
  fi
  OBJS="$OBJS cbuild/$f.o"
done
$LEAN ExploreCT.lean -c cbuild/ExploreCT.c
$LEANC -O2 -c cbuild/ExploreCT.c -o cbuild/ExploreCT.o
$LEANC -o cbuild/ExploreCT cbuild/ExploreCT.o $OBJS
echo built cbuild/ExploreCT
