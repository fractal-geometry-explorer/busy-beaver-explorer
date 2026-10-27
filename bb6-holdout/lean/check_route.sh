#!/bin/bash
# Check the route-tree development (run ./check.sh first):
#   1. the proved module BB6/RouteTree.lean (seconds);
#   2. thm/RouteTheorem.lean, generated from thm/route_tree36.txt.gz by thm/gen_route.py: the 36-digit tree as data,
#      checked by native_decide (about 20 minutes interpreted; with --fast about 3 minutes, see ROUTE_TREE.md).
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check_route.sh [--no-theorem | --fast]
#   --fast  also compiles the BB6 modules to a shared library (lean -c, leanc) and loads it with --load-dynlib, so that
#           native_decide runs the proved check as native code instead of in Lean's interpreter.
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
LEANC=${LEANC:-$(dirname "$LEAN")/leanc}
export LEAN_PATH="$LEANLIB:$PWD/out"
MODS="Basic Cycles Rules Iter Rows Rows2 Marks Model Mid Pkt Pkt2 Gap2 Blk Contact Events PktRun Round SymForm SymRound SymSplit RouteTree"
echo "== BB6/RouteTree.lean"; $LEAN BB6/RouteTree.lean -o out/BB6/RouteTree.olean
[ "$1" = "--no-theorem" ] && { echo "ROUTE TREE MODULE CHECKED"; exit 0; }
if [ ! -f thm/RouteTheorem.lean ] || [ thm/route_tree36.txt.gz -nt thm/RouteTheorem.lean ]; then
  gunzip -c thm/route_tree36.txt.gz > thm/route_tree36.txt
  python3 thm/gen_route.py thm/route_tree36.txt thm/RouteTheorem.lean 36 8000000
fi
DYN=""
if [ "$1" = "--fast" ]; then
  mkdir -p cbuild/so
  OBJS=""
  for f in $MODS; do
    if [ ! -f cbuild/so/$f.o ] || [ BB6/$f.lean -nt cbuild/so/$f.o ]; then
      $LEAN BB6/$f.lean -c cbuild/so/$f.c
      $LEANC -O2 -fPIC -DLEAN_EXPORTING -c cbuild/so/$f.c -o cbuild/so/$f.o
    fi
    OBJS="$OBJS cbuild/so/$f.o"
  done
  $LEANC -shared -o cbuild/so/libBB6.so $OBJS
  DYN="--load-dynlib=cbuild/so/libBB6.so"
fi
echo "== thm/RouteTheorem.lean"; time $LEAN $DYN thm/RouteTheorem.lean -o out/RouteTheorem.olean
$LEAN thm/RouteAxioms.lean
echo "ROUTE TREE CHECKED"
