#!/bin/bash
# Check the route-tree development (run ./check.sh first):
#   1. the proved modules BB6/RouteTree.lean and BB6/RouteExplore.lean (seconds);
#   2. thm/RouteTheorem.lean: the route tree built by the proved explorer, at every depth and every cone constant
#      (nothing evaluated, seconds), and thm/CleanTheorem.lean, the clean-tape tree the same way (seconds);
#   3. thm/RouteMass.lean: the leaf counts and cut measure of the 36-digit tree, evaluated by native_decide; with
#      DEPTH=40 also thm/RouteMass40.lean (the 40-digit tree).  No theorem about the machine uses them.
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean [DEPTH=36|40] ./check_route.sh [--no-theorem | --fast]
#   --fast  compiles the BB6 modules to a shared library (lean -c, leanc) and loads it with --load-dynlib, so that
#           native_decide runs the explorer as native code instead of in Lean's interpreter.
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
LEANC=${LEANC:-$(dirname "$LEAN")/leanc}
export LEAN_PATH="$LEANLIB:$PWD/out"
DEPTH=${DEPTH:-36}
case $DEPTH in 36) MASS="RouteMass" ;; 40) MASS="RouteMass RouteMass40" ;; *) echo "DEPTH must be 36 or 40"; exit 1 ;; esac
MODS="Basic Cycles Rules Iter Rows Rows2 Marks Model Mid Pkt Pkt2 Gap2 Blk Contact Events PktRun Round SymForm SymRound SymSplit RouteTree CleanTree RouteExplore"
for f in RouteTree CleanTree RouteExplore; do echo "== BB6/$f.lean"; $LEAN BB6/$f.lean -o out/BB6/$f.olean; done
for f in RouteTheorem CleanTheorem; do echo "== thm/$f.lean"; $LEAN thm/$f.lean -o out/$f.olean; done
$LEAN thm/RouteAxioms.lean
[ "$1" = "--no-theorem" ] && { echo "ROUTE TREE THEOREM CHECKED"; exit 0; }
DYN=""
if [ "$1" = "--fast" ]; then
  mkdir -p cbuild/so
  OBJS=""
  for f in $MODS; do
    # regenerate the C code and recompile only where it changed (a module's code can change with its imports)
    $LEAN BB6/$f.lean -c cbuild/so/$f.c.new > /dev/null
    if [ ! -f cbuild/so/$f.o ] || ! cmp -s cbuild/so/$f.c.new cbuild/so/$f.c; then
      mv cbuild/so/$f.c.new cbuild/so/$f.c
      $LEANC -O2 -fPIC -DLEAN_EXPORTING -c cbuild/so/$f.c -o cbuild/so/$f.o
    else
      rm cbuild/so/$f.c.new
    fi
    OBJS="$OBJS cbuild/so/$f.o"
  done
  $LEANC -shared -o cbuild/so/libBB6.so $OBJS
  DYN="--load-dynlib=cbuild/so/libBB6.so"
fi
for f in $MASS; do echo "== thm/$f.lean"; time $LEAN $DYN thm/$f.lean -o out/$f.olean; done
echo "ROUTE TREE CHECKED"
