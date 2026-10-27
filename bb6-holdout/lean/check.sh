#!/bin/bash
# Compile the BB6 files in dependency order with a lean binary and its library (no lake needed).
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
mkdir -p out/BB6
export LEAN_PATH="$LEANLIB:$PWD/out"
for f in Basic Cycles Rules Iter Rows Rows2 Marks Model Mid Pkt Pkt2 Gap2 Blk Contact Events PktRun Round SymForm SymRound SymSplit Meets HaltClose HaltStretch; do
  echo "== BB6/$f.lean"
  $LEAN BB6/$f.lean -o out/BB6/$f.olean
done
echo "== BB6.lean"; $LEAN BB6.lean -o out/BB6.olean
echo "ALL CHECKED"
