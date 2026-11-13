#!/bin/sh
# Build the busycoq non-halting proof of 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA (bbchallenge 65826).
# usage: sh build_H65826.sh /path/to/busycoq
#   (a checkout of https://github.com/meithecatte/busycoq, or of its BB6 branch, which has its own BB62.v)
# Needs Coq 8.18 (tested with 8.18.0). Copies lib/SymExecN.v and H65826/*.v into busycoq's verify/ (and
# lib/BB62.v, lib/Individual62.v when the checkout has none) and compiles there. Stops at the first file that
# fails, and prints coqc's output for it.
# The whole build takes about 40 s; the two runs (H65826_Arrive.v, H65826_Period.v) about 10 s each; no file
# needs more than about 450 MB of memory.
set -e
BC=${1:?give the path of a busycoq checkout}
HERE=$(cd "$(dirname "$0")" && pwd)
if [ -d "$BC/verify" ]; then V="$BC/verify"; elif [ -d "$BC/src/verify" ]; then V="$BC/src/verify"; else
  echo "no verify/ folder in $BC" >&2; exit 1; fi
LIB="$HERE/lib"; [ -d "$LIB" ] || LIB="$HERE"
[ -f "$V/BB62.v" ] || cp "$LIB"/BB62.v "$V"/
[ -f "$V/Individual62.v" ] || cp "$LIB"/Individual62.v "$V"/
cp "$LIB"/SymExecN.v "$V"/
if [ -d "$HERE/H65826" ]; then cp "$HERE"/H65826/*.v "$V"/; else cp "$HERE"/H65826*.v "$V"/; fi
cd "$V"
if [ -f HashTable.v ]; then CORE="LibTactics Eqb HashTable Helper Pigeonhole TM Compute Flip Permute Enumerate Individual"
else CORE="LibTactics Helper Pigeonhole TM Compute Flip Permute Individual"; fi
LOG=$(mktemp)
one() {
  t0=$(date +%s)
  if ! coqc -Q . BusyCoq "$1.v" > "$LOG" 2>&1; then
    echo "FAILED: $1.v" >&2; cat "$LOG" >&2; rm -f "$LOG"; exit 1
  fi
  echo "ok  $1.v  ($(( $(date +%s) - t0 )) s)"
  grep -A1 "^Axioms:\|Closed under the global context" "$LOG" || true
}
for f in $CORE BB62 Individual62 SymExecN \
         H65826_Data H65826_Rules H65826_Arrive H65826_Period H65826; do one "$f"; done
rm -f "$LOG"
