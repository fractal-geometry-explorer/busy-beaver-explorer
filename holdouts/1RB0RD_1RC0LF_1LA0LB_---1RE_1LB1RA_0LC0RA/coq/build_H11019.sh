#!/bin/sh
# Build the busycoq non-halting proof of 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA (bbchallenge 11019).
# usage: sh build_H11019.sh /path/to/busycoq [jobs]
#   (a checkout of https://github.com/meithecatte/busycoq, or of its BB6 branch, which has its own BB62.v;
#    jobs = chunk files compiled at once, default 2)
# Needs Coq 8.18 (tested with 8.18.0). Copies lib/SymExecN.v and H11019/*.v into busycoq's verify/ (and
# lib/BB62.v, lib/Individual62.v when the checkout has none) and compiles there. Stops at the first file that
# fails, and prints coqc's output for it.
# The 8 chunk files take about 25 to 35 s each and about 450 MB of memory each; H11019_ClassData.v about 10 s and
# 750 MB; the whole build about 2.5 minutes with 2 jobs.
set -e
BC=${1:?give the path of a busycoq checkout}
JOBS=${2:-2}
HERE=$(cd "$(dirname "$0")" && pwd)
if [ -d "$BC/verify" ]; then V="$BC/verify"; elif [ -d "$BC/src/verify" ]; then V="$BC/src/verify"; else
  echo "no verify/ folder in $BC" >&2; exit 1; fi
LIB="$HERE/lib"; [ -d "$LIB" ] || LIB="$HERE"
[ -f "$V/BB62.v" ] || cp "$LIB"/BB62.v "$V"/
[ -f "$V/Individual62.v" ] || cp "$LIB"/Individual62.v "$V"/
cp "$LIB"/SymExecN.v "$V"/
if [ -d "$HERE/H11019" ]; then cp "$HERE"/H11019/*.v "$V"/; else cp "$HERE"/H11019*.v "$V"/; fi
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
         H11019_Classes H11019_Data H11019_ClassData H11019_Arrive; do one "$f"; done
t0=$(date +%s)
if ! seq 0 7 | xargs -P "$JOBS" -I{} sh -c \
  't0=$(date +%s); if coqc -Q . BusyCoq H11019_Chunk{}.v > chunk{}.log 2>&1; then echo "ok  H11019_Chunk{}.v  ($(( $(date +%s) - t0 )) s)"; rm -f chunk{}.log; else echo "FAILED: H11019_Chunk{}.v" >&2; cat chunk{}.log >&2; exit 255; fi'
then rm -f "$LOG"; exit 1; fi
echo "chunks: $(( $(date +%s) - t0 )) s of wall time with $JOBS jobs"
one H11019
rm -f "$LOG"
