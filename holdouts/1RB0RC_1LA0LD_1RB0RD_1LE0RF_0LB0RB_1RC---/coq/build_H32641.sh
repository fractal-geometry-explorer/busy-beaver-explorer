#!/bin/sh
# Build the busycoq non-halting proof of 1RB0RC_1LA0LD_1RB0RD_1LE0RF_0LB0RB_1RC--- (bbchallenge 32641).
# usage: sh build_H32641.sh /path/to/busycoq [jobs]
#   (a checkout of https://github.com/meithecatte/busycoq; jobs = chunk files compiled at once, default 2)
# Needs Coq 8.18 (tested with 8.18.0). Copies lib/BB62.v, lib/Individual62.v and H32641/*.v into busycoq's
# verify/ and compiles there. Stops at the first file that fails, and prints coqc's output for it.
# The 16 chunk files take about 46 s each and about 500 MB of memory each; the whole build about 7 minutes.
set -e
BC=${1:?give the path of a busycoq checkout}
JOBS=${2:-2}
HERE=$(cd "$(dirname "$0")" && pwd)
if [ -d "$BC/verify" ]; then V="$BC/verify"; elif [ -d "$BC/src/verify" ]; then V="$BC/src/verify"; else
  echo "no verify/ folder in $BC" >&2; exit 1; fi
LIB="$HERE/lib"; [ -d "$LIB" ] || LIB="$HERE"
cp "$LIB"/BB62.v "$LIB"/Individual62.v "$V"/
if [ -d "$HERE/H32641" ]; then cp "$HERE"/H32641/*.v "$V"/; else cp "$HERE"/H32641*.v "$V"/; fi
cd "$V"
LOG=$(mktemp)
one() {
  t0=$(date +%s)
  if ! coqc -Q . BusyCoq "$1.v" > "$LOG" 2>&1; then
    echo "FAILED: $1.v" >&2; cat "$LOG" >&2; rm -f "$LOG"; exit 1
  fi
  echo "ok  $1.v  ($(( $(date +%s) - t0 )) s)"
  grep -A1 "^Axioms:\|Closed under the global context" "$LOG" || true
}
for f in LibTactics Helper Pigeonhole TM Compute Flip Permute Individual BB62 Individual62 \
         H32641_Sim H32641_Period H32641_Data H32641_Bound; do one "$f"; done
t0=$(date +%s)
if ! seq 1 16 | xargs -P "$JOBS" -I{} sh -c \
  't0=$(date +%s); if coqc -Q . BusyCoq H32641_Chunk{}.v > chunk{}.log 2>&1; then echo "ok  H32641_Chunk{}.v  ($(( $(date +%s) - t0 )) s)"; rm -f chunk{}.log; else echo "FAILED: H32641_Chunk{}.v" >&2; cat chunk{}.log >&2; exit 255; fi'
then rm -f "$LOG"; exit 1; fi
echo "chunks: $(( $(date +%s) - t0 )) s of wall time with $JOBS jobs"
for f in H32641_Reach H32641; do one "$f"; done
rm -f "$LOG"
