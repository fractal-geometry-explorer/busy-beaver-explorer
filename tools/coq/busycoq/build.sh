#!/bin/sh
# Build the busycoq non-halting proofs of two BB(6) holdouts.
# usage: sh build.sh /path/to/busycoq      (a checkout of https://github.com/meithecatte/busycoq)
# Needs Coq 8.18 (tested with 8.18.0). Copies the files of this folder into busycoq's verify/ and compiles there.
# Stops at the first file that fails, and prints coqc's output for it.
set -e
BC=${1:?give the path of a busycoq checkout}
HERE=$(cd "$(dirname "$0")" && pwd)
if [ -d "$BC/verify" ]; then V="$BC/verify"; elif [ -d "$BC/src/verify" ]; then V="$BC/src/verify"; else
  echo "no verify/ folder in $BC" >&2; exit 1; fi
cp "$HERE"/lib/*.v "$HERE"/H36670/*.v "$HERE"/H113677/*.v "$V"/
cd "$V"
LOG=$(mktemp)
for f in LibTactics Helper Pigeonhole TM Compute Flip Permute Individual BB62 Individual62 SymRun SymForms \
         H36670 H113677_Rules H113677_Table H113677; do
  t0=$(date +%s)
  if ! coqc -Q . BusyCoq "$f.v" > "$LOG" 2>&1; then
    echo "FAILED: $f.v" >&2; cat "$LOG" >&2; rm -f "$LOG"; exit 1
  fi
  echo "ok  $f.v  ($(( $(date +%s) - t0 )) s)"
  grep -A1 "^Axioms:\|Closed under the global context" "$LOG" || true
done
rm -f "$LOG"
