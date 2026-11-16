#!/bin/sh
# Build the busycoq halting proof of 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE (bbchallenge 172044).
# usage: sh build.sh /path/to/busycoq
#   (a checkout of the BB6 branch of https://github.com/meithecatte/busycoq, which has BB62.v and Individual62.v)
# Needs Coq 8.18 (tested with 8.18.0). Copies the proof into busycoq's verify/, compiles busycoq's core files
# with plain coqc (no native compiler needed), then the proof. The proof takes about 3 minutes, almost all of it
# the vm_compute run of run_halts, and about 600 MB of memory.
set -e
BC=${1:?give the path of a busycoq checkout (BB6 branch)}
HERE=$(cd "$(dirname "$0")" && pwd)
V="$BC/verify"
[ -f "$V/Individual62.v" ] || { echo "no verify/Individual62.v in $BC: use busycoq's BB6 branch" >&2; exit 1; }
F=M_1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_HHH1LE
cp "$HERE/$F.v" "$V/"
cd "$V"
LOG=$(mktemp)
one() {
  t0=$(date +%s)
  if ! coqc -Q . BusyCoq "$1.v" > "$LOG" 2>&1; then
    echo "FAILED: $1.v" >&2; cat "$LOG" >&2; rm -f "$LOG"; exit 1
  fi
  echo "ok  $1.v  ($(( $(date +%s) - t0 )) s)"
  grep -E -A20 "Finished transaction|Closed under the global context|^Axioms:" "$LOG" || true
}
for f in LibTactics Eqb HashTable Helper Pigeonhole TM Compute Flip BB62 Permute Enumerate Individual Individual62; do
  [ -f "$f.vo" ] || one "$f"
done
one "$F"
rm -f "$LOG"
