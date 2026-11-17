#!/bin/sh
# Build the busycoq proof that 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE halts from blank tape if and only if
# 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC does (TailWord.eqv).
# usage: sh build.sh /path/to/busycoq      (a checkout of busycoq's BB6 branch, which has BB62.v and Individual62.v)
# Tested with Coq 8.20.1 (busycoq's version) and 8.18.0. Copies Eqv_TailWord.v into busycoq's verify/ and compiles
# the core files it needs, then the file; prints the result of Print Assumptions. About 10 s in all.
set -e
BC=${1:?give the path of a busycoq checkout (BB6 branch)}
HERE=$(cd "$(dirname "$0")" && pwd)
V="$BC/verify"
[ -f "$V/Individual62.v" ] || { echo "no verify/Individual62.v in $BC: use busycoq's BB6 branch" >&2; exit 1; }
cp "$HERE/Eqv_TailWord.v" "$V/"
cd "$V"
coqc --version | head -1
for f in LibTactics Eqb HashTable Helper Pigeonhole TM Compute Flip Permute Enumerate Individual BB62 Individual62; do
  [ -f "$f.vo" ] && [ "$f.vo" -nt "$f.v" ] || coqc -Q . BusyCoq "$f.v" > /dev/null 2>&1 || { echo "FAILED: $f.v" >&2; exit 1; }
done
t0=$(date +%s)
coqc -Q . BusyCoq Eqv_TailWord.v
echo "ok  Eqv_TailWord.v  ($(( $(date +%s) - t0 )) s)"
