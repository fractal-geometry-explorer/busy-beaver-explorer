#!/bin/sh
# Build the busycoq halting proof of 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB (bbchallenge 23376).
# usage: sh build.sh /path/to/busycoq
#   (a checkout of the BB6 branch of https://github.com/ccz181078/busycoq: the proof uses the symbolic
#   execution tactics of its Individual62.v)
# Needs Coq 8.18 or later (tested with 8.18.0). Compiles busycoq's core files and the proof in verify/.
# About 2 minutes: 80 s for the level rules, 30 s for the run from blank tape.
set -e
BC=${1:?give the path of a busycoq checkout (BB6 branch)}
HERE=$(cd "$(dirname "$0")" && pwd)
V="$BC/verify"
cp "$HERE"/M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.v "$V"/
cd "$V"
[ -f Makefile.coq ] || make Makefile.coq > /dev/null
make -f Makefile.coq Individual62.vo > /dev/null 2>&1
t0=$(date +%s)
coqc -Q . BusyCoq M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.v
echo "compiled in $(( $(date +%s) - t0 )) s"
