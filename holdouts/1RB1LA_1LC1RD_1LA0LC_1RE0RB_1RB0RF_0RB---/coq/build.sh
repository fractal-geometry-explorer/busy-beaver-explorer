#!/bin/sh
# Build the closed counter model of 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and
# 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC--- (SOC23Model.v) and its consequence for both machines
# (SOC23_Holdouts.v: a halt needs a corner round cfgL len 0 (2^len)), and the converse
# (SOC23Corner.v: every corner halts, so halts_iff_corner: a machine halts iff the orbit hits a corner).
# usage: sh build.sh /path/to/busycoq
#   (a checkout of the BB6 branch of https://github.com/ccz181078/busycoq, tested at 33209bc)
# Needs Coq 8.20 (tested with 8.20.1). About 1 minute after busycoq's core files are built.
set -e
BC=${1:?give the path of a busycoq checkout (BB6 branch)}
HERE=$(cd "$(dirname "$0")" && pwd)
V="$BC/verify"
cp "$HERE"/SOC23Model.v "$HERE"/SOC23_Holdouts.v "$HERE"/SOC23Corner.v "$V"/
cd "$V"
[ -f Makefile.coq ] || make Makefile.coq > /dev/null
make -f Makefile.coq ES_v2.vo BinaryCounter_v2.vo SimplTape.vo Individual62.vo > /dev/null 2>&1
t0=$(date +%s)
coqc -Q . BusyCoq SOC23Model.v
coqc -Q . BusyCoq SOC23_Holdouts.v
coqc -Q . BusyCoq SOC23Corner.v
echo "compiled in $(( $(date +%s) - t0 )) s"
