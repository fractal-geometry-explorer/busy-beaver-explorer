#!/bin/sh
# Build the marker lemma (SOC25_Marker.v) on top of busycoq's SOC25Model (Eqv_WordPairs.v, BB6 branch)
# and the round map F of busycoq PR 40 by Andrew McKnight (SOC25_Iter.v, an open pull request,
# pinned here at its head commit 069dc1eb72df69dfa595f491b5c315c3ce424ac6).
# usage: sh build.sh /path/to/busycoq
#   (a git checkout of https://github.com/ccz181078/busycoq on the BB6 branch, tested at 33209bc;
#   the script fetches the PR commit into it)
# Needs Coq 8.20 (tested with 8.20.1). Eqv_WordPairs.v takes a few minutes; the rest seconds.
set -e
BC=${1:?give the path of a busycoq checkout (BB6 branch)}
HERE=$(cd "$(dirname "$0")" && pwd)
PR40=069dc1eb72df69dfa595f491b5c315c3ce424ac6
V="$BC/verify"
git -C "$BC" cat-file -e $PR40 2>/dev/null || git -C "$BC" fetch --depth 1 origin $PR40
git -C "$BC" show $PR40:verify/SOC25_Iter.v > "$V"/SOC25_Iter.v
cp "$HERE"/SOC25_Marker.v "$V"/
cd "$V"
[ -f Makefile.coq ] || make Makefile.coq > /dev/null
make -f Makefile.coq ES_v2.vo BinaryCounter_v2.vo SimplTape.vo Individual62.vo > /dev/null 2>&1
t0=$(date +%s)
coqc -Q . BusyCoq Eqv_WordPairs.v
coqc -Q . BusyCoq SOC25_Iter.v
coqc -Q . BusyCoq SOC25_Marker.v
echo "compiled in $(( $(date +%s) - t0 )) s"
