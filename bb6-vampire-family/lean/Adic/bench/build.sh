#!/bin/bash
# Build the compiled benchmark of the 2-adic checker into lean/out/bench/bench (after lean/check.sh).
# Example, against c/orbit.c (same n mod 2^64, bit length and final context `1011` = context number 3):
#   out/bench/bench LC 0 19 65536 16        and        c/orbit 0 check 1048576
set -e
cd "$(dirname "$0")/../.."
LEANC="$(dirname "$LEAN")/leanc"
mkdir -p out/bench
export LEAN_PATH="$LEANLIB:$PWD/../../tools/lean/out:$PWD/out:$PWD/out/bench"
$LEAN Adic/bench/Dump.lean
(cd out/bench && $LEAN Tabs.lean -o Tabs.olean && $LEAN Tabs.lean -c Tabs.c)
$LEAN Adic/Basic.lean -c out/bench/Basic.c
$LEAN Adic/bench/Bench.lean -c out/bench/Bench.c
"$LEANC" -O3 out/bench/Bench.c out/bench/Tabs.c out/bench/Basic.c -o out/bench/bench
echo "built out/bench/bench"
