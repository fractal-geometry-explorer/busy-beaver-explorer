#!/bin/sh
# Generate and compile the Coq proof that 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD--- halts.
# usage: sh build.sh /path/to/busycoq [fast]
#   Same checkout as ../build.sh. "fast" admits the final evaluation run_ok (about 30 s instead of the full run).
set -e
BC=${1:?give the path of a busycoq checkout}
HERE=$(cd "$(dirname "$0")" && pwd)
V="$BC/verify"
python3 "$HERE/mk.py" "$V/H155900.v" "$V/M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v" ${2:-full}
python3 "$HERE/lem.py" "$V/H155900.v"
cd "$V"
coqc -Q . BusyCoq -Q ./BigInt BigInt H155900.v
