#!/bin/sh
# Generate and compile the Coq proofs that 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD--- (H155900.v, T4 from B) and
# 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE (H181655.v, T4 from A with the D0 detour) and
# 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC--- (H127983.v, T4 from C) halt.
# usage: sh build.sh /path/to/busycoq [fast]
#   Same checkout as ../build.sh. "fast" admits the final evaluations run_ok (about 30 s each instead of 30 minutes to 4 hours).
set -e
BC=${1:?give the path of a busycoq checkout}
HERE=$(cd "$(dirname "$0")" && pwd)
V="$BC/verify"
python3 "$HERE/mk.py" "$V/H155900.v" "$V/M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v" ${2:-full}
python3 "$HERE/lem.py" "$V/H155900.v"
python3 "$HERE/mkA.py" "$V/H155900.v" "$V/H181655.v" ${2:-full}
python3 "$HERE/mkC.py" "$V/H155900.v" "$V/H127983.v" ${2:-full}
cd "$V"
coqc -Q . BusyCoq H155900.v
coqc -Q . BusyCoq H181655.v
coqc -Q . BusyCoq H127983.v
