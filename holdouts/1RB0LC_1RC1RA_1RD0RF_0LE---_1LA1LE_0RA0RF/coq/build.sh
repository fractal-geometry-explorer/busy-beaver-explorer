#!/bin/bash
# Build the Coq proof skeleton (run_ok admitted) and the extracted engine for this machine, start B of the table U.
# usage: BUSYCOQ=/path/to/busycoq/verify coq/build.sh PR93.v OUTDIR
# The scripts live in the folder of the start-A machine of the same table; see coq/README.md.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
U="$HERE/../../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/coq"
START=B M=1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF bash "$U/build.sh" "$1" "$2"
