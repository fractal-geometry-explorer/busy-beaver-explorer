#!/bin/bash
# Build the Coq proof skeleton (run_ok admitted) and the extracted engine for this machine, start D of the table U.
# usage: BUSYCOQ=/path/to/busycoq/verify coq/build.sh PR93.v OUTDIR
# The scripts live in the folder of the start-A machine of the same table; see coq/README.md.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
U="$HERE/../../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/coq"
START=D M=1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF bash "$U/build.sh" "$1" "$2"
