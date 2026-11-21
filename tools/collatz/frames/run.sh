#!/bin/bash
# Build and run the frame-map hunts.  usage: tools/collatz/frames/run.sh [MAXFRAMES]   (default 1e12)
set -e
cd "$(dirname "$0")"
N=${1:-1e12}
python3 gen.py 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE > 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE.h
python3 gen.py 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD > 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD.h
gcc -O2 -DRULES="\"1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE.h\"" -DSTART_C=4 -DSTART_A='{0,1,0}' -o /tmp/frames_a frames.c   # start Ph.g 0 1
gcc -O2 -DRULES="\"1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD.h\"" -DSTART_C=0 -DSTART_A='{0,0,2}' -o /tmp/frames_b frames.c  # start Ph.z 0 0 2
echo "== 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE"; /tmp/frames_a "$N" || true
echo "== 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD"; /tmp/frames_b "$N" || true
