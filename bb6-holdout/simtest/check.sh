#!/bin/bash
# Build the simulator drivers and run the differential test against the proved model (Oracle.lean).
# usage: LEAN=/path/to/lean LEANLIB=/path/to/lib/lean ./check.sh [N SEED ROUNDS]   (../lean/check.sh must have run)
set -e
cd "$(dirname "$0")"
N=${1:-20000}; SEED=${2:-1}; NR=${3:-12}
B=${BUILD:-build}; mkdir -p $B; C=../csearch
for e in nrefdfs2 lined; do gcc -O2 -w -DENGINE="\"$C/$e.c\"" -o $B/$e drv_q.c -lm; done
for e in rtree3d rtree3e; do gcc -O2 -w -DENGINE="\"$C/$e.c\"" -o $B/$e drv_f.c -lm; done
gcc -O2 -w -DENGINE="\"$C/gx3.c\"" -o $B/gx3 drv_gx.c -lm
export LEAN_PATH="$LEANLIB:$PWD/../lean/out"
python3 run.py $N $SEED $NR \
  nrefdfs2="$B/nrefdfs2 $NR" lined="$B/lined $NR" rtree3d="$B/rtree3d $NR" rtree3e="$B/rtree3e $NR" gx3="$B/gx3 $NR" \
  endgame="python3 pysim.py ../cert/check_endgame.py $NR" exit="python3 pysim.py ../cert/check_exit.py $NR" \
  tree="python3 pysim.py ../cert/check_tree.py $NR" \
  stepper="node stepper.js $NR" machine="node stepper.js $NR machine"
