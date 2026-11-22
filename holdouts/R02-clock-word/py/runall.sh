#!/bin/sh
# long exact accelerated runs of the R02 clock machines (phase lines; HALT if one halts)
cd "$(dirname "$0")/.."
printf '%s\n' "$@" | xargs -P ${PAR:-2} -I{} sh -c 'ulimit -v ${VMEM:-5000000}; timeout ${TMAX:-14400} python3 py/runx.py {} run 100000 > out/run_{}.txt 2>&1'
