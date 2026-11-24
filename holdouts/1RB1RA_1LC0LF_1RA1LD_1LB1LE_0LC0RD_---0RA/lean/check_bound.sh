#!/bin/bash
# The long check: Bound.lean (the run of c/wrun.c to visit 2,097,152, by native_decide on the faster model of
# Fast.lean), with compiled code loaded (tools/lean/check_native.sh).  About 15.5 hours of one core
# (Bound20.lean, to visit 1,048,576: 4.5 hours).  usage: check_bound.sh [FILE.lean...]
set -e
cd "$(dirname "$0")"
../../../tools/lean/check_native.sh . "Machine.lean Model.lean ModelWords.lean Sim.lean Fast.lean" "${@:-Bound.lean}"
