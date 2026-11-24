#!/bin/bash
# The long check: Bound.lean (the run of c/wrun.c to visit 2,097,152, by native_decide on the faster model of
# Fast.lean), with compiled code loaded (tools/lean/check_native.sh).  About ten hours of one core.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check_native.sh . "Machine.lean Model.lean ModelWords.lean Sim.lean Fast.lean" Bound.lean
