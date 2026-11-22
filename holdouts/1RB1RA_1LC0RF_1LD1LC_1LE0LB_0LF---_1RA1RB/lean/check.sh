#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh. Route.lean
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Shifts.lean Route.lean Blocks.lean P75625/Machine.lean P75625/Pascal.lean P75625/Lucas.lean P75625/Absorb.lean P75625/Wall.lean P75625/Crossing.lean P75625/End.lean P75625/Race.lean Fail.lean Mirror.lean
