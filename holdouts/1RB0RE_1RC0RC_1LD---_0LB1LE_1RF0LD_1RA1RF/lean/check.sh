#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh. Route.lean
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Twin.lean Route.lean watch/Machine.lean watch/Pascal.lean watch/Absorb.lean watch/Wall.lean watch/Crossing.lean watch/End.lean watch/Race.lean NoBreak.lean
