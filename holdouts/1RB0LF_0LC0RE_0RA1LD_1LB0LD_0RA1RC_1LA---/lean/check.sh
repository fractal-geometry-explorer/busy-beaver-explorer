#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Gadgets.lean Macro.lean Rules.lean Seq.lean Sweep.lean Twin29537.lean RulesTwin1.lean RulesTwin2.lean ResetMapRuns.lean ResetMap.lean ExcSim.lean ResetExc.lean
./check_native.sh ResetExcRuns.lean
