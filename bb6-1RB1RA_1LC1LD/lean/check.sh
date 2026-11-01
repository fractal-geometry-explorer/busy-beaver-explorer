#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../tools/lean/check.sh . Machine.lean Blank.lean EdgeCert.lean Edge.lean Rules.lean Macro.lean Blocks.lean Recur.lean Finish.lean Formula.lean Offset.lean OffsetData.lean Stops.lean Chain.lean CaseB.lean Bound.lean Count.lean Axioms.lean
# OffsetData.lean is written by OffsetGen.lean: check that it is up to date
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
LEAN_PATH="$LEANLIB:$PWD/../../tools/lean/out:$PWD/out" $LEAN --run OffsetGen.lean | cmp - OffsetData.lean
echo "OffsetData.lean is up to date"
