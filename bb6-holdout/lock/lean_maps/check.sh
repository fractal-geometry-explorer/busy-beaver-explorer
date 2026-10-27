#!/bin/bash
# Check PassMaps.lean and DQ.lean (needs the compiled BB6 oleans: run ../../lean/check.sh first).
# usage: source /etc/profile.d/lean.sh; ./check.sh [kernel]
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
export LEAN_PATH="$LEANLIB:$(cd ../../lean && pwd)/out"
echo "== PassMaps.lean"; time $LEAN PassMaps.lean
if [ "$1" = kernel ]; then echo "== PassMapsKernel.lean (about 5 min)"; time $LEAN PassMapsKernel.lean; fi
echo "== DQ.lean"; time $LEAN DQ.lean
