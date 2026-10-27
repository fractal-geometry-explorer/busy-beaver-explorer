#!/bin/bash
# Check PassMaps.lean, DQ.lean and GmmMaps.lean (needs the compiled BB6 oleans: run ../../lean/check.sh first).
# usage: source /etc/profile.d/lean.sh; ./check.sh
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
export LEAN_PATH="$LEANLIB:$(cd ../../lean && pwd)/out"
echo "== PassMaps.lean"; time $LEAN PassMaps.lean
echo "== DQ.lean"; time $LEAN DQ.lean
echo "== GmmMaps.lean"; time $LEAN GmmMaps.lean
