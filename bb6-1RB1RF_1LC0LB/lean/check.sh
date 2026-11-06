#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
# The wall-building top pieces (TopWall*.lean) take longer and are checked by check_wall.sh.
set -e
cd "$(dirname "$0")"
../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Counter.lean Wall.lean Seq.lean Top.lean TopFam.lean Axioms.lean
