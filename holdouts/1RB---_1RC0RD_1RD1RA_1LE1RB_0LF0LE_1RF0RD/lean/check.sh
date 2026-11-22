#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Shapes.lean Count.lean Bits.lean Junction.lean Overflow.lean Phase.lean Orbit.lean OrbitCheck.lean Invariant.lean Start.lean Family.lean Converse.lean Landing.lean
