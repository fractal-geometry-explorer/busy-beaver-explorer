#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Sweep.lean Reduce.lean OrbitRun.lean Xor.lean Bits.lean Zone.lean ZoneRun.lean Cascade.lean ZoneCascade.lean Window.lean WindowRun.lean Axioms.lean
