#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../tools/lean/check.sh . Machine.lean Rules.lean Blank.lean Macro.lean MacroRun.lean Wave.lean WaveTime.lean Cascade.lean CascadeRun.lean Cycles.lean Axioms.lean
