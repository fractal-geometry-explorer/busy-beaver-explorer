#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Unwind.lean HaltIff.lean Sweeps.lean PassTail.lean PassRules.lean PassRel.lean
