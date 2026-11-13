#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Chain.lean Deep/u1_one.lean Deep/u1_two.lean Deep/u2_one.lean Deep/u2_two.lean Deep/u3_one.lean Deep/u3_two.lean
