#!/bin/bash
# Check the family's Lean files with the shared library (tools/lean).  LEAN, LEANLIB as for tools/lean/check.sh.
# About 6 minutes from scratch; Core/Ctx.lean is most of it (the 2-adic checker, Adic/, adds under a minute).
set -e
cd "$(dirname "$0")"
FILES=(Core/Machine.lean Core/Rules.lean Core/Defs.lean Core/Ctx.lean)
for v in VLC VLA VRB; do FILES+=($v/Machine.lean $v/Rules.lean $v/Map.lean); done
FILES+=(Machines/*.lean)
FILES+=(Adic/Basic.lean Adic/Link.lean Adic/VLC.lean Adic/VLA.lean Adic/VRB.lean Adic/Machines.lean Adic/Test.lean)
../../tools/lean/check.sh . "${FILES[@]}"
