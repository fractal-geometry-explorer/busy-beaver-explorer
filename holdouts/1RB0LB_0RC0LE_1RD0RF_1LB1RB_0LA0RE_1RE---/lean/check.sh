#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Events.lean Visit.lean
# VisitLaw.lean and VisitCheck.lean are shared: they live in the twin machine's folder.
S=../../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
export LEAN_PATH="$LEANLIB:$(cd ../../../tools/lean && pwd)/out:$(pwd)/out"
O="$(pwd)/out"
for f in VisitLaw VisitCheck; do echo "== $S/$f.lean"; (cd $S && $LEAN $f.lean -o "$O/$f.olean"); done
echo "== Law.lean"; $LEAN Law.lean -o out/Law.olean
echo "ALL CHECKED"
