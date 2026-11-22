#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean HaltPred.lean
# Tokens.lean, Total.lean and Need.lean (the token rules, the one-defect theorem, the fuel of a defect) live in the twin's folder.
S=../../1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF/lean
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
export LEAN_PATH="$LEANLIB:$(cd ../../../tools/lean && pwd)/out:$(pwd)/out"
O="$(pwd)/out"
for f in Tokens Total Need; do echo "== $S/$f.lean"; (cd $S && $LEAN $f.lean -o "$O/$f.olean"); done
echo "== Link.lean"; $LEAN Link.lean -o out/Link.olean
echo "ALL CHECKED"
