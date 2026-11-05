#!/bin/bash
# Check the wall-building top pieces TopWall*.lean (written by top_gen.py), after the files they import.  Each file
# is compiled in its own Lean process; JOBS (default 1) of them at a time.  LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean Counter.lean Wall.lean Top.lean
export LEAN_PATH="$LEANLIB:$(cd ../../tools/lean && pwd)/out:$(pwd)/out"
ls TopWall*.lean | sort -V | xargs -P "${JOBS:-1}" -I{} sh -c \
  'echo "== {}"; '"$LEAN"' {} -o out/$(basename {} .lean).olean || { echo "FAILED {}"; exit 255; }'
echo "== AxiomsWall.lean"
$LEAN AxiomsWall.lean -o out/AxiomsWall.olean
echo "ALL CHECKED"
