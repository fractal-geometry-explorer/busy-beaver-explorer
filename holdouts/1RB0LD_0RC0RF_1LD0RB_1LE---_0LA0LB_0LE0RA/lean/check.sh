#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
# Written by py/replay/gen.py.  The 8 class checks (Check*.lean, native_decide) run in parallel, JOBS at a time.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean MachineM.lean Exec.lean Pieces.lean \
  Decode.lean ExecData.lean Data.lean Arrive.lean
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
export LEAN_PATH="$LEANLIB:../../../tools/lean/out:$(pwd)/out"
JOBS=${JOBS:-$(nproc)}
ls Check*.lean | xargs -P "$JOBS" -I{} sh -c 'echo "== {}"; $0 {} -o out/$(basename {} .lean).olean' "$LEAN"
for f in Replay Mirror Final; do echo "== $f.lean"; $LEAN $f.lean -o out/$f.olean; done
echo "ALL CHECKED"
