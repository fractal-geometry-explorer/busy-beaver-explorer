#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
# The proofs of the front's case tree are generated first (py/gen_cases.py, about 3 minutes; 7.8 MB of Lean, so not
# committed) into Cases/, one file per group. The groups are independent of each other, so they are compiled in
# parallel (JOBS at a time, default the number of cores).
set -e
cd "$(dirname "$0")"
python3 ../py/gen_cases.py .
../../../tools/lean/check.sh . Machine.lean Blank.lean Rounds.lean Subround.lean Collapse.lean Run.lean Pass.lean General.lean Transient.lean Counter.lean Advance.lean Frame.lean Bits.lean Map.lean MapRun.lean Front.lean FrontCases.lean FrontLib.lean Cases/Defs.lean
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
export LEAN LEAN_PATH="$LEANLIB:$(cd ../../../tools/lean && pwd)/out:$PWD/out"
mkdir -p out/Cases
xargs -P "${JOBS:-$(nproc)}" -I{} sh -c 'echo "== {}"; "$LEAN" "{}" -o "out/$(echo {} | sed "s/\.lean$//").olean"' < Cases/list.txt
echo "== Cases.lean"
"$LEAN" Cases.lean -o out/Cases.olean
echo "ALL CASES CHECKED"
