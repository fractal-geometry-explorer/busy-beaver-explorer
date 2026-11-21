#!/bin/bash
# The return map below 2^74 by the kernel alone (Return74.lean and the pieces in R74/, written by return62.py 12000 16 74).
# Checks the usual files first (check.sh), then the shards JOBS at a time (default 4; each needs up to 4.3 GB, so use 3
# on a 16 GB machine), then Return74.lean.  About 4 hours of CPU, about an hour with 4 jobs.  LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
./check.sh
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
export LEAN LEAN_PATH="$LEANLIB:$(pwd)/../../tools/lean/out:$(pwd)/out"
mkdir -p out/R74
ls R74/Shard*.lean | sed 's/\.lean$//' | xargs -P "${JOBS:-4}" -I{} sh -c 'echo "== {}.lean"; "$LEAN" {}.lean -o out/{}.olean'
echo "== Return74.lean"
"$LEAN" Return74.lean -o out/Return74.olean
echo "== Replay74.lean"
"$LEAN" Replay74.lean -o out/Replay74.olean
cat > out/Axioms74.lean <<'LEAN'
import Return74
import Replay74
#print axioms BB6d.returns_2_74_kernel
#print axioms BB6d.replay_1e22_kernel
#print axioms BB6d.no_one_1e22_kernel
LEAN
"$LEAN" out/Axioms74.lean | tee out/axioms74.txt
if grep -q "native\|sorry" out/axioms74.txt; then echo "NOT KERNEL ONLY"; exit 1; fi
echo "ALL CHECKED"
