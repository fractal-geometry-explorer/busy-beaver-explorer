#!/bin/bash
# The return map below 2^62 by the kernel alone (Return62.lean and the pieces in R62/, written by return62.py).
# Checks the usual files first (check.sh), then the shards JOBS at a time (default 4; each needs up to ~2 GB), then
# Return62.lean.  About an hour of CPU, 17 minutes with 4 jobs.  LEAN, LEANLIB as for tools/lean/check.sh.
set -e
cd "$(dirname "$0")"
./check.sh
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
export LEAN LEAN_PATH="$LEANLIB:$(pwd)/../../tools/lean/out:$(pwd)/out"
mkdir -p out/R62
ls R62/Shard*.lean | sed 's/\.lean$//' | xargs -P "${JOBS:-4}" -I{} sh -c 'echo "== {}.lean"; "$LEAN" {}.lean -o out/{}.olean'
echo "== Return62.lean"
"$LEAN" Return62.lean -o out/Return62.olean
cat > out/Axioms62.lean <<'LEAN'
import Return62
#print axioms BB6d.returns_2_62_kernel
#print axioms BB6d.no_one_3e18_kernel
LEAN
"$LEAN" out/Axioms62.lean | tee out/axioms62.txt
if grep -q "native\|sorry" out/axioms62.txt; then echo "NOT KERNEL ONLY"; exit 1; fi
echo "ALL CHECKED"
