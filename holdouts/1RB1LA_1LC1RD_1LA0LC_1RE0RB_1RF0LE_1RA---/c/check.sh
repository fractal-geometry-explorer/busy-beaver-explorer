#!/bin/sh
# Compare c/fq.c with the Python transcription of F (py/F25.py) on the first 3,000 rounds of both
# machines and a few other starts (L and X mod 2^61-1 every round), then run 10^7 rounds.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
T=$(mktemp -d)
gcc -O2 -o "$T/fq" "$HERE/fq.c"
for s in "8 145" "1 3" "3 5" "4 16" "6 64" "9 300"; do
  set -- $s
  python3 - "$HERE/../py" $1 $2 <<'PY' > "$T/ref.txt"
import sys; sys.path.insert(0, sys.argv[1]); from F25 import F
L, X = int(sys.argv[2]), int(sys.argv[3]); MP = (1 << 61) - 1
for t in range(3000):
    print(t, L, X % MP); r = F(L, X)
    if r is None: print("HALT in round", t, "L=%d" % L); break
    L, X = r
PY
  "$T/fq" $1 $2 3000 0 1 2>/dev/null | head -n "$(wc -l < "$T/ref.txt")" > "$T/c.txt"
  cmp "$T/ref.txt" "$T/c.txt" && echo "F($1, $2): 3000 rounds agree with py/F25.py"
done
"$T/fq" 8 145 10000000 0 2>/dev/null
rm -rf "$T"
