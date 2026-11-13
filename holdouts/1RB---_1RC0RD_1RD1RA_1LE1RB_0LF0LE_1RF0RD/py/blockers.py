"""Blockers at the overflows of the (trusted) macro map of macro.py.

A blocker is a pair of bits of the remainder R (pairs from the lowest bit) whose low bit is 0; the halting case
needs R without blockers.  Prints, every STEP overflows, M and the number of blockers, then how many overflows had
fewer than 20, and how many have the top M - j0 bits of R all 1 (j0 = j at the start of the phase).
usage: python3 blockers.py OVERFLOWS [STEP]     (20000 overflows: about 10 minutes)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from macro import phases  # noqa: E402

n = int(sys.argv[1])
step = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
few = top = 0
for i, (t, j, M, R, new) in enumerate(phases(0, 2, 1, n)):
    s = format(R, f"0{M}b")[::-1]
    b = s[0::2].count("0")
    few += b < 20
    j0 = j - t
    top += j >= M and (R >> j0) == (1 << (M - j0)) - 1
    if i % step == 0:
        print(f"overflow {i}: M = {M}, blockers = {b}")
print(f"{n} overflows: {few} with fewer than 20 blockers; top bits all 1 at {top}")
