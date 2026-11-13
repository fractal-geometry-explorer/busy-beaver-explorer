"""Check that 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC carries its stream rigidly to the right.

usage:  gcc -O2 -o arrivals c/arrivals.c
        ./arrivals 1RB1LD_1RC0RC_1LD0RE_0LB0LA_0RF1LA_---1RC 120000000 1000 -1000 100000000 | python3 py/check_translation.py

For each pair of consecutive arrivals of the head at the right end, finds the smallest cell B such that the new tape
from B + shift on equals the old tape from B on (shift = the growth of the tape), and prints the shifts seen and the
range of B.
"""
import collections
import sys

tapes = [line.split()[3].replace(">", "") for line in sys.stdin if len(line.split()) == 4]
shifts, bs = collections.Counter(), []
for t1, t2 in zip(tapes, tapes[1:]):
    sh = len(t2) - len(t1)
    b = len(t1)
    while b > 0 and t1[b - 1] == t2[b - 1 + sh]:
        b -= 1
    shifts[sh] += 1
    bs.append(b)
print(f"{len(bs)} round trips; growth per round trip: {dict(shifts)}; the tape from cell {min(bs)}-{max(bs)} on "
      f"is the previous tape shifted (widths {len(tapes[0])}-{len(tapes[-1])})")
