"""Check the three-block transfer of 1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA on the plain run.

Reads `hturn MACHINE STEPS 6` output (see septurns.py) and looks at the turns in state A after a rightward move
where the tape around the head reads

    (110)^x 0 (110)^y 1 A> 1 0 1 0 1 1 0 0 (110)^z 0

For two such turns in a row at the same place it prints the change of (x, y, z) and the steps between them, and
fits the step count as a linear function of x, y and z.

usage: hturn M STEPS 6 | python3 transfer.py
"""
import collections
import re
import sys

pat = re.compile(r'((?:110)+)0((?:110)+)1>10101100((?:110)*)0')
prev = None
count = collections.Counter()
rows = []
for line in sys.stdin:
    f = line.split()
    if len(f) < 6 or f[1] != 'R' or f[2] != 'A':
        continue
    s, t = int(f[0]), f[5]
    m = pat.search(t)
    if not m:
        prev = None
        continue
    x, y, z = (len(g) // 3 for g in m.groups())
    if prev and prev[0] == m.start():
        count[(x - prev[1], y - prev[2], z - prev[3])] += 1
        rows.append((s - prev[4], prev[1], prev[2], prev[3]))
    prev = (m.start(), x, y, z, s)
for k, v in count.most_common():
    print(f'{v} cycles with (dx, dy, dz) = {k}')
bad = [r for r in rows if r[0] != 28 * r[2] + 111]
print(f'{len(rows) - len(bad)} of {len(rows)} cycles take exactly 28y + 111 steps')
