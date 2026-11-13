"""Phases of 1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE.

usage (from the repo root):
  gcc -O2 -o /tmp/tmrun tools/c/tmrun.c
  /tmp/tmrun 1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE 1000000000 records 100000 > /tmp/rec.txt
  python3 holdouts/1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE/py/phases.py /tmp/rec.txt

Takes the moments the head extends the tape on the other side from the last extension.  At the right end the tape
is a solid block 1^m followed by an alternating stretch of r cells; at the left end it is an alternating stretch,
`0 0`, and a solid block at the right end.  Checks that the left phase keeps m and prints its cost / (m r), and the
sequence of m.
"""
import re
import sys


def cells_of(body):
    c = []
    for k in body.split():
        if ">" in k:
            continue
        if "^" in k:
            a, b = k.split("^")
            c += [int(a)] * int(b)
        else:
            c.append(int(k))
    return c


prev, ev = None, []
for line in open(sys.argv[1]):
    t = line.split()
    if len(t) < 4 or not t[0].isdigit():
        continue
    if t[1] != prev:
        c = cells_of(" ".join(t[3:]))
        if t[1] == "R":
            i = 0
            while i < len(c) and c[i] == 1:
                i += 1
            ev.append((int(t[0]), "R", i, len(c) - i, "".join(map(str, c[i:]))))
        else:
            j = len(c)
            while j > 0 and c[j - 1] == 1:
                j -= 1
            ev.append((int(t[0]), "L", len(c) - j, j, "".join(map(str, c[:j]))))
    prev = t[1]
ev = [e for e in ev if e[0] > 10000]
shapes = {e[1] + ":" + re.sub(r"(10)+|(01)+", "*", e[4]) for e in ev}
keep = sum(1 for a, b in zip(ev, ev[1:]) if a[1] == "R" and b[1] == "L" and a[2] == b[2])
pairs = sum(1 for a, b in zip(ev, ev[1:]) if a[1] == "R" and b[1] == "L")
cost = [(b[0] - a[0]) / (a[2] * a[3]) for a, b in zip(ev, ev[1:]) if a[1] == "R" and b[1] == "L"]
print(f"side switches after step 10^4: {len(ev)}; tape shapes (* = alternating run): {sorted(shapes)}")
print(f"left phases keeping the solid block: {keep} of {pairs}; cost/(m r), last 8: {[round(x, 3) for x in cost[-8:]]}")
print("solid block m at the last right-end visits:", [e[2] for e in ev if e[1] == "R"][-16:])
