"""How close the run of a machine comes to halting: at every step, the smallest d such that the configuration
matches a pattern from which the machine halts in exactly d steps (backward.py), for d <= DEPTH.

usage: python3 near_miss.py MACHINE DEPTH STEPS"""
import sys
from collections import defaultdict

m, DEPTH, STEPS = sys.argv[1], int(sys.argv[2]), int(float(sys.argv[3]))
T = {}
for s, g in enumerate(m.split("_")):
    for y in (0, 1):
        x = g[3 * y:3 * y + 3]
        T[(s, y)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, "ABCDEF".index(x[2]))
layer = set((s, ((0, y),)) for (s, y), tr in T.items() if tr is None)
seen = set(layer)
pats = defaultdict(list)      # (state, head symbol) -> [(depth, cells)]
for x in layer:
    pats[(x[0], dict(x[1])[0])].append((0, x[1]))
for d in range(1, DEPTH + 1):
    new = set()
    for st, cells in layer:
        c = dict(cells)
        for (p, b), tr in T.items():
            if tr is None or tr[2] != st:
                continue
            w, dirn, q = tr
            pos = -dirn
            if pos in c and c[pos] != w:
                continue
            c2 = dict(c)
            c2[pos] = b
            x = (p, tuple(sorted((k - pos, v) for k, v in c2.items())))
            if x not in seen:
                seen.add(x)
                new.add(x)
                pats[(p, b)].append((d, x[1]))
    layer = new
for k in pats:
    pats[k].sort()
tp = defaultdict(int)
pos = st = 0
best = {}
for t in range(STEPS):
    for d, cells in pats[(st, tp[pos])]:
        if all(tp[pos + k] == v for k, v in cells):
            if d not in best:
                best[d] = (t, cells)
            break
    tr = T[(st, tp[pos])]
    if tr is None:
        print("HALT", t)
        break
    tp[pos], dd, st = tr
    pos += dd
for d in sorted(best):
    print("depth", d, "first at step", best[d][0])
