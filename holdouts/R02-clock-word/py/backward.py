"""Backward reasoning from the halt of a machine: the local patterns (cells around the head, '?' unknown) from
which the machine halts within d steps, for d = 0..DEPTH.  Prints the number of patterns per depth and the
shortest ones.

usage: python3 backward.py MACHINE DEPTH [SHOW]"""
import sys

m = sys.argv[1]
DEPTH = int(sys.argv[2])
SHOW = int(sys.argv[3]) if len(sys.argv) > 3 else 5
T = {}
for s, g in enumerate(m.split("_")):
    for y in (0, 1):
        x = g[3 * y:3 * y + 3]
        T[(s, y)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, s if False else "ABCDEF".index(x[2]))

# a pattern: (state, cells dict offset->bit relative to head)
start = []
for (s, y), tr in T.items():
    if tr is None:
        start.append((s, ((0, y),)))
layer = set(start)
seen = set(layer)
for d in range(1, DEPTH + 1):
    new = set()
    for st, cells in layer:
        c = dict(cells)
        # predecessor: state p reading b at position -dir, wrote w there, moved by dir to 0, now in st
        for (p, b), tr in T.items():
            if tr is None:
                continue
            w, dirn, q = tr
            if q != st:
                continue
            pos = -dirn                       # where the head was
            if pos in c and c[pos] != w:
                continue
            c2 = dict(c)
            c2[pos] = b
            # shift so the head is at 0
            pat = tuple(sorted((k - pos, v) for k, v in c2.items()))
            x = (p, pat)
            if x not in seen:
                seen.add(x)
                new.add(x)
    layer = new
    def show(x):
        st, cells = x
        lo, hi = min(k for k, _ in cells), max(k for k, _ in cells)
        cc = dict(cells)
        return " ".join(("ABCDEF"[st] + ">" if k == 0 else "") + str(cc.get(k, "?")) for k in range(lo, hi + 1))
    print(d, len(layer), " | ".join(show(x) for x in sorted(layer, key=lambda x: len(x[1]))[:SHOW]), flush=True)
    if not layer:
        print("backward reasoning closes at depth", d)
        break
