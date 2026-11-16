#!/usr/bin/env python3
"""The 32 abstract configurations of lean/RightEnd.lean (the list `S`), for 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE.

Only the last four cells (q-3 to q) and the state are kept.  With the head inside them: the state, the cells left of
the head inside the window (nearest first) and the cells from the head to q.  With the head further left: the four
cells only; the head comes back in any state a move right can produce.  A move right from q is allowed only in
state B on a 1 (then q moves two cells right, as in `tnext`).  Starting from `C>1 1` (step 2), the closure is
computed and printed as Lean.  `python3 py/rightend.py check` only reports its size and whether a bad move occurs.
"""
import sys
M = "1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE"
T = {}
for i, g in enumerate(M.split('_')):
    for r in (0, 1):
        t = g[3 * r:3 * r + 3]
        T[(i, r)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
RT = sorted({t[2] for t in T.values() if t and t[1] == 1})   # B, D, E, F
K = 4
start = ('in', 2, (0, 0), (1, 1))                           # C>1 1 with two blank cells left of it in the window
seen = {start}; todo = [start]; bad = []
def add(x):
    if x not in seen: seen.add(x); todo.append(x)
while todo:
    x = todo.pop()
    if x[0] == 'out':
        add(x)
        for s in RT: add(('in', s, (), x[1]))
        continue
    _, s, wl, u = x; a = u[0]; t = T[(s, a)]
    if t is None: continue
    b, d, s2 = t
    if d == -1:
        if not wl: add(('out', (b,) + u[1:]))
        else: add(('in', s2, wl[1:], (wl[0], b) + u[1:]))
    elif len(u) == 1:
        if not (s == 1 and a == 1): bad.append(x); continue
        add(('in', s2, ((b,) + wl)[:K - 2], (0, 0)))
    else: add(('in', s2, (b,) + wl, u[1:]))
ins = sorted(x[1:] for x in seen if x[0] == 'in'); outs = sorted(x[1] for x in seen if x[0] == 'out')
if len(sys.argv) > 1 and sys.argv[1] == 'check':
    print(f"{len(ins)} with the head in the window, {len(outs)} outside, {len(bad)} bad moves")
    for w in outs: print("outside:", ''.join(map(str, w)))
    sys.exit(1 if bad else 0)
bl = lambda x: '[' + ', '.join('true' if c else 'false' for c in x) + ']'
items = [f".inn .{'ABCDEF'[s]} {bl(wl)} {bl(u)}" for s, wl, u in ins] + [f".out {bl(w)}" for w in outs]
print("def S : List Ab := [\n  " + ",\n  ".join(items) + "]")
