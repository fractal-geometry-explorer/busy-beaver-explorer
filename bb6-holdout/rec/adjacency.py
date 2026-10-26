"""Pair counts between consecutive marks in the abstract states (insertion grammar), to see which adjacencies occur."""
from absim2 import round_step
from collections import defaultdict
LEN = {'G': 2, 'W': 1, 'M': 1, 'B': 2}
def ip(t, p): return p + 1 if t in 'GW' else p
def gaps(w, marks):
    out = []
    prev = ('S', 0, 0)   # content start: the first pair "1 0" ends at insertion point 2
    pt, pip, plen = 'S', 2, 0
    for t, p in marks:
        a2 = ip(t, p) - pip - plen
        out.append((pt, t, a2))
        pt, pip, plen = t, ip(t, p), LEN[t]
    # end: content ends at w-1. For an end marker M(w-2): insertion at w-2, then "1" then blank.
    out.append((pt, 'END', w - (pip + plen)))
    return out
mins = defaultdict(lambda: 10**9); odd = set(); seen = defaultdict(int)
def scan(n, maxr=500):
    w = 2 * n + 6; marks = [('G', 1), ('M', w - 2)]
    for r in range(maxr):
        for a, b, d in gaps(w, marks):
            if d % 2: odd.add((a, b, d))
            mins[a, b] = min(mins[a, b], d // 2); seen[a, b] += 1
        w, marks = round_step(w, marks)
        if len(marks) == 2 and marks[1] == ('M', w - 2): return
for n in range(2, 300000, 3): scan(n)
for k in sorted(mins): print(k, 'min pairs', mins[k], 'count', seen[k])
print('odd gaps:', sorted(odd)[:20])
