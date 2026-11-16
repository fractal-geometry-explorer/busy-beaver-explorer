"""Which lists are one or two visits away from a halt?  Enumeration over small lists of the domain D.

Claims checked (for all lists of D with at most LEN runs, each at most MAX):
  * visit(l) is all even (the next visit halts) exactly for  l = [X, 1]  or  l = [X, 4, odd, odd, even, ..., even];
  * no list of D is mapped to [X, 1] except [X-6, 3], and none is mapped to [X, 3].
So, since the orbit of the machine does not start at [X, 1] or [X, 3], it halts iff it reaches a list
[X, 4, odd, odd, even, ..., even]: two odd runs side by side, a 4 before them and only even runs elsewhere.

usage: python3 last_step.py [LEN [MAX]]      (default 6 13)
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from visit import visit, inD

LEN = int(sys.argv[1]) if len(sys.argv) > 1 else 6
MAX = int(sys.argv[2]) if len(sys.argv) > 2 else 13
vals = [v for v in range(1, MAX + 1) if v != 2]
n = 0; last = 0; pre1 = set(); pre3 = set()
for k in range(1, LEN + 1):
    for tail in itertools.product(vals, repeat=k - 1):
        for x in (6, 12, 14, 16, 18, 20, 22):
            l = [x] + list(tail)
            if not inD(l): continue
            n += 1
            r = visit(l)
            if r is None: continue
            allev = all(v % 2 == 0 for v in r)
            form = (len(l) == 2 and l[1] == 1) or (len(l) >= 4 and l[1] == 4 and l[2] % 2 and l[3] % 2
                                                    and all(v % 2 == 0 for v in l[4:]))
            assert allev == form, (l, r)
            last += allev
            if len(r) == 2 and r[1] == 1: assert l == [r[0] - 6, 3], (l, r); pre1.add(tuple(l))
            assert not (len(r) == 2 and r[1] == 3), (l, r)
print("lists of D checked:", n, "| one visit before a halt:", last, "| mapped to [X, 1]:", sorted(pre1))
