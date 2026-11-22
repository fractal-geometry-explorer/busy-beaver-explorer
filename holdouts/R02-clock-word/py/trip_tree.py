"""Trips of 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB decided by a prefix of the word.

A trip starts at `0 0 0 1 1 A> W` (the head may never go left of the region; doing so is an exit).  For a prefix u,
the trip is run with only u known; if it returns (`E> 1 1 1 1 0` at the region start), exits or halts without reading
past u, the prefix decides it, otherwise u is extended by 0 and by 1.  Prints the decided outcomes and the number of
prefixes of length D still undecided.

usage: python3 trip_tree.py D"""
import sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from clockx import clock

T = clock.table("1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB")
MAXD = int(sys.argv[1])


def sim(u):
    tp = dict(enumerate([0, 0, 0, 1, 1] + u))
    pos, st, L = 5, 0, 5 + len(u)
    for t in range(10 ** 7):
        if pos == 0 and st == 4 and [tp.get(i, 0) for i in range(5)] == [1, 1, 1, 1, 0]:
            return "return", t
        if pos < 0:
            return "exit " + "ABCDEF"[st] + "".join(str(tp.get(i, 0)) for i in range(6)), t
        if pos >= L:
            return "need", t
        tr = T[(st, tp.get(pos, 0))]
        if tr is None:
            return "HALT", t
        tp[pos], d, st = tr
        pos += d
    return "limit", 0


leaves, undecided, longest = Counter(), 0, 0
stack = [[]]
while stack:
    u = stack.pop()
    r, t = sim(u)
    if r == "need":
        if len(u) >= MAXD:
            undecided += 1
        else:
            stack += [u + [0], u + [1]]
        continue
    leaves[r] += 1
    longest = max(longest, t)
for k, v in sorted(leaves.items(), key=lambda x: -x[1]):
    print(v, k)
print("undecided prefixes of length %d: %d; longest decided trip %d steps" % (MAXD, undecided, longest))
