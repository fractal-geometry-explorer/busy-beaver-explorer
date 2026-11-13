"""The far end of the list.  Reads the P1 rows of c/rword.c ("step n word") on stdin and collects the far-end
suffixes: what follows the last block of 10 or more copies of v.  Then it closes that set under a borrow arriving at
the far end: the machine is run from 0^inf 1110 (111110)^12 1 A> v^50 s v^60 SUFFIX (an s-separator, so the borrow
passes into the last block).  It prints the size of the closure, whether any suffix of it halts, and where each
observed suffix ends up.  Also prints which short suffixes make the machine halt when a borrow arrives.

usage: rword MACHINE STEPS | awk '$2%2==0' | python3 farend.py
"""
import itertools
import os
import re
import sys
from collections import deque, Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import macro as M  # noqa: E402

B = 60


def suffix(bits):
    xs, ss, tail = M.tokenize(bits)
    ks = [i for i, x in enumerate(xs) if x >= 10]
    if not ks: return None
    k = ks[-1]
    return M.tostr([0] + xs[k + 1:], ss[k:], tail)


def arrive(S):
    return M.oracle(12, '010' * 50 + '1' + '010' * B + S, 10 ** 6)


def main():
    obs = Counter()
    for line in sys.stdin:
        a = line.split()
        w = a[2] if len(a) > 2 else ''
        big = [m for m in re.finditer(r'<(\d+)>', w) if int(m.group(1)) >= 10]
        if not big: continue
        m = big[-1]
        S = suffix('010' * 10 + re.sub(r'<(\d+)>', lambda m: '010' * int(m.group(1)), w[m.end():]))
        if S is not None: obs[S] += 1
    G = {}; Q = deque(obs); halts = []
    while Q:
        S = Q.popleft()
        if S in G: continue
        r = arrive(S)
        if r is None or r[0] == 'HALT':
            G[S] = r; halts.append(S); continue
        G[S] = suffix(r[1]); Q.append(G[S])
    print('%d far-end suffixes seen, %d in the closure under arrivals, halting: %s' % (len(obs), len(G), halts))
    ends = Counter()
    for S in obs:
        seen = set()
        while S not in seen and S not in halts:
            seen.add(S); S = G[S]
        ends[S] += 1
    print('each seen suffix runs into a cycle through:', dict(ends))
    bad = []
    for L in range(0, 9):
        for t in map(''.join, itertools.product('01', repeat=L)):
            if t.startswith('010'): continue
            r = arrive(t)
            if r is not None and r[0] == 'HALT': bad.append(t)
    print('suffixes of up to 8 bits that halt when a borrow arrives:', bad)


if __name__ == '__main__':
    main()
