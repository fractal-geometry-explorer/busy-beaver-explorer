"""What a closed set of walls of 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC has to contain (free parities, the
counter-stack model of stackmodel.py; walls bottom first here).  See README, "A closed set of walls (24 November)".

usage (from this directory):
  python3 closed.py family I        the signals 1 (01)^(2i) 1 1 1 lead from the wall 1 to 1 K(0) K(9i + 7), i < I
                                    (lean/Closed.lean proves it for every i)
  python3 closed.py bad B           start values k < 2^B over K(0) whose odd run makes a count negative
  python3 closed.py families D B    breadth first to depth D under free parities: every lower stack with an open
                                    counter on top, the top counts that occur over it (as an arithmetic progression),
                                    and whether any member of the progression is a bad start value below 2^B
"""
import os
import sys
from math import gcd
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from stackmodel import step  # noqa: E402
from pairs import cert, brute, orbit  # noqa: E402

sys.setrecursionlimit(100000)


def run(lv, ss):
    for s in ss:
        r = step(lv, s)
        if r is None:
            return None
        lv = r[0]
    return lv


def family(I):
    for i in range(I):
        w = run([], [1] + [0, 1] * (2 * i) + [1, 1, 1])
        assert w == [(0, False), (9 * i + 7, False)], (i, w)
    print(f"1 (01)^(2i) 1 1 1 gives 1 K(0) K(9i + 7) for i < {I}")


def bad(B):
    oms, _ = orbit(0, B + 80)
    mb, flag = cert(oms, 0, B)
    small = brute(oms, 0, mb + 1, B + 60)
    print(f"over K(0), start values below 2^{B}: largest bad {mb}, all bad: {small}, FLAG {flag}")
    print("members 9i + 7 among them:", [k for k in small if k % 9 == 7])


def oms_of(V, n):
    V, out = list(V), []
    for _ in range(n):
        r = step(V, 1)
        if r is None:
            return None
        V = r[0]
        out.append(r[1])
    return out


def families(D, B):
    front, seen = {()}, {()}
    for _ in range(D):
        nxt = set()
        for lv in front:
            for s in (0, 1):
                r = step(list(lv), s)
                if r is None:
                    print("a count goes negative at", lv, s)
                    return
                t = tuple(r[0])
                if t not in seen:
                    seen.add(t)
                    nxt.add(t)
        front = nxt
    tops = defaultdict(list)
    for t in seen:
        if len(t) >= 2 and not t[-1][1] and not t[-2][1]:
            tops[t[:-1]].append(t[-1][0])
    rows, hits = [], []
    for V, ks in tops.items():
        if len(ks) < 8:
            continue
        ks.sort()
        d = 0
        for k in ks:
            d = gcd(d, k - ks[0])
        o = oms_of(V, B + 80)
        mb, flag = cert(o, 0, B)
        bad_ks = brute(o, 0, mb + 1, B + 60) if mb else []
        h = [k for k in bad_ks if k >= ks[0] and d and (k - ks[0]) % d == 0]
        rows.append((mb, V, ks[0], d, len(ks)))
        if h or flag:
            hits.append((V, h, flag))
    rows.sort(reverse=True)
    print(f"{len(seen)} walls to depth {D}; {len(rows)} lower stacks with at least 8 top counts over them")
    for mb, V, k0, d, n in rows[:10]:
        print(f"  lower stack {V}: {n} tops, from {k0} in steps of {d}; largest bad start value below 2^{B}: {mb}")
    print("lower stacks with a bad member of their progression:", hits)


if __name__ == "__main__":
    cmd, args = sys.argv[1], [int(x) for x in sys.argv[2:]]
    {"family": family, "bad": bad, "families": families}[cmd](*args)
