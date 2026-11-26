"""Closed sets of residue classes for the chain starts of 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD: none found.

A chain start is a sample (x, m0, 0) with m0 = 1 or 3, made by an R or an A' step of the map of lean/MapThm.lean.
It halts in its first chain iff x = h_k, where h_k = 2^(k+3) - k - 5 for m0 = 1 and 5*2^(k+1) - k - 6 for m0 = 3
(`crit_m1`, `crit_m3` in lean/Chain.lean).  Put k = the level of x (h_k <= x < h_(k+1)), v = x - h_k, and sort the
chain starts into classes

    (v mod N,  k mod P,  m0,  cell of v among B equal cells of its level)

with P = lcm(N, order of 2 mod the odd part of N), so that a class also fixes x mod N.  A non-halting proof by
residues would be a set of classes that holds the run, is mapped into itself by the round map (chain start to next
chain start) and does not contain the class of v = 0.  The search follows real rounds: from each class reached it
takes members of many sizes, runs the exact map to the next chain start and adds that class.  It stops when it
reaches a class (0, k, m0, cell 0), which holds the halting value h_k itself.  Every transition used is a real
round of the map, so a hit shows that no such closed set exists for that N and B (from the class of the run after
60 rounds, hence for the run).

usage (from the repository root):
  python3 holdouts/1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/py/residues.py            the table of the README (~25 s)
  python3 holdouts/1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/py/residues.py N B        one modulus and cell count
"""
import random
import sys
from collections import deque
from math import gcd


def mstep(x, m, s):
    """The map of lean/MapThm.lean; None is H."""
    if m % 2 == 0:
        return (x - 1, m + 4, 1 - s) if x >= 1 else ((m + 6) // 2, 3 if s else 1, 0)
    if x == 0:
        return None
    if x >= (m + 5) // 2:
        return (x - (m + 5) // 2, 2 * m + 7 - s, s)
    if x + 1 == (m + 5) // 2 and s == 0:
        return (2 * x + 3, 1, 0)
    return (2 * x + 1, m + 4 - 2 * x, 1 - s)


def nxt(x, m0):
    """From the chain start (x, m0, 0): the next chain start (x', m0'), made by R or A'; None if the map halts."""
    p = (x, m0, 0)
    while True:
        x, m, s = p
        if m % 2 == 0 and x >= 1:                     # a whole B phase at once
            p = (0, m + 4 * x, s ^ (x & 1))
            continue
        q = mstep(x, m, s)
        if q is None:
            return None
        if m % 2 == 0 or (s == 0 and x + 1 == (m + 5) // 2):
            return q[0], q[1]
        p = q


def hval(k, m0):
    return (1 << (k + 3)) - k - 5 if m0 == 1 else 5 * (1 << (k + 1)) - k - 6


def level(x, m0):
    k = max(x.bit_length() - 5, 0)
    while hval(k + 1, m0) <= x:
        k += 1
    while hval(k, m0) > x:
        k -= 1
    return k


def cls(x, m0, N, B, P):
    k = level(x, m0)
    v, w = x - hval(k, m0), hval(k + 1, m0) - hval(k, m0)
    return (v % N, k % P, m0, v * B // w)


def period(N):
    odd = N >> ((N & -N).bit_length() - 1)
    o, t = 1, 2 % odd if odd > 1 else 1
    while t != 1:
        t, o = t * 2 % odd, o + 1
    return N * o // gcd(N, o)


def search(N, B, per=2, kmin=20, seed=1):
    """('halt', classes seen, length of the chain of classes) or ('CLOSED', classes, 0)."""
    P = period(N)
    rnd = random.Random(seed)
    ks = range(kmin, kmin + max(3 * P, 48))

    def members(c):
        r, ph, m0, cell = c
        for k in ks:
            if k % P != ph:
                continue
            h = hval(k, m0)
            w = hval(k + 1, m0) - h
            lo, hi = -(-cell * w // B), -(-(cell + 1) * w // B)
            for _ in range(per):
                v = rnd.randrange(lo, hi)
                v += (r - v) % N
                if v < hi:
                    yield h + v

    x, m0 = 7, 1
    for _ in range(60):
        x, m0 = nxt(x, m0)
    start = cls(x, m0, N, B, P)
    seen, todo = {start: None}, deque([start])
    while todo:
        c = todo.popleft()
        if c[0] == 0 and c[3] == 0:
            n = 0
            while c is not None:
                n, c = n + 1, seen[c]
            return 'halt', len(seen), n
        for x in members(c):
            q = nxt(x, c[2])
            if q is not None:
                d = cls(q[0], q[1], N, B, P)
                if d not in seen:
                    seen[d] = c
                    todo.append(d)
    return 'CLOSED', len(seen), 0


def table():
    assert all(nxt(hval(k, m), m) is None for k in range(60) for m in (1, 3))
    jobs = [(N, B) for N in list(range(2, 49)) + [64, 81, 96, 128, 243, 256] for B in (1, 16)]
    jobs += [(N, B) for N in (2, 3, 4, 6, 8, 9, 12, 16, 27, 32) for B in (64, 256)]
    worst, closed = 0, []
    for N, B in jobs:
        res, n, length = search(N, B)
        if res != 'halt':
            closed.append((N, B, n))
            print(f'N = {N}, {B} cells: CLOSED SET of {n} classes  <-- look at this')
        worst = max(worst, length)
    print(f'{len(jobs)} searches (N = 2..48, 64, 81, 96, 128, 243, 256 with 1 and 16 cells; '
          f'N = 2, 3, 4, 6, 8, 9, 12, 16, 27, 32 with 64 and 256 cells): '
          f'{len(jobs) - len(closed)} reach the class of a halting value, in at most {worst} classes; '
          f'closed sets: {closed or "none"}')


if __name__ == '__main__':
    if len(sys.argv) == 3:
        N, B = int(sys.argv[1]), int(sys.argv[2])
        print(N, B, *search(N, B))
    else:
        table()
