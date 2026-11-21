"""Residue screen: is there a modulus M for which the halting class is unreachable?

For a map on a few counters, replace every counter by its residue mod M and every size comparison (c <= a+8, u < v,
...) by "either branch". If the halting test can never be met mod M from the start, that is a proof of non-halting
(the abstraction over-approximates the orbit). For the four subtract-and-multiply maps below the halting class is
reached for every M tried (all M up to 7,776 with only factors 2 and 3), and within a few hundred residue states,
so there is no invariant of this kind.

usage: python3 tools/number-theory/residues.py
"""
from collections import deque

H = "HALT"


def smooth(limit):
    out = []
    for a in range(0, 13):
        for b in range(0, 9):
            m = 2 ** a * 3 ** b
            if 2 <= m <= limit:
                out.append(m)
    return sorted(out)


def explore(step, init, M, limit=300000):
    init = tuple(x % M for x in init)
    seen, q = {init}, deque([init])
    while q:
        s = q.popleft()
        for t in step(s, M):
            if t == H:
                return False, len(seen)
            t = tuple(x % M for x in t)
            if t not in seen:
                seen.add(t)
                q.append(t)
                if len(seen) > limit:
                    return None, len(seen)
    return True, len(seen)


def s22(s, M):   # 1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA, (a, c) from (74, 30)
    a, c = s
    if c % 2 == 0:
        o = [(a - c + 12, 3 * c - 6), (c - a - 10, 3 * a + 27)]
        if (c - a) % M in (10 % M, 12 % M):
            o.append(H)
    else:
        o = [(a - c - 1, 3 * c + 6), (c - a + 3, 3 * a)]
        if (a - c) % M in (1 % M, 3 % M):
            o.append(H)
    return o


def s34(s, M):   # 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE, (p, r) from (2, 1)
    p, r = s
    o = [(2 * p + 2, r - p - 1), (2, 4 * p + 1), (p - r, 4 * r + 2)]
    if (r - p) % M == 1 % M:
        o.append(H)
    return o


def s28(s, M):   # 1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD, (P/Q, u, v) from P(3, 0)
    t, u, v = s
    o = [H] if (u - v) % M in (0, 1 % M) else []
    if t == 0:
        o += [(0, 3 * u + 2, v - u - 1), (1, 3 * v + 3, u - v - 2)]
    else:
        o += [(1, 3 * u + 3, v - u - 1), (0, 3 * v + 5, u - v - 2)]
    return o


def s27(s, M):   # 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE, (J, i, j) from (0, 3, 1)
    J, i, j = s
    o = [H] if (i - j) % M == 0 or (j - i) % M == 1 % M else []
    o.append((J, i - j - 1, 3 * j + (3 if J else 2)))
    o.append((0, 3 * i, 1) if J else (1, 3 * i - 3, 3))
    o.append((1, 3 * i + 3, 3) if J else (0, 3 * i + 3, 1))
    o.append((1 - J, j - i - 2, 3 * i + (5 if J else 3)))
    return o


if __name__ == "__main__":
    for name, st, init in [("1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA", s22, (74, 30)),
                           ("1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE", s34, (2, 1)),
                           ("1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD", s28, (0, 3, 0)),
                           ("1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE", s27, (0, 3, 1))]:
        worst, found = 0, None
        for M in smooth(7776):
            ok, n = explore(st, init, M)
            if ok:
                found = M
                break
            worst = max(worst, n)
        print(name, f"invariant mod {found}" if found else f"no invariant for 2^a 3^b <= 7776 "
              f"(halting class reached within {worst} residue states)")
