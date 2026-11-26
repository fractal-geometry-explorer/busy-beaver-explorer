"""Closed sets of (residue, level, size) classes for the doubling form of the four machines
1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE, 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE,
1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE and 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE: none found.

The model is the doubling form of `lean/Doubling.lean`: a stop (s, L) goes to (2s, L + 2) if 2s <= L and to
(2s - L, L + 2) otherwise, and the fatal event is the midpoint 2s = L + MID at a stop with L = F_k, the L whose
all-ones tape L - OFF is the fatal length FC*2^k - 2k - FD.  (`py/doubling.py residues N` runs the phase map mod N
with the fatal lengths taken mod N for every k at once; here the level k is part of the class, and so is the size.)
With k the level of L (F_k <= L < F_(k+1)) and u = (L - F_k)/2, a class is

    (s mod N,  u mod N,  k mod P,  cell of s/L among B cells,  half of the level u is in)

with P a common period of k and 2^k mod 2N.  The search starts from the class of a point far along a model orbit,
takes members of many sizes from each class reached (the last u of a level included, so that levels are crossed),
applies the map and adds the class of the image.  It stops at a class of a fatal midpoint (u = 0, s = (F_k + MID)/2).
Every transition is a real step of the map, so a hit shows that no set of such classes is closed, holds the orbit
and misses the fatal midpoints.

usage (from the repository root): python3 holdouts/1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE/py/sizeresidues.py   (~80 s)
"""
import sys, random
from math import gcd
from collections import deque
TABLE = {
    "1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE": (1, 5, 20, 12),
    "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE": (2, 4, 32, 12),
    "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE": (2, 5, 28, 13),
    "1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE": (0, 3, 12, 9),
}
def mk(M):
    MID, OFF, FC, FD = TABLE[M]
    F = lambda k: FC * 2 ** k - 2 * k - FD + OFF
    def level(L):
        k = max(L.bit_length() - 7, 0)
        while F(k + 1) <= L: k += 1
        while F(k) > L: k -= 1
        return k
    def cls(s, L, N, B, Bu, P):
        k = level(L); u = (L - F(k)) // 2; w = (F(k + 1) - F(k)) // 2
        return (s % N, u % N, k % P, s * B // L, u * Bu // w)
    def search(N, B, Bu, P, per=3, kmin=14, seed=1):
        rnd = random.Random(seed)
        ks = list(range(kmin, kmin + max(3 * P, 30)))
        halting = {(((F(k) + MID) // 2) % N, 0, k % P, B // 2, 0) for k in ks}
        def samples(c):
            sr, ur, ph, cs, cu = c
            for k in ks:
                if k % P != ph: continue
                w = (F(k + 1) - F(k)) // 2
                lo = -(-cu * w // Bu); hi = -(-(cu + 1) * w // Bu)
                us = [rnd.randrange(lo, hi) for _ in range(per)] + [hi - 1 - ((hi - 1 - ur) % N)]
                for u in us:
                    u += (ur - u) % N
                    if not lo <= u < hi: continue
                    L = F(k) + 2 * u
                    a = -(-cs * L // B); b = -(-(cs + 1) * L // B)
                    for _ in range(per):
                        s = rnd.randrange(a, b); s += (sr - s) % N
                        if a <= s < b and 0 < s < L: yield s, L
        s, L = 12, F(3) + 2
        for _ in range(3000):
            s, L = (2 * s if 2 * s <= L else 2 * s - L), L + 2
            if s == 0: s = 1
        start = cls(s, L, N, B, Bu, P)
        seen = {start: None}; dq = deque([start])
        while dq:
            c = dq.popleft()
            if c in halting:
                n = 0; d = c
                while d is not None: n += 1; d = seen[d]
                return "halt", len(seen), n
            for s, L in samples(c):
                if 2 * s == L + MID: continue
                d = cls(2 * s if 2 * s <= L else 2 * s - L, L + 2, N, B, Bu, P)
                if d not in seen: seen[d] = c; dq.append(d)
        return "CLOSED", len(seen), 0
    return search
def ordp(N):
    o = N >> ((N & -N).bit_length() - 1)
    if o == 1: return 1
    k, t = 1, 2 % o
    while t != 1: t = t * 2 % o; k += 1
    return k
if __name__ == "__main__":
    NS, BS = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 24, 27, 32], [2, 8, 32]
    for M in TABLE:
        search = mk(M)
        worst, closed = 0, []
        for N in NS:
            o = ordp(N)
            P = 2 * N * o // gcd(2 * N, o)
            for B in BS:
                r = search(N, B, 2, P)
                worst = max(worst, r[2])
                if r[0] != "halt":
                    closed.append((N, B, r[1]))
        print(f"{M}: N in {NS}, cells {BS}: {len(NS) * len(BS) - len(closed)} of {len(NS) * len(BS)} searches reach "
              f"a fatal midpoint class (longest chain {worst} classes); closed sets: {closed or 'none'}", flush=True)
