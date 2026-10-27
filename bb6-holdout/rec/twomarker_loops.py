#!/usr/bin/env python3
"""Loops through two-marker states on the cut paths of the clean-tape tree, and their locks (untrusted).

A two-marker state is the round start G 1, M m, M W-2 (the gap, a marker at m, the end marker). The cut paths of the
clean-tape tree with loop entries (../lean/CutShapes.lean) end in a periodic stretch of round shapes in about 10% of
cases; three of the loops run through two-marker states. For each, this script runs random states through the loop
with the round function of clean_recurrence.py, keeps those that follow the loop's word exactly, and fits the map
m' = a m + b W + c, W' = W + k on them in exact rationals (checked on every kept run). Writing the map as
L' = a L for L = m - lam W - mu and clearing denominators gives the lock: at integer points L is never 0 (it has a
fixed nonzero residue modulo the common factor of its coefficients of m and W, or it is m itself), so it is divided
by 1/a only finitely often, and an integer state leaves the loop after at most log_{1/a} |L| times round it, while the
2-adic point at L = 0 goes round for ever.  Output: twomarker_loops.out.

usage: python3 twomarker_loops.py
"""
import random
from fractions import Fraction as F
from math import gcd, lcm

from clean_recurrence import _round

LOOPS = [
    # (name, shapes after each round, where to sample m as a fraction of W)
    ("G M M -> G M M M -> G W M M", ["GMMM", "GWMM", "GMM"], (F(1, 8), F(7, 8))),
    ("seven rounds", ["GMW", "GWW", "GB", "GWW", "GB", "GWMM", "GMM"], (F(30, 31), F(30, 31))),
    ("G M M -> G M W", ["GMW", "GMM"], (F(0), F(1))),
]


def run(W, m, n):
    w, marks = W, [["G", 1], ["M", m], ["M", W - 2]]
    out = []
    for _ in range(n):
        w, marks = _round(w, [list(x) for x in marks])
        marks = sorted(marks, key=lambda x: x[1])
        out.append(("".join(x[0] for x in marks), w, [x[1] for x in marks]))
    return out


def solve3(rows):
    """Exact solution of three equations a m + b W + c = y."""
    M = [[F(m), F(W), F(1), F(y)] for m, W, y in rows]
    for i in range(3):
        p = next(r for r in range(i, 3) if M[r][i] != 0)
        M[i], M[p] = M[p], M[i]
        for r in range(3):
            if r != i:
                f = M[r][i] / M[i][i]
                M[r] = [x - f * y for x, y in zip(M[r], M[i])]
    return [M[i][3] / M[i][i] for i in range(3)]


def fit(word, lo, hi, tries=200000, seed=1):
    rnd = random.Random(seed)
    pts = []
    for _ in range(tries):
        W = rnd.randrange(2**40, 2**41) | 1
        if lo == hi:
            m = int(lo * W) + rnd.randrange(-2000, 2000)
        else:
            m = rnd.randrange(int(lo * W), int(hi * W))
        m -= m % 2
        try:
            o = run(W, m, len(word))
        except AssertionError:
            continue
        if [x[0] for x in o] == word:
            pts.append((m, W, o[-1][2][1], o[-1][1]))
    if len(pts) < 3:
        return pts, None
    for _ in range(50):
        sel = rnd.sample(pts, 3)
        try:
            a, b, c = solve3([(m, W, mp) for m, W, mp, _ in sel])
        except StopIteration:
            continue
        if all(a * m + b * W + c == mp for m, W, mp, _ in pts):
            return pts, (a, b, c)
    return pts, None


def main():
    for name, word, (lo, hi) in LOOPS:
        pts, co = fit(word, lo, hi)
        print(f"{name}: {len(pts)} runs follow the loop")
        if co is None:
            print("  no exact affine fit")
            continue
        a, b, c = co
        ks = {Wp - W for _, W, _, Wp in pts}
        print(f"  m' = {a} m + {b} W + {c},  W' - W in {sorted(ks)}")
        if len(ks) != 1 or a == 1:
            continue
        k = ks.pop()
        lam = b / (1 - a)
        mu = (c - lam * k) / (1 - a)
        den = lcm(lam.denominator, mu.denominator)
        A, B, C = den, int(-lam * den), int(-mu * den)
        g = gcd(A, B)
        lock = f"L = {C % g} (mod {g}) at integer points" if g > 1 else "no residue lock"
        print(f"  L = {A} m + {B} W + {C}:  L' = {a} L,  {lock} (fixed point m = {lam} W + {mu})")


if __name__ == "__main__":
    main()
