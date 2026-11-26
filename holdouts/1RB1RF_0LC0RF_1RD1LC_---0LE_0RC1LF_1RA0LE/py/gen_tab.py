#!/usr/bin/env python3
"""gen_tab.py K LOGN0 OUT: the table of K-rule steps for tentfast.c.

A state is B(x, Y).  With d = 2x - Y the generic rules are (rounds.c / py/rules.py):
  fold,   d >= 3 (Y odd) or d >= 0 (Y even):  Y even: (Y + 2, 2x - Y)      Y odd: (Y + 3, 2x - Y - 3)
  double, d <= -3 (Y odd) or d <= -4 (Y even): (2x + 2, Y - 2x - 3)
A table entry is a word of K generic rules taken from a state with |d_i| >= M at every one of them.  For the word it
holds the parity of Y after the word (bit 1 of its first field), the composed affine map, twice the step count as a quadratic in (x, Y), and the two binding conditions.
The conditions of all K rules are linear; for n = 2x + Y >= N0 = 2^LOGN0 two of them imply the rest (checked here
exactly, entry by entry; an entry where that fails is marked unusable).
"""
import sys, struct
from fractions import Fraction as Fr
K = int(sys.argv[1]); LOGN0 = int(sys.argv[2]); out = sys.argv[3]
M = 24; N0 = 1 << LOGN0
# polynomials in x, Y of degree <= 2 as dicts {(i,j): coef}
def padd(p, q):
    r = dict(p)
    for k, v in q.items(): r[k] = r.get(k, 0) + v
    return r
def pmul(p, q):
    r = {}
    for (a, b), v in p.items():
        for (c, e), w in q.items(): r[(a + c, b + e)] = r.get((a + c, b + e), 0) + v * w
    return r
def pc(c): return {(0, 0): c}
def lin(a, b, c): return {(1, 0): a, (0, 1): b, (0, 0): c}
def ev(p, x, Y): return sum(v * x ** i * Y ** j for (i, j), v in p.items())
def rule(par, br, X, Yp):
    """one generic rule on affine forms X, Yp (polys of degree 1): new forms, twice the steps, new parity"""
    two = pc(2)
    if br == 'f':
        if par == 0:
            # 4xh - 2h^2 + 2x + 16h + 12 with h = Y/2 ; doubled: 4xY - Y^2 + 4x + 16Y + 24
            s2 = padd(padd(pmul(pc(4), pmul(X, Yp)), pmul(pc(-1), pmul(Yp, Yp))), padd(pmul(pc(4), X), padd(pmul(pc(16), Yp), pc(24))))
            return padd(Yp, pc(2)), padd(pmul(two, X), pmul(pc(-1), Yp)), s2, 0
        # h = (Y-1)/2: 4xh - 2h^2 + 6x + 12h + 22 ; doubled: 4xY - Y^2 + 8x + 14Y + 31
        s2 = padd(padd(pmul(pc(4), pmul(X, Yp)), pmul(pc(-1), pmul(Yp, Yp))), padd(pmul(pc(8), X), padd(pmul(pc(14), Yp), pc(31))))
        return padd(Yp, pc(3)), padd(padd(pmul(two, X), pmul(pc(-1), Yp)), pc(-3)), s2, 0
    # 2x^2 + 10x + 9, doubled
    s2 = padd(pmul(pc(4), pmul(X, X)), padd(pmul(pc(20), X), pc(18)))
    return padd(pmul(two, X), pc(2)), padd(padd(Yp, pmul(pc(-2), X)), pc(-3)), s2, 1 - par
def slow(x, Y):
    """one rule exactly as rounds.c; returns (x, Y, steps) or None at the halt"""
    h = Y >> 1
    if Y % 2 == 0:
        if x >= h: return 2 * h + 2, 2 * x - 2 * h, 4 * x * h - 2 * h * h + 2 * x + 16 * h + 12
        if x + 1 < h: return 2 * x + 2, 2 * h - 2 * x - 3, 2 * x * x + 10 * x + 9
        return 2 * x + 1, 0, 2 * x * x + 10 * x + 7
    if x > h + 1: return 2 * h + 4, 2 * x - 2 * h - 4, 4 * x * h - 2 * h * h + 6 * x + 12 * h + 22
    if x == h + 1: return 2, 4 * x - 2, 2 * x * x + 14 * x + 7
    if x < h: return 2 * x + 2, 2 * h - 2 * x - 2, 2 * x * x + 10 * x + 9
    return None
def word_of(par, iu):
    # a large state in the middle of the cell: u = 2x/(2x+Y) = (iu + 1/2)/2^K
    n = 1 << 60
    twox = n * (2 * iu + 1) >> (K + 1); x = twox // 2; Y = n - 2 * x
    if Y % 2 != par: Y += 1
    w = ''
    for _ in range(K):
        d = 2 * x - Y
        if abs(d) < (1 << 30): return None
        w += 'f' if d > 0 else 'd'
        x, Y, _s = slow(x, Y)
    return w
def entry(par, w):
    X, Yp = lin(1, 0, 0), lin(0, 1, 0); S2 = {}; p = par; cons = []
    for br in w:
        # d = 2X - Y ; fold: d - M >= 0 ; double: -d - M >= 0
        dd = padd(pmul(pc(2), X), pmul(pc(-1), Yp))
        cons.append(padd(dd, pc(-M)) if br == 'f' else padd(pmul(pc(-1), dd), pc(-M)))
        X, Yp, s2, p = rule(p, br, X, Yp); S2 = padd(S2, s2)
    # binding conditions, in n = 2x + Y, d = 2x - Y: a x + b Y + g >= 0  <=>  P n + Q d + 4g >= 0, P = a + 2b, Q = a - 2b
    lo, hi = [], []
    for i, c in enumerate(cons):
        a, b, g = c.get((1, 0), 0), c.get((0, 1), 0), c.get((0, 0), 0)
        P, Q = a + 2 * b, a - 2 * b
        if Q == 0: return None
        # d >= -(P n + 4g)/Q  (Q > 0)   or   d <= -(P n + 4g)/Q  (Q < 0)
        slope, val = Fr(-P, Q), Fr(-(P * N0 + 4 * g), Q)
        (lo if Q > 0 else hi).append((val, slope, i))
    if not lo or not hi: return None
    bl = max(lo); bh = min(hi, key=lambda t: (t[0], -t[1]))
    if any(s > bl[1] for _v, s, _i in lo): return None
    if any(s < bh[1] for _v, s, _i in hi): return None
    def c3(c): return [c.get((1, 0), 0), c.get((0, 1), 0), c.get((0, 0), 0)]
    A = [X.get((1, 0), 0), X.get((0, 1), 0), X.get((0, 0), 0), Yp.get((1, 0), 0), Yp.get((0, 1), 0), Yp.get((0, 0), 0)]
    Qd = [S2.get(k, 0) for k in ((2, 0), (1, 1), (0, 2), (1, 0), (0, 1), (0, 0))]
    return A + c3(cons[bl[2]]) + c3(cons[bh[2]]) + Qd, (X, Yp, S2, cons), p
def selftest(par, w, full):
    # random states that satisfy every condition: the entry equals K slow rules
    import random
    X, Yp, S2, cons = full
    for _ in range(3):
        for _try in range(200):
            n = random.randrange(N0, 1 << 50); x = random.randrange(1, n // 2); Y = n - 2 * x
            if Y % 2 != par: Y += 1
            if all(ev(c, x, Y) >= 0 for c in cons): break
        else: return
        a, b, st = x, Y, 0
        for _ in range(K):
            a, b, s = slow(a, b); st += s
        assert (ev(X, x, Y), ev(Yp, x, Y), ev(S2, x, Y)) == (a, b, 2 * st), (par, w, x, Y)
ok = bad = 0
with open(out, 'wb') as f:
    f.write(struct.pack('<4q', K, LOGN0, M, 0))
    for par in (0, 1):
        for iu in range(1 << K):
            w = word_of(par, iu); e = entry(par, w) if w else None
            if e is None:
                f.write(struct.pack('<19q', *([0] * 19))); bad += 1; continue
            vals, full, pout = e
            if iu % 37 == 0: selftest(par, w, full)
            assert all(abs(v) < 1 << 62 for v in vals)
            f.write(struct.pack('<19q', 1 + 2 * pout, *vals)); ok += 1
print(f"K {K} N0 2^{LOGN0}: {ok} usable entries, {bad} unusable")
