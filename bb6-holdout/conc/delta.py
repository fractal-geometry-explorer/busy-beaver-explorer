"""At each pass start (G, W a, W b, W c, end E followed by G-B-W, G-M-B) of a clean-tape cycle, write the two loop
countdowns as affine functions of N = 2n + 6:  R = E - c - 1 = lR*N + kR,  L = 1029b + 1960E - 2744c - 4046 = lL*N + kL.
Delta = lR*kL - lL*kR is the same for every N in the family; it bounds how far the line can follow both countdowns."""
import sys
from fractions import Fraction as F
from conc import Model, Pos
def v2f(x):
    if x == 0: return 999
    n, d = x.numerator, x.denominator; c = 0
    while n % 2 == 0: n //= 2; c += 1
    while d % 2 == 0: d //= 2; c -= 1
    return c
def v2i(x):
    if x == 0: return 999
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
def analyse(n0):
    w0 = 2 * n0 + 6
    m = Model(1); m.W = m.var(0, w0); m.add('G', m.const(1)); m.add('M', m.var(0, w0) - 2)
    hist = []; states = []
    for r in range(1, 3000):
        m.do_round(); sh = m.shape(); hist.append(sh)
        if sh == 'GWWW':
            mk = m.marks(); a, b, c = [p for t, p in mk[1:]]; states.append((r, a, b, c, m.W))
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    out = []
    for (r, a, b, c, E) in states:
        if r + 1 < len(hist) and hist[r] == 'GBW' and hist[r + 1] == 'GMB':
            Rf = E - c - 1
            Lf = Pos([1029 * x + 1960 * y - 2744 * z for x, y, z in zip(b.f, E.f, c.f)], 1029 * b.v + 1960 * E.v - 2744 * c.v)
            Lf = Lf - 4046
            lR, kR = Rf.f; lL, kL = Lf.f
            D = lR * kL - lL * kR
            out.append((r, v2i(Lf.v), v2i(Rf.v), v2f(lL), v2f(lR), v2f(D)))
    return out
if __name__ == '__main__':
    for l in open(sys.argv[1]):
        if not l.strip(): continue
        n = int(l.split()[0])
        res = analyse(n)
        if res:
            r, fl, fr, vl, vr, vd = res[0]
            print(f"{n} first pass start round {r}: fuels L {fl} R {fr}; v(lamL) {vl} v(lamR) {vr} v(Delta) {vd}; "
                  f"gaps {vd - vr} {vd - vl}")
