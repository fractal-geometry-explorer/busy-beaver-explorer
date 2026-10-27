"""At each plain-loop pass start of a clean cycle (N = 2n+6 symbolic): digits of N read by the tests so far (k),
denominator exponents of lam_R, lam_L and of the constants, the gaps, and the trivial bound G_R <= v2-size of the
numerator.  Checks whether the denominators lag behind the depth."""
import sys, math
from fractions import Fraction as F
from conc import Model, Pos
def v2f(x):
    if x == 0: return 999
    n, d = x.numerator, x.denominator; c = 0
    while n % 2 == 0: n //= 2; c += 1
    while d % 2 == 0: d //= 2; c -= 1
    return c
def dexp(x):
    d = F(x).denominator; s = 0
    while d > 1: d //= 2; s += 1
    return s
def analyse(n0):
    w0 = 2 * n0 + 6
    m = Model(1); m.W = Pos([F(1), F(0)], w0); m.add('G', m.const(1)); m.add('M', m.W - 2)
    hist = []; out = []; kread = 0; ncong = 0
    for r in range(1, 3000):
        m.do_round(); sh = m.shape(); hist.append(sh)
        for (d, res, mod) in m.cong[ncong:]:
            lam = d.f[0]
            kread = max(kread, dexp(lam) + 2)        # d mod 4 needs N mod 2^(s+2)
        ncong = len(m.cong)
        if sh == 'GWWW':
            mk = m.marks(); a, b, c = [p for t, p in mk[1:]]; out.append([r, a, b, c, m.W, kread])
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    res = []
    for (r, a, b, c, E, k) in out:
        if r + 1 < len(hist) and hist[r] == 'GBW' and hist[r + 1] == 'GMB':
            Rf = E - c - 1
            Lf = Pos([1029 * x + 1960 * y - 2744 * z for x, y, z in zip(b.f, E.f, c.f)], 0) - 4046
            lR, kR = Rf.f; lL, kL = Lf.f; D = lR * kL - lL * kR
            s = max(dexp(lR), dexp(kR), dexp(lL), dexp(kL))
            GR = v2f(D) - v2f(lL); GL = v2f(D) - v2f(lR)
            num = abs(D * 2 ** (2 * s)); bound = math.log2(num) - 2 * s - v2f(lL) if num else None   # G_R <= this
            res.append((r, k, s, GL, GR, round(bound, 1), round(math.log2(Rf.v), 1), round(math.log2(w0), 1)))
    return res
if __name__ == '__main__':
    src = sys.argv[1]
    ns = [int(l.split()[0]) for l in open(src) if l.strip()][:int(sys.argv[2]) if len(sys.argv) > 2 else None]
    for n in ns:
        for t in analyse(n)[:1]:
            print(n, "round %d depth k=%d denom s=%d gaps (%d,%d) bound G_R<=%s log2 R=%s log2 W=%s" % t)
