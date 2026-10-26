import sys
from fractions import Fraction as F
from depthslack import *
def factor(n):
    n = abs(n); f = []; p = 2
    while p * p <= n and p < 10 ** 6:
        while n % p == 0: f.append(p); n //= p
        p += 1
    if n > 1: f.append(n)
    return f
for n0 in [int(l.split()[0]) for l in open('long_n.txt')][:6]:
    w0 = 2 * n0 + 6
    m = Model(1); m.W = Pos([F(1), F(0)], w0); m.add('G', m.const(1)); m.add('M', m.W - 2)
    hist = []
    for r in range(1, 3000):
        m.do_round(); hist.append(m.shape())
        if len(hist) >= 3 and hist[-3] == 'GWWW' and hist[-2] == 'GBW' and hist[-1] == 'GMB': break
    # replay to the GWWW state
    m = Model(1); m.W = Pos([F(1), F(0)], w0); m.add('G', m.const(1)); m.add('M', m.W - 2)
    for i in range(len(hist) - 2): m.do_round()
    mk = m.marks(); a, b, c = [p for t, p in mk[1:]]; E = m.W
    Rf = E - c - 1; Lf = Pos([1029 * x + 1960 * y - 2744 * z for x, y, z in zip(b.f, E.f, c.f)], 0) - 4046
    lR, kR = Rf.f; lL, kL = Lf.f; D = lR * kL - lL * kR
    print(n0, "Delta =", D, " v2 =", v2f(D), " v2(lamL) =", v2f(lL), " numerator factors:", factor(D.numerator)[:12])
