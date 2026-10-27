import sys
from fractions import Fraction as F
from conc import Model, Pos
from taustates import ratrec
M = 1 << 20
def tau(p, W):
    t = W.f[1] - p.f[1] * W.f[0] / p.f[0]
    if t.denominator % 2 == 0: return 'nonint'
    v = (t.numerator * pow(t.denominator, -1, M)) % M
    r = ratrec(v, M)
    return str(r) if r is not None and abs(r.numerator) < 2000 and r.denominator < 2000 else f"#{v}"
def s_of(p):
    d = p.f[0].denominator; s = 0
    while d > 1: d //= 2; s += 1
    return s
n0 = int(sys.argv[1]); R = int(sys.argv[2])
m = Model(1); m.W = Pos([F(1), F(6)], 2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2)
for r in range(R):
    mk = m.marks()
    print(r, m.shape().ljust(7), '  '.join(f"{t}[s{s_of(p)}] {tau(p, m.W)}" for t, p in mk[1:]))
    m.do_round()
