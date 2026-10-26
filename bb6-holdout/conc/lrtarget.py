import sys, re
from fractions import Fraction as F
from tree4 import TModel, Coset, Pos
from entrydepth import entry_bits
from snf2 import v2
MODP = 2 ** 400
def q2(x):     # rational with odd denominator -> integer mod 2^400 ; returns (value, valuation shift)
    num, den = x.numerator, x.denominator
    s = 0
    while den % 2 == 0: den //= 2; s += 1
    return (num * pow(den, -1, MODP)) % MODP, s
def val(x):
    if x == 0: return 999
    n, d = x.numerator, x.denominator; return v2(abs(n)) - v2(d)
def solve2(lam, const):      # 2-adic root of lam*N + const = 0, as an element mod 2^300 (assume v(lam) <= v(const))
    vl = val(lam); r = -const / lam
    a, s = q2(r); return a, s
def analyse(n0):
    w0 = 2 * n0 + 6
    class FM(TModel):
        def test_outcome(self, d):
            dec = self.coset.decided(d.f); v = int(d.f[0] * w0 + d.f[1])
            if dec is None: self.coset.impose(d.f, v % 4)
            return v % 4
    m = FM(1); m.W = Pos([F(1), F(0)], F(w0)); m.add('G', m.const(1)); m.add('M', Pos([F(1), F(-2)], F(w0 - 2)))
    c = Coset([w0], [[2]]); m.setup_tree(c)
    hist = []
    for r in range(1, 200):
        m.do_round(); hist.append(m.shape())
        if hist[-3:] == ['GWWW', 'GBW', 'GWWW']: break
    mk = m.marks(); a, b, cc = [p for t, p in mk[1:]]; E = m.W
    # left condition: b - 16E/21 - 62/49 = 0 ; right: E - c - 1 = 0
    Lf = [x - F(16, 21) * y for x, y in zip(b.f, E.f)]; Lf[1] -= F(62, 49)
    Rf = [x - y for x, y in zip(E.f, cc.f)]; Rf[1] -= 1
    tL = -Lf[1] / Lf[0]; tR = -Rf[1] / Rf[0]
    return r, c.bits, Lf, Rf, val(Lf[0]), val(Rf[0]), val(tL - tR), (w0 - tL), (w0 - tR)
lines = [l for l in open('long_templates.txt').read().split('\n') if l]
seen = set()
for l in lines[:400]:
    n = int(l.split()[0]); ch = int(l.split()[2])
    r, bits, Lf, Rf, vL, vR, vd, dl, dr = analyse(n)
    key = (n % (1 << bits))
    if key in seen: continue
    seen.add(key)
    print(f"n={n:16d} chain {ch} cycle start round {r} digits {bits:2d}: v(lamL)={vL:3d} v(lamR)={vR:3d}  v(tL-tR)={vd:4d}  v(N-tL)={val(dl):4d} v(N-tR)={val(dr):4d}")
    if len(seen) > 25: break
