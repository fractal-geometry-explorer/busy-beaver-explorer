"""For every mark at every round start of many clean cycles: tau_x = kappa_E - kappa_x / lambda_x (2-adic, mod 2^M),
with N = 2n + 6 symbolic.  How many distinct values occur?"""
import sys, random, collections
from fractions import Fraction as F
from conc import Model, Pos
M = 1 << 16
def tau_mod(lam, kap, lamE, kapE):
    # positions are lam*N + kap; E = lamE*N + kapE; tau = kapE - kap*lamE/lam  (all dyadic)
    t = kapE - kap * lamE / lam
    num, den = t.numerator, t.denominator
    if den % 2 == 0: return None
    return (num * pow(den, -1, M)) % M
random.seed(1)
vals = collections.Counter(); bytype = collections.defaultdict(set); ncyc = 0
for trial in range(int(sys.argv[1]) if __name__ == "__main__" else 0):
    n0 = random.randrange(2 ** 35, 2 ** 40) * 6 + 2         # n = 2 mod 3, even? keep both parities
    m = Model(1); m.W = Pos([F(1), F(6)], 2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2)
    # use N = 2n as the variable: W = N + 6
    for r in range(4000):
        for t, p in m.marks()[1:]:
            if p.f[0] == 0: continue
            v = tau_mod(p.f[0], p.f[1], m.W.f[0], m.W.f[1])
            if v is not None: vals[v] += 1; bytype[t].add(v)
        m.do_round()
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    ncyc += 1
if __name__ == "__main__": print(ncyc, "cycles;", len(vals), "distinct tau mod 2^16 over all marks;", {t: len(s) for t, s in bytype.items()})
if __name__ == "__main__": print("most common:", vals.most_common(12))

def ratrec(a, m=M):
    # rational reconstruction: find p/q with |p|, q <= sqrt(m/2) and p = a q (mod m)
    import math
    r0, r1 = m, a % m; s0, s1 = 0, 1; bound = int(math.isqrt(m // 2))
    while r1 > bound:
        q = r0 // r1; r0, r1 = r1, r0 - q * r1; s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound: return None
    return F(r1, s1) if s1 > 0 else F(-r1, -s1)
if __name__ == '__main__' and len(sys.argv) > 2:
    rs = collections.Counter()
    for v, c in vals.items(): rs[ratrec(v)] += c
    print("as small rationals:", sorted(((str(k), c) for k, c in rs.items()), key=lambda x: -x[1])[:60])
