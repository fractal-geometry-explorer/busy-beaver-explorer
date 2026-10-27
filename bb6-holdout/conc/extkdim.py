"""Contracting directions of the loop with k extra walls (pass map from extk_forced), and how many passes a family
with d free numbers can follow: families x0 + sum of d random even directions, x0 a point that makes one pass."""
import random, sys
from fractions import Fraction as F
import extk_forced as XK
from ewmap import nullspace
from lattice import Coset as LCoset
def geo_for(k):
    E = 2 ** 200
    geo = [E * 64 // 10000, E * 1230 // 10000, E * 4550 // 10000] + [E - (E * 1620 // 10000) // (3 ** i) for i in range(k)] + [E]
    return sorted(geo[:-1]) + [E]
NMAX = 5
for k in range(0, 4):
    nv = 4 + k
    congs = {}
    for n in range(1, NMAX + 1):
        mm, err = XK.run(k, geo_for(k), n)
        if mm is None: break
        congs[n] = mm.cong
    m1, _ = XK.run(k, geo_for(k), 1)
    pos = [p for t, p in m1.marks()[1:]] + [m1.W]
    M = [[p.f[j] for j in range(nv)] for p in pos]
    zero = len(nullspace([[M[i][j] for i in range(nv)] for j in range(nv)]))
    one = len(nullspace([[M[i][j] - (1 if i == j else 0) for i in range(nv)] for j in range(nv)]))
    # a point making one pass, in the free model
    C1 = LCoset(nv)
    for form, res, mod in congs[1]:
        den = max(q.denominator for q in form.f)
        C1.impose([int(q * den) for q in form.f[:nv]], den * res - int(form.f[nv] * den), den * mod, reduce=False)
    x0 = C1.x0
    print(f"k = {k}: {nv} coordinates, forgotten {zero}, neutral {one}, contracting {nv - zero - one}; "
          f"congruences per pass {len(congs[1])}", flush=True)
    def consistent(fam, d, n):
        C = LCoset(d)
        for form, res, mod in congs[n]:
            f = [F(0)] * (d + 1)
            for i in range(nv):
                for j in range(d + 1): f[j] += form.f[i] * fam[i][j]
            f[d] += form.f[nv]
            den = max(q.denominator for q in f)
            if not C.impose([int(q * den) for q in f[:d]], den * res - int(f[d] * den), den * mod, reduce=False): return False
        return True
    random.seed(100 + k)
    for d in range(1, nv):
        caps = []
        for trial in range(10):
            fam = [[F(2 * random.randrange(-10**6, 10**6)) for _ in range(d)] + [F(x0[i])] for i in range(nv)]
            n = 0
            while n < max(congs) and consistent(fam, d, n + 1): n += 1
            caps.append(n)
        print(f"   {d} free numbers: largest n consistent (of {max(congs)}): {caps}", flush=True)
