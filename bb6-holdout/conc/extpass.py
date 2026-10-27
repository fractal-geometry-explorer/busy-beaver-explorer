"""Pass map of the loop with an extra wall, from a concrete example; its countdowns; and the exact 2-adic cost per pass
(forced repetition, Smith form)."""
from fractions import Fraction as F
from conc import Model, Pos, fmt
from snf2 import solve_info
E0, m0, r0 = 3359928725346, 342330978480, 2783085762543
mc = Model(1); mc.W = mc.const(E0); mc.add('M', mc.const(m0)); mc.add('B', mc.const(r0)); mc.add('G', mc.const(1))
for r in range(4): mc.do_round()
assert mc.shape() == 'GWWWW', mc.shape()
vals = [p.v for t, p in mc.marks()[1:]] + [mc.W.v]
print("G W W W W state:", vals)
names = ['a', 'b', 'c', 'd', 'E']
EXTP = ['GBWW', 'GWWWW', 'GBWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
def setup(v, concrete):
    m = Model(5)
    for i in range(4):
        f = [F(0)] * 6; f[i] = F(1); m.add('W', Pos(f, v[i]) if not concrete else m.var(i, v[i]))
    m.W = m.var(4, v[4]) if concrete else Pos([F(0)] * 4 + [F(1), F(0)], v[4])
    m.add('G', m.const(1)); return m
m = setup(vals, True)
for want in EXTP:
    m.do_round(); assert m.shape() == want, (m.shape(), want)
outs = m.outcomes[:]
print("tests per pass:", len(outs), outs)
for t, p in m.marks()[1:]: print("   ", t, fmt(p, names))
print("    end", fmt(m.W, names))
rows = [p.f[:5] for t, p in m.marks()[1:]] + [m.W.f[:5]]
def nullspace(A):
    A = [r[:] for r in A]; n = len(A[0]); piv = []; r = 0
    for col in range(n):
        p = next((i for i in range(r, len(A)) if A[i][col] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; pv = A[r][col]; A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][col] != 0:
                f = A[i][col]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(col); r += 1
    free = [j for j in range(n) if j not in piv]; out = []
    for fj in free:
        v = [F(0)] * n; v[fj] = F(1)
        for i, pc in enumerate(piv): v[pc] = -A[i][fj]
        out.append(v)
    return out
for e in range(0, 14):
    mu = F(1, 2 ** e)
    A = [[rows[i][j] - (mu if i == j else 0) for i in range(5)] for j in range(5)]
    for v in nullspace(A):
        print(f"  left eigenvector with factor 1/{2**e}: on (a, b, c, d, E) =", [str(x) for x in v])
A0 = [[rows[i][j] for i in range(5)] for j in range(5)]
for v in nullspace(A0): print("  kernel (factor 0):", [str(x) for x in v])
# exact cost per pass by forced repetition at a scaled-up geometry
big = [F(x) * 2 ** 200 for x in vals]
for k in range(1, 6):
    mm = setup(big, False); mm.force = outs * k
    ok = True
    for _ in range(k):
        for want in EXTP:
            mm.do_round()
            if mm.shape() != want or mm.bad: ok = False; break
        if not ok: break
    if not ok: print(k, "passes: geometry broke"); break
    b, solv, S = solve_info(mm.cong, 5)
    print(f"{k} passes: bits fixed {b}, solvable {solv}")

# affine countdowns: constant so that Q(T x) = mu Q(x) exactly
trans = [p.f[5] for t, p in m.marks()[1:]] + [m.W.f[5]]
from math import gcd
def affine_countdown(v, mu):
    vt = sum(vi * ti for vi, ti in zip(v, trans))
    kappa = -vt / (1 - mu)
    coeffs = list(v) + [kappa]
    den = 1
    for x in coeffs: den = den * x.denominator // gcd(den, x.denominator)
    ints = [int(x * den) for x in coeffs]
    g = 0
    for x in ints[:5]: g = gcd(g, abs(x))
    return ints, g
for mu, v in [(F(1, 16), [F(0), F(0), F(0), F(-1), F(1)]), (F(1, 64), [F(0), F(-63, 236), F(105, 236), F(-77, 59), F(1)])]:
    ints, g = affine_countdown(v, mu)
    print(f"countdown x{mu}: {ints[0]}a + {ints[1]}b + {ints[2]}c + {ints[3]}d + {ints[4]}E + {ints[5]};  gcd of variable coefficients {g}, constant mod gcd = {ints[5] % g if g else None}")
