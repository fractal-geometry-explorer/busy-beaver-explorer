"""The line-up number of a GMM-born entry into the extra-wall loop: write the three contracting countdowns of a P
pass (R, the Jordan partner J of R, and L) as affine forms on the entry's 2-parameter family; they satisfy one
relation aR + bJ + cL = kappa with integer a, b, c; print kappa and its 2-adic valuation."""
import json, math
from fractions import Fraction as F
import mixsolve as MS, ewforms as EF
from ewmap import nullspace
m = MS.forced('P'); mk = m.marks(); pos = [p for t, p in mk[1:]] + [m.W]
M = [[p.f[j] for j in range(5)] for p in pos]; t = [p.f[5] for p in pos]
MT = [[M[j][i] for j in range(5)] for i in range(5)]
def affine_countdown(v, lam):
    # phi(x) = v.x + c with phi(Mx + t) + c = lam (phi + c)  (exact eigenform)
    vt = sum(a * b for a, b in zip(v, t)); return v, vt / (lam - 1)
lam = F(1, 16); R = [F(0), F(0), F(0), F(-1), F(1)]
A = [[MT[i][j] - (lam if i == j else 0) for j in range(5)] + [R[i]] for i in range(5)]
# solve (MT - lam) v = R  -> generalized eigenvector
import copy
def solve(A):
    A = copy.deepcopy(A); n = len(A); piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, n) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; A[r] = [x / A[r][c] for x in A[r]]
        for i in range(n):
            if i != r and A[i][c] != 0: A[i] = [a - A[i][c] * b for a, b in zip(A[i], A[r])]
        piv.append(c); r += 1
    x = [F(0)] * n
    for i, c in enumerate(piv): x[c] = A[i][n]
    return x
Jv = solve(A)
Lv = [F(0), F(-63), F(105), F(-308), F(236)]
print("J form", [str(x) for x in Jv])
routes = json.load(open('../ewroutes_30.json'))
def v2(x):
    x = F(x)
    if x == 0: return 99
    num, den = x.numerator, x.denominator; v = 0
    while num % 2 == 0: num //= 2; v += 1
    while den % 2 == 0: den //= 2; v -= 1
    return v
out = []
for idx, (h, o, p) in enumerate(routes):
    md = EF.route_model(h, o); mk = md.marks()
    fam = [list(q.f) for tt, q in mk[1:]] + [list(md.W.f)]
    def on_family(v):
        return [sum(v[i] * fam[i][j] for i in range(5)) for j in range(3)]   # coefficients of m, E, const
    fR, fJ, fL = on_family(R), on_family(Jv), on_family(Lv)
    # find (a, b, c) with a fR + b fJ + c fL having zero m and E coefficients
    ns = nullspace([[fR[0], fJ[0], fL[0]], [fR[1], fJ[1], fL[1]]])
    if len(ns) != 1: out.append((idx, 'degenerate', len(ns))); continue
    a, b, c = ns[0]
    den = 1
    for q in (a, b, c): den = den * q.denominator // math.gcd(den, q.denominator)
    a, b, c = a * den, b * den, c * den
    g = math.gcd(math.gcd(int(a), int(b)), int(c)); a, b, c = a / g, b / g, c / g
    kappa = a * fR[2] + b * fJ[2] + c * fL[2]
    out.append((idx, p, int(a), int(b), int(c), kappa, v2(kappa)))
for x in out[:20]: print(x)
vals = [x[-1] for x in out if len(x) == 7]
import collections
print("v2(kappa) distribution:", sorted(collections.Counter(vals).items()))
