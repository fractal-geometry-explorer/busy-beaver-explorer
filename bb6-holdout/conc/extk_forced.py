"""Loop with k extra walls via forced branches: outcome pattern [2]*(5+2k) + [0,0] + [2]*(2+k) + [0,0] + [2]*(3+k)
(read off k = 0, 1, 2). Prints the pass map's left countdown (factor 1/64) and its residue mod 7, the exact bits per
pass, and checks the shapes."""
import sys
from fractions import Fraction as F
from math import gcd
from conc import Model, Pos
from snf2 import solve_info
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
def run(k, geo, npass=1):
    nw = 3 + k; nv = nw + 1
    EXT = [s + 'W' * k for s in LOOP]
    seq = [EXT[(6 + q) % 8] for q in range(1, 9)]          # phase-6 start: G B W.. G W W W.. G B W.. G M B ...
    pat = [2] * (5 + 2 * k) + [0, 0] + [2] * (2 + k) + [0, 0] + [2] * (3 + k)
    m = Model(nv)
    for i in range(nw): m.add('W', Pos([F(int(i == j)) for j in range(nv)] + [F(0)], F(geo[i])))
    m.W = Pos([F(int(j == nv - 1)) for j in range(nv)] + [F(0)], F(geo[-1])); m.add('G', m.const(1))
    m.force = pat * npass
    for p in range(npass):
        for want in seq:
            m.do_round()
            if m.bad or m.shape() != want: return None, f"shape {m.shape()} vs {want} (bad {m.bad})"
    return m, None
def countdown(m, nv):
    rows = [p.f[:nv] for t, p in m.marks()[1:]] + [m.W.f[:nv]]
    trans = [p.f[nv] for t, p in m.marks()[1:]] + [m.W.f[nv]]
    # left eigenvector for 1/64 by solving (M^T - mu I) v = 0
    mu = F(1, 64); n = nv
    A = [[rows[i][j] - (mu if i == j else 0) for i in range(n)] for j in range(n)]
    piv = []; r = 0
    for col in range(n):
        pv_ = next((i for i in range(r, n) if A[i][col] != 0), None)
        if pv_ is None: continue
        A[r], A[pv_] = A[pv_], A[r]; pv = A[r][col]; A[r] = [x / pv for x in A[r]]
        for i in range(n):
            if i != r and A[i][col] != 0:
                f = A[i][col]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(col); r += 1
    free = [j for j in range(n) if j not in piv]
    assert len(free) == 1, free
    v = [F(0)] * n; v[free[0]] = F(1)
    for i, pc in enumerate(piv): v[pc] = -A[i][free[0]]
    vt = sum(vi * ti for vi, ti in zip(v, trans)); kappa = -vt / (1 - mu)
    coeffs = v + [kappa]; den = 1
    for x in coeffs: den = den * x.denominator // gcd(den, x.denominator)
    ints = [int(x * den) for x in coeffs]; g = 0
    for x in ints[:n]: g = gcd(g, abs(x))
    return ints, g
if __name__ == "__main__":
  for k in range(0, int(sys.argv[1]) + 1):
      E = 2 ** 200
      geo = [E * 64 // 10000, E * 1230 // 10000, E * 4550 // 10000] + [E - (E * 1620 // 10000) // (3 ** i) for i in range(k)] + [E]
      geo = sorted(geo[:-1]) + [E]
      m, err = run(k, geo)
      if m is None: print(f"k = {k}: forced pass failed: {err}"); continue
      ints, g = countdown(m, 4 + k)
      nb = []
      for p in ((1, 2, 3) if k <= 8 else (1,)):
          mm, err = run(k, geo, p)
          if mm is None: nb.append(None); break
          b, ok, S = solve_info(mm.cong, 4 + k); nb.append(b if ok else 'X')
      print(f"k = {k}: left countdown coefficients/7 = {[x // 7 if g % 7 == 0 else x for x in ints[:-1]]}, constant {ints[-1]} (mod 7 = {ints[-1] % 7}); gcd {g}; bits fixed for 1, 2, 3 passes: {nb}")
