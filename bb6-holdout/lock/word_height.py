"""The lock of a single word.  For any word w the composite map has a left quadratic factor q; when q is
irreducible, the forms killed by q(M_w^T) span a 2-dimensional rational space {φ1, φ2}, and there is a quadratic
D_w in φ1, φ2 (primitive, integer coefficients in w2, w3, w4, E) with D_w(w(x)) = det_w · D_w(x),
det_w = 2^-B(w), B(w) = 10 n_P + 12 n_Q.  D_w vanishes only where φ1 = φ2 = 0.  If the start and the end of the
word are integer states and D_w(x) ≠ 0, then 2^B(w) | D_w(x), so
    B(w) <= log2 |D_w(x)| <= 2 log2 E + h(w),   h(w) = log2(sum of |coefficients| of D_w)
(|D_w| <= 2^h(w) E^2 when 0 <= w_i <= E).  Prints B, h and the never-zero check for families of words."""
import sys, random, math
import sympy as sp
from periodic_locks import composite, X, lam, v2, int_zero_possible, w2, w3, w4, E
mons = [X[i] * X[j] for i in range(5) for j in range(i, 5)]
def norm_form(word):
    M = composite(word)
    cp = sp.factor_list(sp.Poly(M.charpoly(lam).as_expr(), lam))[1]
    q = [f for f, e in cp if sp.Poly(f, lam).degree() == 2]
    if not q: return None
    f = sp.Poly(q[0], lam); a2, a1, a0 = f.all_coeffs()
    det = sp.Rational(a0, a2)
    K = (a2 * M.T * M.T + a1 * M.T + a0 * sp.eye(5)).nullspace()
    assert len(K) == 2
    phis = [sp.expand((k.T * X)[0]) for k in K]
    Y = M * X
    sub = {X[i]: Y[i] for i in range(4)}
    c = sp.symbols('c0:3')
    Dg = c[0] * phis[0] ** 2 + c[1] * phis[0] * phis[1] + c[2] * phis[1] ** 2
    eq = sp.Poly(sp.expand(Dg.subs(sub, simultaneous=True) - det * Dg), w2, w3, w4, E).coeffs()
    sol = sp.linsolve(eq, c)
    (s,) = list(sol)
    free = [t for t in s if t.free_symbols]
    s = [sp.simplify(t.subs({fs: 1 for t2 in s for fs in t2.free_symbols})) for t in s]
    D = sp.expand(sum(ci * m for ci, m in zip(s, [phis[0] ** 2, phis[0] * phis[1], phis[1] ** 2])))
    p = sp.Poly(D, w2, w3, w4, E)
    den = sp.ilcm(*[sp.fraction(cc)[1] for cc in p.coeffs()])
    cs = [int(cc * den) for cc in p.coeffs()]; g = math.gcd(*cs)
    cs = [cc // g for cc in cs]
    h = math.log2(sum(abs(cc) for cc in cs))
    nz = not int_zero_possible(phis)
    nza = not int_zero_possible(phis, parity=False)
    return dict(B=-v2(det), h=h, never_zero=nz, never_zero_all=nza, D=sp.Poly(dict(zip(p.monoms(), cs)), w2, w3, w4, E))
if __name__ == '__main__':
    random.seed(7)
    fams = []
    for n in (1, 2, 4, 8, 16): fams.append('Q' * n); fams.append('PQ' * n); fams.append('PPQ' * n)
    for a, b in ((5, 5), (10, 10), (20, 20), (10, 30)): fams.append('P' * a + 'Q' + 'P' * b)
    for n in (4, 8, 12, 16, 24, 32, 48):
        for _ in range(3): fams.append(''.join(random.choice('PQ') for _ in range(n)))
    for w in fams:
        r = norm_form(w)
        if r is None: print(f"{w:40s} reducible"); continue
        print(f"{w if len(w) <= 40 else w[:37] + '...':40s} len {len(w):3d}  B {r['B']:4d}  h {r['h']:7.1f}  h/B {r['h'] / r['B']:.3f}  never-zero {r['never_zero']}", flush=True)
