"""Polynomials f in (w2, w3, w4, E) of degree <= d with f∘P = λ f and f∘Q = μ f (common eigen-polynomials)."""
import sympy as sp, itertools, sys
from passmaps import P, Q
w2, w3, w4, E = V = sp.symbols('w2 w3 w4 E')
def img(M):
    return {v: sum(sp.Rational(M[i + 1][j + 1].numerator, M[i + 1][j + 1].denominator) * V[j] for j in range(4)) +
            sp.Rational(M[i + 1][5].numerator, M[i + 1][5].denominator) for i, v in enumerate(V)}
iP, iQ = img(P), img(Q)
d = int(sys.argv[1]) if len(sys.argv) > 1 else 2
mons = [m for k in range(d + 1) for m in itertools.combinations_with_replacement(V, k)]
mons = [sp.Mul(*m) for m in mons]
def opmat(im):
    rows = []
    for m in mons:
        f = sp.Poly(sp.expand(m.subs(im, simultaneous=True)), *V)
        rows.append([f.coeff_monomial(mm) for mm in mons])
    return sp.Matrix(rows).T   # column j = image of monomial j
CP, CQ = opmat(iP), opmat(iQ)
evP = CP.eigenvals(); evQ = CQ.eigenvals()
print('eigenvalues P:', evP); print('eigenvalues Q (rational ones):', {k: v for k, v in evQ.items() if k.is_rational})
n = len(mons)
for lp in evP:
    for lq in evQ:
        if not lq.is_rational: continue
        Mst = (CP - lp * sp.eye(n)).col_join(CQ - lq * sp.eye(n))
        ns = Mst.nullspace()
        for v in ns:
            f = sp.factor(sum(c * m for c, m in zip(v, mons)))
            print(f'  λP={lp} λQ={lq}:', f)
