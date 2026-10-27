import sympy as sp
from passmaps import P, Q
w2, w3, w4, E = sp.symbols('w2 w3 w4 E')
X = sp.Matrix([w2, w3, w4, E, 1])
def hom(M):  # 5x5 on (w2,w3,w4,E,1)
    rows = [M[1], M[2], M[3], M[4]]
    H = sp.zeros(5, 5)
    for i, r in enumerate(rows):
        for j, k in enumerate([1, 2, 3, 4, 5]): H[i, j] = sp.Rational(r[k].numerator, r[k].denominator)
    H[4, 4] = 1
    return H
HP, HQ = hom(P), hom(Q)
for name, H in (('P', HP), ('Q', HQ)):
    print(name, 'charpoly', sp.factor(H.charpoly().as_expr()))
    for lam, mult, vecs in H.T.eigenvects():
        for v in vecs:
            v = sp.simplify(v / v[[i for i in range(5) if v[i] != 0][-1]])
            print('  eig', sp.nsimplify(lam), 'form', [sp.nsimplify(sp.simplify(c)) for c in v])

print('--- quadratic lock for Q')
s17 = sp.sqrt(17)
lam = (13 + 3 * s17) / 256
N = (HQ.T - lam * sp.eye(5))
ns = N.nullspace()
assert len(ns) == 1
v = ns[0]
v = sp.Matrix([sp.radsimp(sp.expand(c)) for c in v])
psi = sp.expand((v.T * X)[0])
# psi = A + sqrt17 B with A,B rational affine
A = sp.expand(psi.subs(s17, 0)); B = sp.expand((psi - A) / s17)
D = sp.expand(A**2 - 17 * B**2)
# normalise to a primitive integer polynomial
poly = sp.Poly(D, w2, w3, w4, E)
den = sp.ilcm(*[sp.fraction(c)[1] for c in poly.coeffs()])
Dz = sp.Poly(sp.expand(D * den), w2, w3, w4, E)
g = sp.igcd(*[int(c) for c in Dz.coeffs()])
Dz = sp.Poly(sp.expand(Dz.as_expr() / g), w2, w3, w4, E)
print('D_Q =', Dz.as_expr())
# check invariance: D(Q x) = D(x)/4096
Y = HQ * X
Dq = Dz.as_expr().subs({w2: Y[0], w3: Y[1], w4: Y[2], E: Y[3]}, simultaneous=True)
print('D(Qx) - D(x)/4096 =', sp.simplify(sp.expand(Dq - Dz.as_expr() / 4096)))
open('DQ.txt', 'w').write(str(Dz.as_expr()) + '\n')

print('--- zero set of D_Q: A = B = 0')
sol = sp.solve([A, B], [w2, w3], dict=True)[0]
for k in (w2, w3): print(' ', k, '=', sol[k], '  =', sp.factor(sol[k]))
