"""Never-zero countdowns ("locks") for every periodic word of the one-extra-wall loop.

For a word w over {P, Q} (ℓ letters, n_P and n_Q of each) the composite pass map is affine on (w2, w3, w4, E)
(w1 is forgotten).  Its characteristic polynomial is (λ − 1)² (16^ℓ λ − 1) q(λ): E and the constant, the common end
countdown R = E − w4 − 1, and a quadratic factor q for the two left directions, with q(0)/lead = 2^-B,
B = 10 n_P + 12 n_Q (the left blocks of P and Q have determinants 2^-10 and 2^-12).
  - q irreducible over Q: D_w (see word_height.py) is an integer quadratic with D_w∘w = 2^-B D_w; it vanishes only on
    the rational subspace φ1 = φ2 = 0, checked here to hold no integer point of the tape's parity class (w2 even,
    w3 odd, w4 even, E odd).  Repeating w n times from integer states then needs 2^(Bn) | D_w(x0) ≠ 0, so
    n ≤ (2 log2 E + h_w)/B: the stretch makes at most (8ℓ/B) log2 E + 4ℓ h_w/B halvings.
  - q reducible (rational roots ±m/2^k): each root has a rational eigenform φ, a lock of degree 1 and k bits when
    φ = 0 has no integer point; P is this case (L₂, 6 bits; its other left root 1/16 is R's Jordan partner).
The rate of the best lock is 4ℓ·deg/bits.  For comparison, the fixed-point argument of the notes ("The general form
of the lock": x − x* shrinks like the slowest real eigenvalue ρ) gives 4ℓ / log2(1/ρ).
usage: python3 periodic_locks.py [maxlen]"""
import sys, itertools, math
import sympy as sp
from passmaps import P, Q
from zsolve import solvable
w2, w3, w4, E = V = sp.symbols('w2 w3 w4 E')
X = sp.Matrix([w2, w3, w4, E, 1])
lam = sp.symbols('lam')
def hom(M):
    H = sp.zeros(5, 5)
    for i in range(4):
        for j in range(5): H[i, j] = sp.Rational(M[i + 1][j + 1].numerator, M[i + 1][j + 1].denominator)
    H[4, 4] = 1
    return H
H = {'P': hom(P), 'Q': hom(Q)}
def composite(word):
    M = sp.eye(5)
    for c in word: M = H[c] * M      # first letter acts first
    return M
def v2(r):
    r = sp.Rational(r); n, d = r.p, r.q; k = 0
    while n % 2 == 0: n //= 2; k += 1
    while d % 2 == 0: d //= 2; k -= 1
    return k
def int_zero_possible(forms, parity=True):
    """Do the rational affine forms (in w2..E) vanish together at some integer point (of the parity class)?"""
    if parity:
        a, b, c, d = vs = sp.symbols('a b c d', integer=True)
        sub = {w2: 2 * a, w3: 2 * b + 1, w4: 2 * c, E: 2 * d + 1}
    else:
        vs = V; sub = {}
    A, bb = [], []
    for f in forms:
        g = sp.expand(f.subs(sub, simultaneous=True)) if sub else sp.expand(f)
        p = sp.Poly(g, *vs)
        den = sp.ilcm(*[sp.fraction(sp.Rational(c))[1] for c in p.coeffs()] + [1])
        p = sp.Poly(sp.expand(g * den), *vs)
        A.append([int(p.coeff_monomial(v)) for v in vs]); bb.append(-int(p.coeff_monomial(1)))
    return solvable(A, bb)
def lyndon(n):
    out = []
    for t in itertools.product('PQ', repeat=n):
        w = ''.join(t)
        if all(w < w[i:] + w[:i] for i in range(1, n)): out.append(w)
    return out
def analyse(word):
    from word_height import norm_form
    l = len(word); M = composite(word)
    cp = sp.factor_list(sp.Poly(M.charpoly(lam).as_expr(), lam))[1]
    left = [sp.Poly(f, lam) for f, e in cp for _ in range(e)
            if sp.Poly(f, lam).eval(1) != 0 and sp.Poly(f, lam).eval(sp.Rational(1, 16 ** l)) != 0]
    leftroots = [complex(r) for f in left for r in sp.Poly(f, lam).nroots()]
    # the left block also contains 16^-ℓ for P-type Jordan partners: include multiplicity beyond R's own
    mult16 = sum(e for f, e in cp if sp.Poly(f, lam).eval(sp.Rational(1, 16 ** l)) == 0)
    if mult16 > 1: leftroots += [16.0 ** -l] * (mult16 - 1)
    rho = max(abs(r) for r in leftroots)
    fp_rate = 4 * l / math.log2(1 / rho)
    locks = []
    for f in left:
        if f.degree() == 2:
            r = norm_form(word)
            locks.append(dict(kind='norm', deg=2, B=r['B'], h=r['h'], never_zero=r['never_zero'],
                              nz_all=r['never_zero_all']))
        else:
            for root in sp.roots(f.as_expr(), lam):
                for v in (M.T - root * sp.eye(5)).nullspace():
                    phi = sp.expand(sum(c * x for c, x in zip(v, X)))
                    p = sp.Poly(phi, *V); den = sp.ilcm(*[sp.fraction(c)[1] for c in p.coeffs()])
                    cs = [int(c * den) for c in p.coeffs()]; g = math.gcd(*cs)
                    h = math.log2(sum(abs(c) // g for c in cs))
                    locks.append(dict(kind='linear', deg=1, B=-v2(root), h=h, never_zero=not int_zero_possible([phi]),
                                      nz_all=not int_zero_possible([phi], parity=False), root=root))
    best = max((lk for lk in locks if lk['never_zero']), key=lambda lk: sp.Rational(lk['B'], lk['deg']), default=None)
    rate = sp.Rational(4 * l * best['deg'], best['B']) if best else None
    return locks, best, rate, fp_rate
if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    worst, worst_fp, nwords, nz_all = (0, None), (0, None), 0, 0
    for n in range(1, maxlen + 1):
        for w in lyndon(n):
            locks, best, rate, fp = analyse(w); nwords += 1
            nz_all += all(lk['nz_all'] for lk in locks if lk is best)
            desc = '; '.join(f"{lk['kind']} B={lk['B']} h={lk['h']:.1f}" + ('' if lk['never_zero'] else ' CAN VANISH')
                             for lk in locks)
            print(f"{w:14s} nP={w.count('P'):2d} nQ={w.count('Q'):2d}  lock rate {str(rate):8s} = "
                  f"{float(rate) if rate else float('nan'):.4f}   fixed-point rate {fp:.3f}   [{desc}]", flush=True)
            if rate is None or rate > worst[0]: worst = (rate if rate else 99, w)
            if fp > worst_fp[0]: worst_fp = (fp, w)
    print(f"words: {nwords}; best lock never 0 on all integer points (not only the parity class): {nz_all}")
    print('largest lock rate:', worst, float(worst[0]))
    print('largest fixed-point rate:', worst_fp)
