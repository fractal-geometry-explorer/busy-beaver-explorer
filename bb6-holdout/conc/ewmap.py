"""The affine map of extra-wall pass words on (w1, w2, w3, w4, E): rational eigenvalues and left eigenforms
(countdowns phi(x) + c with phi(Mx + t) + c = lam (phi(x) + c))."""
from fractions import Fraction as F
import mixsolve as MS
def nullspace(A):
    A = [row[:] for row in A]; n = len(A[0]); piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; A[r] = [x / A[r][c] for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0: A[i] = [a - A[i][c] * b for a, b in zip(A[i], A[r])]
        piv.append(c); r += 1
    free = [c for c in range(n) if c not in piv]; out = []
    for f in free:
        v = [F(0)] * n; v[f] = F(1)
        for i, c in enumerate(piv): v[c] = -A[i][f]
        out.append(v)
    return out
def charpoly_roots(M):
    n = len(M); roots = []
    cands = [F(s, 2 ** k) for k in range(0, 13) for s in (1, -1)] + [F(s * 3, 2 ** k) for k in range(0, 13) for s in (1, -1)]
    for lam in cands:
        A = [[M[j][i] - (lam if i == j else 0) for j in range(n)] for i in range(n)]   # (M^T - lam)
        ns = nullspace(A)
        if ns: roots.append((lam, ns))
    return roots
if __name__ == "__main__":
 for word in ("P", "Q", "PP", "PQ"):
     m = MS.forced(word)
     mk = m.marks(); pos = [p for t, p in mk[1:]] + [m.W]
     M = [[p.f[j] for j in range(5)] for p in pos]; t = [p.f[5] for p in pos]
     print(f"== {word}: rows = new positions as forms in (w1, w2, w3, w4, E)")
     for row, tt in zip(M, t): print("   ", [str(x) for x in row], "+", tt)
     tot = 0
     for lam, vecs in charpoly_roots(M):
         for v in vecs:
             den = 1
             for x in v: den = den * x.denominator // __import__('math').gcd(den, x.denominator)
             v = [x * den for x in v]
             phit = sum(a * b for a, b in zip(v, t))
             c = phit / (lam - 1) if lam != 1 else None
             print(f"  eigenvalue {lam}: form {[str(x) for x in v]} + {c}")
             tot += 1
     print("  eigenforms found:", tot, " congruences:", len(m.cong))
