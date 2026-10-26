"""Integer lattice helpers: cosets of congruence systems, LLL, Babai nearest point."""
from fractions import Fraction as F

def egcd(a, b):
    if b == 0: return (abs(a), (1 if a >= 0 else -1), 0)
    x0, y0, x1, y1 = 1, 0, 0, 1; aa, bb = a, b
    while bb: q = aa // bb; aa, bb = bb, aa - q * bb; x0, x1 = x1, x0 - q * x1; y0, y1 = y1, y0 - q * y1
    if aa < 0: aa, x0, y0 = -aa, -x0, -y0
    return aa, x0, y0

def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]

def lll(B, delta=F(99, 100)):
    """B: list of basis vectors (rows). Returns LLL-reduced rows."""
    B = [list(v) for v in B]; n = len(B)
    def dot(u, v): return sum(a * b for a, b in zip(u, v))
    def gs():
        Bs = []; mu = [[F(0)] * n for _ in range(n)]
        for i in range(n):
            v = [F(x) for x in B[i]]
            for j in range(i):
                mu[i][j] = F(dot(B[i], Bs[j])) / dot(Bs[j], Bs[j]) if any(Bs[j]) else F(0)
                v = [a - mu[i][j] * b for a, b in zip(v, Bs[j])]
            Bs.append(v)
        return Bs, mu
    Bs, mu = gs(); k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            q = round(mu[k][j])
            if q:
                B[k] = [a - q * b for a, b in zip(B[k], B[j])]
                Bs, mu = gs()
        if dot(Bs[k], Bs[k]) >= (delta - mu[k][k - 1] ** 2) * dot(Bs[k - 1], Bs[k - 1]): k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]; Bs, mu = gs(); k = max(k - 1, 1)
    return B

def babai(B, t):
    """Lattice vector (integer combination of rows of B) near the real target t (nearest-plane)."""
    n = len(B)
    def dot(u, v): return sum(a * b for a, b in zip(u, v))
    Bs = []
    for i in range(n):
        v = [F(x) for x in B[i]]
        for j in range(i):
            mu = F(dot(B[i], Bs[j])) / dot(Bs[j], Bs[j]); v = [a - mu * b for a, b in zip(v, Bs[j])]
        Bs.append(v)
    b = [F(x) for x in t]; out = [0] * len(t)
    for i in range(n - 1, -1, -1):
        c = round(dot(b, Bs[i]) / dot(Bs[i], Bs[i]))
        b = [x - c * y for x, y in zip(b, B[i])]; out = [x + c * y for x, y in zip(out, B[i])]
    return out

def lg(x):
    x = abs(int(x))
    if x == 0: return float('-inf')
    b = x.bit_length(); sh = max(0, b - 60)
    import math
    return math.log2(x >> sh) + sh

class Coset:
    """x = x0 + (integer combination of rows of B)."""
    def __init__(self, n):
        self.n = n; self.x0 = [0] * n; self.B = [[int(i == j) for j in range(n)] for i in range(n)]; self.ok = True
    def impose(self, M, r, m, reduce=True):
        """M.x = r (mod m), M integer row."""
        n = self.n
        v = [sum(a * b for a, b in zip(M, row)) for row in self.B] + [m]
        rhs = r - sum(a * b for a, b in zip(M, self.x0))
        U = [[int(i == j) for j in range(n + 1)] for i in range(n + 1)]   # columns ops on v: v U = (g,0,...)
        for j in range(1, n + 1):
            p, q = v[0], v[j]
            if q == 0: continue
            g, s, t = egcd(p, q)
            for row in U:
                c0, cj = row[0], row[j]; row[0] = s * c0 + t * cj; row[j] = (-q // g) * c0 + (p // g) * cj
            v[0], v[j] = g, 0
        g = v[0]
        if rhs % g: self.ok = False; return False
        y = [(rhs // g) * U[i][0] for i in range(n)]
        self.x0 = [a + sum(y[i] * self.B[i][k] for i in range(n)) for k, a in enumerate(self.x0)]
        Y = [[U[i][j] for i in range(n)] for j in range(1, n + 1)]     # kernel vectors (as rows, first n coords)
        self.B = matmul(Y, self.B)
        if reduce: self.B = lll(self.B)
        return True
    def index_bits(self):
        # |det B|
        import math
        n = self.n; M = [[F(x) for x in row] for row in self.B]; det = F(1)
        for c in range(n):
            p = next(i for i in range(c, n) if M[i][c] != 0)
            if p != c: M[c], M[p] = M[p], M[c]; det = -det
            det *= M[c][c]
            for i in range(c + 1, n):
                f = M[i][c] / M[c][c]; M[i] = [a - f * b for a, b in zip(M[i], M[c])]
        det = abs(det); return lg(det.numerator) - lg(det.denominator)
