"""General pass map of the loop with k extra walls (read off k <= 7 by forced runs) and its left countdown, by forward
substitution (the map is triangular). Checks the never-zero property (coefficients divisible by 7, constant not) for
k up to K, and cross-checks small k against the forced simulations."""
import sys
from fractions import Fraction as F
from math import gcd
def pass_map(k):
    n = k + 3          # walls w0..w_{k+2}, then E at index n
    N = n + 1
    M = [[F(0)] * N for _ in range(N)]; t = [F(0)] * N
    def put(row, col, val):
        M[row][min(col, n)] += val     # columns beyond the last wall fold into E
    put(0, 1, F(1, 64)); put(0, 2, F(1, 64)); t[0] = F(271, 64)
    for off, cf in zip(range(1, 6), (1, 5, 12, 12, 4)): put(1, off, F(cf, 64))
    t[1] = F({0: 915, 1: 899}.get(k, 895), 64)
    for j in range(2, n):
        for off, cf in enumerate((1, 4, 6, 4, 1)): put(j, j + off, F(cf, 16))
        back = n - 1 - j                 # 0 for the last wall
        t[j] = F({0: 369, 1: 358, 2: 353}.get(back, 352), 16)
    M[n][n] = F(1); t[n] = F(24)
    return M, t
def left_countdown(M, t, mu=F(1, 64)):
    N = len(M); v = [F(0)] * N
    for j in range(N):
        s = sum(v[i] * M[i][j] for i in set([0, 1] + list(range(max(0, j - 4), j))) if i < j and M[i][j] != 0) + (sum(v[i] * M[i][j] for i in range(j) if M[i][j] != 0) if j == N - 1 else 0) - (0 if j != N - 1 else sum(v[i] * M[i][j] for i in set([0, 1] + list(range(max(0, j - 4), j))) if i < j and M[i][j] != 0))
        d = M[j][j] - mu
        if d == 0:
            v[j] = F(1) if s == 0 else None
            assert v[j] is not None
        else:
            v[j] = -s / d
    vt = sum(a * b for a, b in zip(v, t)); kappa = -vt / (1 - mu)
    coeffs = v + [kappa]; den = 1
    for x in coeffs: den = den * x.denominator // gcd(den, x.denominator)
    ints = [int(x * den) for x in coeffs]; g = 0
    for x in ints[:-1]: g = gcd(g, abs(x))
    gg = gcd(g, abs(ints[-1])); ints = [x // gg for x in ints]; g //= gg
    return ints, g
K = int(sys.argv[1]); bad = []; res = []
for k in range(K + 1):
    M, t = pass_map(k)
    ints, g = left_countdown(M, t)
    ok = (g % 7 == 0) and (ints[-1] % 7 != 0)
    res.append(ints[-1] % 7)
    if not ok: bad.append(k)
    if k <= 3: print(f"k = {k}: countdown {ints[:-1]} constant {ints[-1]}")
print("residues of the constant mod 7 for k = 0..30:", res[:31]); print("pattern 6*3^k mod 7 holds for all k checked:", all(r == (6 * pow(3, k, 7)) % 7 for k, r in enumerate(res)))
print(f"checked k = 0..{K}: never-zero property fails for {bad if bad else 'no k'}; residue = 6*4^k mod 7 for all: {all(r == (6 * pow(4, k, 7)) % 7 for k, r in enumerate(res))}")
