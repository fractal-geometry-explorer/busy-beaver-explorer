"""Pass maps of the extra-wall loop's standard pass P and its detour Q (forced outcomes read off the C explorer), their
eigen-structure, and the cost of mixed sequences of P and Q by forced repetition (2-adic Smith form)."""
from fractions import Fraction as F
from math import gcd
from conc import Model, Pos, fmt
from snf2 import solve_info
geo = [21395686159, 412072778788, 1527835310093, 2817122580142, 3359928725359]
SC = 2 ** 200; big = [F(v) * SC for v in geo]
P_out = [2,2,2,2, 2,2,2,0, 0,2,2,2, 0, 0,2,2,2, 2]
Q_out = [2,2,0,0,0,2,2, 0,2, 0, 0,2,2,2, 0, 0,2,2,2, 2]
P_sh = ['GBWW', 'GWWWW', 'GBWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
Q_sh = ['GBWW', 'GMMWW', 'GMWWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
def setup():
    m = Model(5)
    for i in range(4): m.add('W', Pos([F(int(i == j)) for j in range(5)] + [F(0)], big[i]))
    m.W = Pos([F(int(j == 4)) for j in range(5)] + [F(0)], big[4]); m.add('G', m.const(1)); return m
def run_seq(seq):
    m = setup(); m.force = []
    for x in seq: m.force += (P_out if x == 'P' else Q_out)
    for x in seq:
        for want in (P_sh if x == 'P' else Q_sh):
            m.do_round()
            if m.bad or m.shape() != want: return None, f"{x}: got {m.shape()} want {want}"
    return m, None
def nullspace(A):
    A = [r[:] for r in A]; n = len(A[0]); piv = []; r = 0
    for col in range(n):
        p = next((i for i in range(r, len(A)) if A[i][col] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; pv = A[r][col]; A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][col] != 0: f = A[i][col]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(col); r += 1
    free = [j for j in range(n) if j not in piv]; out = []
    for fj in free:
        v = [F(0)] * n; v[fj] = F(1)
        for i, pc in enumerate(piv): v[pc] = -A[i][fj]
        out.append(v)
    return out
names = ['a', 'b', 'c', 'd', 'E']
for name, seq in (('P', 'P'), ('Q', 'Q')):
    m, err = run_seq(seq)
    if m is None: print(name, "failed:", err); continue
    print(f"pass {name}: {len(m.cong)} tests")
    for t, p in m.marks()[1:]: print("    ", t, fmt(p, names))
    print("     end", fmt(m.W, names))
    rows = [p.f[:5] for t, p in m.marks()[1:]] + [m.W.f[:5]]; trans = [p.f[5] for t, p in m.marks()[1:]] + [m.W.f[5]]
    for e in range(0, 12):
        mu = F(1, 2 ** e)
        for v in nullspace([[rows[i][j] - (mu if i == j else 0) for i in range(5)] for j in range(5)]):
            if mu == 1: continue
            vt = sum(a * b for a, b in zip(v, trans)); kappa = -vt / (1 - mu); co = v + [kappa]; den = 1
            for x in co: den = den * x.denominator // gcd(den, x.denominator)
            ints = [int(x * den) for x in co]; g = 0
            for x in ints[:5]: g = gcd(g, abs(x))
            print(f"     countdown x1/{2**e}: {ints[:5]} const {ints[5]} (coefficient gcd {g}, constant mod gcd {ints[5] % g})")
for seq in ('P', 'Q', 'PP', 'QQ', 'PQ', 'QP', 'PQP', 'QPQ', 'PPQQ', 'PQPQ', 'QQQQ', 'PQQPQ'):
    m, err = run_seq(seq)
    if m is None: print(seq, "failed:", err); continue
    b, ok, S = solve_info(m.cong, 5)
    print(f"sequence {seq:6s}: bits {b} ({b / len(seq):.1f} per pass), solvable {ok}")
