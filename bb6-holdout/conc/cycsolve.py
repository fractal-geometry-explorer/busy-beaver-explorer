import sys
from conc import *
from cyccost import setup, CYC, outs, vals, big
from snf2 import v2
from fractions import Fraction as F
sys.setrecursionlimit(10000)
NC = int(sys.argv[1])
m = setup(big, False); m.force = outs * NC
for c in range(NC):
    for want in CYC: m.do_round(); assert m.shape() == want
cons = []
for pform, res, mod in m.cong:
    form = pform.f; den = max(a.denominator for a in form)
    M = [int(a * den) for a in form[:4]]; cc = int(form[4] * den)
    cons.append((M, den * res - cc, v2(den * mod)))
S = max(c[2] for c in cons)
def ok(x, k):
    for M, t, s in cons:
        q = min(k, s); md = 1 << q
        if (sum(a * b for a, b in zip(M, x)) - t) % md: return False
    return True
def dfs(x, k):
    if k == S: return x
    for bits in range(16):
        y = [x[i] | (((bits >> i) & 1) << k) for i in range(4)]
        if ok(y, k + 1):
            r = dfs(y, k + 1)
            if r: return r
    return None
sol = dfs([0, 0, 0, 0], 0)
print("solution mod 2^%d:" % S, sol)
# lift into the geometry of the sample: nearest values to the sample's that agree mod 2^S
MOD = 1 << S
scale = 2 ** 40 if len(sys.argv) < 3 else int(sys.argv[2])
target = [v * scale // vals[3] * 1 for v in vals]
x = [t - ((t - s) % MOD) for t, s in zip(target, sol)]
print("start GWWW state:", x)
mm = Model(1); mm.W = mm.const(x[3]); mm.add('G', mm.const(1))
for v in x[:3]: mm.add('W', mm.const(v))
shapes = []
for rd in range(8 * NC + 40):
    mm.do_round(); shapes.append(mm.shape())
    if mm.halted or mm.bad: print("halted/bad", mm.halted, mm.bad); break
    mk = mm.marks()
    if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2: break
print("shapes:", ' '.join(shapes))
ends = [r for r, d in mm.endd]
print("end meetings at rounds:", ends)
