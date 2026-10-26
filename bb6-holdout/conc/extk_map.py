"""Does the loop run with k extra walls near the end? Generic state G W^(3+k), every position free, explore branches up
to a bit cap and report the probability that one pass of the loop pattern (with k extra W's) completes."""
import sys, copy, itertools, collections
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
k = int(sys.argv[1]); cap = int(sys.argv[2])
EXT = [s + 'W' * k for s in LOOP]
nw = 3 + k; nv = nw + 1
E = 10 ** 6
if len(sys.argv) > 3:
    geo = [int(x) for x in sys.argv[3].split(',')]; E = geo.pop()
else:
    geo = [150000, 650000] + [1000000 - 30000 // (2 ** i) for i in range(k + 1)]
    geo = sorted(geo)
SC = 2 ** 200; big = [F(v) * SC for v in geo] + [F(E) * SC]
found = collections.Counter(); tot = F(0)
for par in itertools.product((0, 1), repeat=nv):
    m = TModel(nv)
    for i in range(nw): m.add('W', Pos([F(int(i == j)) for j in range(nv)] + [F(0)], big[i]))
    m.W = Pos([F(int(j == nv - 1)) for j in range(nv)] + [F(0)], big[-1]); m.add('G', m.const(1)); m.run = []; m.hist = [EXT[0]]
    c = Coset(list(par), [[2 * (i == j) for j in range(nv)] for i in range(nv)])
    stack = [(m, c, [])]; comp = F(0); capped = 0
    while stack:
        m0, c0, fo = stack.pop()
        mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = fo; ne0 = len(mm.endd)
        try: mm.do_round()
        except Branch:
            if c0.bits + len(fo) + 1 > cap: capped += 1; continue
            stack.append((m0, c0, fo + [0])); stack.append((m0, c0, fo + [2])); continue
        except AssertionError: continue
        if mm.halted or mm.bad: continue
        mm.hist.append(mm.shape())
        h = mm.hist; L = len(h)
        if not any(all(h[q] == EXT[(ph + q) % 8] for q in range(L)) for ph in (0, 6)): continue
        broken = False
        for (rr, d) in mm.endd[ne0:]:
            if mm.run and pred_form(*mm.run[-1]).f != d.f: broken = True; break
            mm.run.append((d, cc.decided(d.f)))
        if broken: continue
        if L == 9:
            comp += F(1, 2 ** cc.bits); found[tuple(mm.outcomes)] += 1
            if 'model' not in globals(): globals()['model'] = mm
            continue
        stack.append((mm, cc, []))
    if comp: print(f"parities {par}: P(pass with {k} extra walls completes) = {comp} (= 2^-{(1/comp).numerator.bit_length() - 1}), capped {capped}", flush=True)
    tot += comp
print("outcome sequences of completed passes:", list(found.items())[:3])

from math import gcd
from conc import fmt
mm = model
names = ['w%d' % i for i in range(nw)] + ['E']
rows = [p.f[:nv] for t, p in mm.marks()[1:]] + [mm.W.f[:nv]]
trans = [p.f[nv] for t, p in mm.marks()[1:]] + [mm.W.f[nv]]
print("pass map:")
for (t, p) in mm.marks()[1:]: print("   ", t, fmt(p, names))
print("    end", fmt(mm.W, names))
def nullspace(A):
    A = [r[:] for r in A]; n = len(A[0]); piv = []; r = 0
    for col in range(n):
        pv_ = next((i for i in range(r, len(A)) if A[i][col] != 0), None)
        if pv_ is None: continue
        A[r], A[pv_] = A[pv_], A[r]; pv = A[r][col]; A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][col] != 0:
                f = A[i][col]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(col); r += 1
    free = [j for j in range(n) if j not in piv]; out = []
    for fj in free:
        v = [F(0)] * n; v[fj] = F(1)
        for i, pc in enumerate(piv): v[pc] = -A[i][fj]
        out.append(v)
    return out
for e in (0, 4, 6):
    mu = F(1, 2 ** e)
    A = [[rows[i][j] - (mu if i == j else 0) for i in range(nv)] for j in range(nv)]
    for v in nullspace(A):
        vt = sum(vi * ti for vi, ti in zip(v, trans))
        if mu == 1: print("  invariant direction:", [str(x) for x in v]); continue
        kappa = -vt / (1 - mu); coeffs = list(v) + [kappa]
        den = 1
        for x in coeffs: den = den * x.denominator // gcd(den, x.denominator)
        ints = [int(x * den) for x in coeffs]; g = 0
        for x in ints[:nv]: g = gcd(g, abs(x))
        print(f"  countdown x1/{2**e}: coefficients {ints[:nv]}, constant {ints[nv]}; gcd of coefficients {g}; constant mod gcd {ints[nv] % g}")
