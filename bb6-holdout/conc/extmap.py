"""Find one completed pass of the extended loop (G W W W W ...) by exact branching, then print its pass map and
look for countdowns: linear combinations of (a, b, c, d, E, 1) that the map divides by a power of 2."""
import sys, copy, itertools
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
from conc import fmt
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
EXT = [s + 'W' for s in LOOP]
geo = [int(x) for x in sys.argv[1].split(',')]; par = tuple(int(x) for x in sys.argv[2])
SC = 2 ** 200; big = [F(v) * SC for v in geo]; nv = 5
m = TModel(nv)
for i in range(4): m.add('W', Pos([F(int(i == j)) for j in range(nv)] + [F(0)], big[i]))
m.W = Pos([F(int(j == 4)) for j in range(nv)] + [F(0)], big[4]); m.add('G', m.const(1)); m.run = []; m.hist = ['GWWWW']
c = Coset(list(par), [[2 * (i == j) for j in range(nv)] for i in range(nv)])
stack = [(m, c, [])]; found = []
while stack and len(found) < 4:
    m0, c0, fo = stack.pop()
    mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = fo; ne0 = len(mm.endd)
    try: mm.do_round()
    except Branch:
        if c0.bits + len(fo) + 1 > 40: continue
        stack.append((m0, c0, fo + [0])); stack.append((m0, c0, fo + [2])); continue
    except AssertionError: continue
    if mm.halted or mm.bad: continue
    mm.hist.append(mm.shape()); broken = False
    for (rr, d) in mm.endd[ne0:]:
        if mm.run and pred_form(*mm.run[-1]).f != d.f: broken = True; break
        mm.run.append((d, cc.decided(d.f)))
    if len(mm.hist) == 9 and not broken and any(all(mm.hist[k] == EXT[(ph + k) % 8] for k in range(9)) for ph in (0, 6)):
        found.append((mm, cc)); continue
    mk = mm.marks(); fin = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
    if broken or fin or len(mm.hist) > 12: continue
    stack.append((mm, cc, []))
names = ['a', 'b', 'c', 'd', 'E']
for mm, cc in found:
    print("pass:", ' '.join(mm.hist), "| run meetings", len(mm.run), "| bits", cc.bits)
    mk = mm.marks()
    for t, p in mk[1:]: print("   ", t, fmt(p, names))
    print("    end", fmt(mm.W, names))
    # linear part of the map (rows: new a..E in terms of old)
    rows = [p.f[:5] for t, p in mk[1:]] + [mm.W.f[:5]]
    def nullspace(A):
        A = [r[:] for r in A]; n = len(A[0]); piv = []; r = 0
        for col in range(n):
            p = next((i for i in range(r, len(A)) if A[i][col] != 0), None)
            if p is None: continue
            A[r], A[p] = A[p], A[r]; pv = A[r][col]; A[r] = [x / pv for x in A[r]]
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
    # countdown: v with v . new = mu * (v . old) for the linear part: sum_i v_i rows[i][j] = mu v_j
    for e in range(0, 13):
        mu = F(1, 2 ** e)
        A = [[rows[i][j] - (mu if i == j else 0) for i in range(5)] for j in range(5)]
        for v in nullspace(A):
            print(f"    countdown with factor 1/{2**e}: coefficients on (a, b, c, d, E) =", [str(x) for x in v])
    break
