"""Second route into the loop, G M B -> G M M M -> G M M W -> G M W W -> G W W W: the countdowns as forms in the
route's first state (marker m, block r, end E), and the gap in terms of those integers on the actual lines."""
import sys, collections
from fractions import Fraction as F
from conc import Model, Pos, fmt
from depthslack import v2f
ROUTE = ['GMB', 'GMMM', 'GMMW', 'GMWW', 'GWWW', 'GBW', 'GMB']
def find(n0):
    m = Model(1); m.W = Pos([F(1), F(6)], 2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2)
    snaps = []; outs_at = []
    for r in range(4000):
        snaps.append((m.shape(), [(t, p) for t, p in m.marks()[1:]], m.W, len(m.outcomes)))
        m.do_round()
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    snaps.append((m.shape(), [(t, p) for t, p in m.marks()[1:]], m.W, len(m.outcomes)))
    sh = [s[0] for s in snaps]
    res = []
    for i in range(len(sh) - 6):
        if sh[i:i + 7] == ROUTE:
            res.append((i, snaps[i], snaps[i + 4], m.outcomes[snaps[i][3]: snaps[i + 4][3]]))
    return res
def symbolic(start_snap, forced):
    sh, marks, W, _ = start_snap
    (tm, pm), (tb, pb) = marks
    md = Model(3)   # variables m, r, E
    md.W = Pos([F(0), F(0), F(1), F(0)], F(W.v) * 2 ** 100)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0), F(0)], F(pm.v) * 2 ** 100)); md.add('B', Pos([F(0), F(1), F(0), F(0)], F(pb.v) * 2 ** 100))
    md.force = list(forced)
    for want in ROUTE[1:5]:
        md.do_round()
        if md.bad or md.shape() != want: return None
    mk = md.marks(); a, b, c = [p for t, p in mk[1:]]; WW = md.W
    R = WW - c - 1
    L = Pos([1029 * x + 1960 * y - 2744 * z for x, y, z in zip(b.f, WW.f, c.f)], 0) - 4046
    return R, L
if __name__ == '__main__':
    seen = set()
    for l in open(sys.argv[1]):
        n0 = int(l.split()[0])
        for (i, s0, s4, forced) in find(n0):
            out = symbolic(s0, forced)
            if out is None: continue
            R, L = out
            key = (fmt(R, ['m', 'r', 'E']), fmt(L, ['m', 'r', 'E']))
            if key not in seen: seen.add(key); print("R =", key[0], "   L =", key[1])
            # the line: m = lm N + km, r = lr N + kr, E = N + kE ; actual gap from the pass-start state
            sh, marks, W, _ = s0
            (tm, pm), (tb, pb) = marks
            def s_of(p):
                d = p.f[0].denominator; s = 0
                while d > 1: d //= 2; s += 1
                return s
            # compose R, L with the line
            lam = [pm.f[0], pb.f[0], W.f[0]]; kap = [pm.f[1], pb.f[1], W.f[1]]
            lR = sum(R.f[k] * lam[k] for k in range(3)); kR = R.f[3] + sum(R.f[k] * kap[k] for k in range(3))
            lL = sum(L.f[k] * lam[k] for k in range(3)); kL = L.f[3] + sum(L.f[k] * kap[k] for k in range(3))
            D = lR * kL - lL * kR; GR = v2f(D) - v2f(lL)
            print(f"   n={n0} round {i}: depths s(m)={s_of(pm)} s(r)={s_of(pb)}  G_R={GR}  W mod 2^12={W.v % 4096}  r mod 2^12={pb.v % 4096}  m mod 2^12={pm.v % 4096}")
