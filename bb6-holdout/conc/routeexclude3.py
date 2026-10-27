"""Faster single-stretch exclusion (same method as routeexclude2.py, slack 12): integer positions (fasttree.P), the
route run once, plain passes added one at a time with their congruences imposed incrementally.
usage: routeexclude3.py routes.jsonl kmin kmax candidates_out summary_out [slack]"""
import sys, json, math
from fractions import Fraction as F
from lattice import Coset as LCoset
import fasttree as FT
import routeexclude as RX
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import CYC, outs as L_out
SC = FT.SC

class Forced(FT.M):
    __slots__ = ('cong',)
    def test_outcome(self, d):
        if self.fi >= len(self.forced): raise FT.Branch()
        res = self.forced[self.fi]; self.fi += 1
        self.cong.append((d.f, res)); return res

def start(ratio, scale):
    m = Forced.__new__(Forced); m.T = []; m.Ps = []; m.A = []; m.halted = False; m.bad = 0; m.outcomes = []; m.rd = 0
    m.coset = None; m.forced = []; m.fi = 0; m.cong = []
    E = scale; mv = int(E * ratio) // 2 * 2
    m.W = FT.P((0, SC, 0), (E + 1) * SC)
    m.add('G', FT.const(1)); m.add('M', FT.P((SC, 0, 0), mv * SC)); m.add('M', m.W.add(-2))
    return m

def run(m, shapes, outs):
    m.forced = list(outs); m.fi = 0
    for want in shapes:
        try: m.do_round()
        except (FT.Branch, AssertionError): return False
        if m.bad or m.halted or m.shape() != want: return False
    return m.fi == len(m.forced)

def impose_all(C, congs):
    for f, res in congs:
        # (f . (m, E, 1)) / SC = d ;  d = res (mod 4)  ->  f0 m + f1 E = SC*res - f2 (mod 4 SC)
        if not C.impose([f[0], f[1]], SC * res - f[2], 4 * SC, reduce=False): return False
    return True

if __name__ == '__main__':
    routes = [json.loads(l) for l in open(sys.argv[1])]
    kmin, kmax = int(sys.argv[2]), int(sys.argv[3])
    S = int(sys.argv[6]) if len(sys.argv) > 6 else 12
    cand = open(sys.argv[4], 'w'); summ = open(sys.argv[5], 'w')
    for idx, r in enumerate(routes):
        for phase in ('A', 'B'):
            shapes = list(r['shapes']); outs = list(r['outs'])
            if phase == 'B': shapes += ['GBW', 'GWWW']; outs += [2, 2, 2]
            m = start(r['ratio'], 2 ** 300)
            if not run(m, shapes, outs): summ.write(f"{idx} {phase} prefix geometry fails\n"); continue
            mk = m.marks(); d = m.W.minus(mk[-1][1])
            a, b = F(d.f[0], SC), F(d.f[1], SC)
            lo = min(b, a + b)
            if lo <= 0: summ.write(f"{idx} {phase} UNBOUNDED route halvings\n"); continue
            H = math.log2(1 / float(lo))
            kcap = min(kmax, int(3 * H + 3 * S + 18.26) + 1)
            pmax = max(1, math.ceil((kcap - S - H) / 4))
            C = LCoset(2)
            ok = impose_all(C, m.cong) and C.impose([1, 0], 0, 2, reduce=False) and C.impose([0, 1], 1, 2, reduce=False)
            cos = {}
            done = 0
            for p in range(1, pmax + 1):
                if not ok: break
                m.cong = []
                if not run(m, CYC, L_out): break
                ok = impose_all(C, m.cong)
                if ok: cos[p] = LCoset(2); cos[p].x0 = list(C.x0); cos[p].B = [row[:] for row in C.B]
            total = 0
            for k in range(kmin, kcap + 1):
                p = max(1, math.ceil((k - S - H) / 4))
                if p not in cos: continue
                for mm, E in RX.points(cos[p], k):
                    cand.write(f"{mm} {E}\n"); total += 1
            summ.write(f"{idx} {phase} H={H:.2f} kmax={kcap} consistent_p={sorted(cos)} candidates={total} measure={r['measure']:.3e} {' '.join(shapes)}\n")
        if idx % 50 == 0: summ.flush(); cand.flush()
    print("done")
