"""Why does the main route into the loop (G M M, G M M M, G M M W, G M W W, then G W W W) never give a gap above 8?
Run the route symbolically from its first state with the free positions (marker m, end E; the end marker is tied to
E - 2), forcing the outcomes a real clean tape took, and look at the two countdowns as forms in (m, E)."""
import sys
from fractions import Fraction as F
from conc import Model, Pos, fmt
from lattice import Coset, lll
from snf2 import v2
def concrete_run(n0):
    m = Model(1); m.W = m.const(2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2)
    states = []; outs = []
    for r in range(1, 4000):
        mk = m.marks(); states.append((m.shape(), [p.v for t, p in mk[1:]], m.W.v, len(m.outcomes)))
        m.do_round()
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    states.append((m.shape(), [p.v for t, p in m.marks()[1:]], m.W.v, len(m.outcomes)))
    return states, m.outcomes
ROUTE = ['GMM', 'GMMM', 'GMMW', 'GMWW', 'GWWW', 'GBW', 'GMB']
def analyse(n0):
    states, outs = concrete_run(n0)
    shapes = [s[0] for s in states]
    for i in range(len(shapes) - 6):
        if shapes[i:i + 7] == ROUTE:
            sh, pos, E, o0 = states[i]
            o1 = states[i + 4][3]
            forced = outs[o0:o1]
            # symbolic: variables (m, E); the second marker is the end marker at E - 2
            md = Model(2); md.W = Pos([F(0), F(1), F(0)], F(E) * 2 ** 100)
            md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(pos[0]) * 2 ** 100)); md.add('M', md.W - 2)
            md.force = list(forced)
            for want in ROUTE[1:5]:
                md.do_round()
                if md.bad or md.shape() != want: return None
            mk = md.marks(); a, b, c = [p for t, p in mk[1:]]; W = md.W
            R = W - c - 1
            L = Pos([1029 * x + 1960 * y - 2744 * z for x, y, z in zip(b.f, W.f, c.f)], 0) - 4046
            C = Coset(2)
            for pform, res, mod in md.cong:
                f = pform.f; den = max(q.denominator for q in f)
                C.impose([int(q * den) for q in f[:2]], den * res - int(f[2] * den), den * mod, reduce=False)
            C.B = lll(C.B)
            # largest g such that some (m, E) in the coset has L = 0 mod 2^60 and R = 0 mod 2^g
            def solvable(g):
                D = Coset(2); D.x0 = C.x0[:]; D.B = [r[:] for r in C.B]
                for form, md_ in ((L, 60), (R, g)):
                    f = form.f; den = max(q.denominator for q in f)
                    if not D.impose([int(q * den) for q in f[:2]], -int(f[2] * den), den * 2 ** md_, reduce=False): return False
                return True
            g = 0
            while g < 50 and solvable(g + 1): g += 1
            det = R.f[0] * L.f[1] - R.f[1] * L.f[0]
            return dict(n=n0, R=fmt(R, ['m', 'E']), L=fmt(L, ['m', 'E']), det=det, v2det=None if det == 0 else (v2(det.numerator) - v2(det.denominator)),
                        coset_bits=round(C.index_bits(), 1), cap=g)
    return None
if __name__ == '__main__':
    for l in list(open(sys.argv[1]))[:int(sys.argv[2])]:
        r = analyse(int(l.split()[0]))
        if r: print(r)
