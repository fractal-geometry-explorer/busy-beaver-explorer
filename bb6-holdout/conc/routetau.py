"""Main route (GMM GMMM GMMW GMWW -> GWWW GBW GMB): the gap G_R as v2(1225*tau + 38423) - 3, where
tau = E - m*(lam_E/lam_m) is the line's 2-adic invariant at the route's first state (m = the left marker)."""
import sys, collections
from fractions import Fraction as F
from conc import Model, Pos
from snf2 import v2
from depthslack import v2f
ROUTE = ['GMM', 'GMMM', 'GMMW', 'GMWW', 'GWWW', 'GBW', 'GMB']
def run_line(n0, k, upto):
    rho = n0 % (1 << k)
    m = Model(1); m.W = Pos([F(2 ** (k + 1)), F(2 * rho + 6)], 2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2)
    snaps = []
    for r in range(upto):
        snaps.append((m.shape(), [(p.f, p.v) for t, p in m.marks()[1:]], (m.W.f, m.W.v)))
        m.do_round()
    snaps.append((m.shape(), [(p.f, p.v) for t, p in m.marks()[1:]], (m.W.f, m.W.v)))
    return snaps
def analyse(n0):
    # find the route in the concrete run
    m = Model(1); m.W = m.const(2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2); sh = []
    for r in range(3000):
        sh.append(m.shape()); m.do_round()
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    sh.append(m.shape())
    for i in range(len(sh) - 6):
        if sh[i:i + 7] == ROUTE: break
    else: return None
    # a deep enough parametrisation: use k = 60 (all tests decided for n mod 2^60 = n itself, j free)
    snaps = run_line(n0, 60, i + 4)
    s0, pos0, (Wf, Wv) = snaps[i]
    (mf, mv), (ef, ev) = pos0[0], pos0[1]
    lam_m, kap_m = mf; lam_E, kap_E = Wf
    tau = kap_E - kap_m * lam_E / lam_m
    pred = v2f(1225 * tau + 38423) - 3
    s4, pos4, (W4, _) = snaps[i + 4]
    b, c = pos4[1][0], pos4[2][0]
    lR = W4[0] - c[0]; kR = W4[1] - c[1] - 1
    lL = 1029 * b[0] + 1960 * W4[0] - 2744 * c[0]; kL = 1029 * b[1] + 1960 * W4[1] - 2744 * c[1] - 4046
    D = lR * kL - lL * kR
    GR = v2f(D) - v2f(lL)
    return tau, pred, GR
if __name__ == '__main__':
    cnt = collections.Counter(); taus = collections.Counter()
    for l in list(open(sys.argv[1]))[:int(sys.argv[2])]:
        n0 = int(l.split()[0]); r = analyse(n0)
        if not r: continue
        tau, pred, GR = r
        cnt[(pred, GR)] += 1
        num, den = tau.numerator, tau.denominator
        taus[(num * pow(den, -1, 1 << 16)) % (1 << 16)] += 1
    print("(predicted, actual G_R):", dict(cnt))
    print("tau mod 2^16 values:", len(taus), taus.most_common(8))
