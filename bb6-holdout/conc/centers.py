"""At plain-loop pass starts: do the three walls share one 2-adic 'centre' tau = kappa_E - kappa_x/lambda_x?
Report v2 of the pairwise differences of tau, the wall depths s, and the gap."""
import sys, collections
from fractions import Fraction as F
from conc import Model, Pos
from depthslack import v2f
def tau(p, W): return W.f[1] - p.f[1] * W.f[0] / p.f[0]
def s_of(p):
    d = p.f[0].denominator; s = 0
    while d > 1: d //= 2; s += 1
    return s
stats = collections.Counter()
for l in list(open(sys.argv[1]))[:int(sys.argv[2])]:
    n0 = int(l.split()[0])
    m = Model(1); m.W = Pos([F(1), F(6)], 2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2); hist = []; snaps = []
    for r in range(3000):
        hist.append(m.shape()); snaps.append([(t, p) for t, p in m.marks()[1:]] + [('E', m.W)])
        m.do_round()
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    for i in range(len(hist) - 2):
        if hist[i] == 'GWWW' and hist[i + 1] == 'GBW' and hist[i + 2] == 'GMB':
            (ta, a), (tb, b), (tc, c), (_, W) = snaps[i]
            A, B_, C = tau(a, W), tau(b, W), tau(c, W)
            print(n0, "round", i, "depths s:", s_of(a), s_of(b), s_of(c), "| v2(tau_a - tau_b) =", v2f(A - B_), " v2(tau_b - tau_c) =", v2f(B_ - C),
                  "| tau_b - tau_c =", float(B_ - C))
            break
