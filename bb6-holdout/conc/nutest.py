"""For a main-route stage with growth g: the clean tapes that would line up best are the truncations of the 2-adic
number nu_g = (tau* - 6 - g)/2, tau* = -38423/1225.  What do their cycles actually do?"""
import sys
from conc import Model
from fractions import Fraction as F
from depthslack import v2f
ROUTE = ['GMM', 'GMMM', 'GMMW', 'GMWW', 'GWWW', 'GBW', 'GMB']
def cycle_info(n0):
    m = Model(1); m.W = m.const(2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2); sh = []; Ws = []
    for r in range(3000):
        sh.append(m.shape()); Ws.append(m.W.v); m.do_round()
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    sh.append(m.shape()); Ws.append(m.W.v)
    hits = [(i, Ws[i] - (2 * n0 + 6)) for i in range(len(sh) - 6) if sh[i:i + 7] == ROUTE]
    ends = [int(d.v) for r, d in m.endd]
    return hits, len(sh), m.endd
tstar = F(-38423, 1225)
for g in map(int, sys.argv[1:]):
    nu = (tstar - 6 - g) / 2
    for b in (20, 28, 36, 44):
        M = 1 << b
        n = (nu.numerator * pow(nu.denominator, -1, M)) % M
        n = n + M if n < M // 2 else n          # make it b or b+1 bits with the top digits of nu
        if n % 2: print(g, b, "odd n, skip"); continue
        hits, rounds, endd = cycle_info(n)
        print(f"g={g} b={b} n={n}: main-route entries (round, growth) {hits}; cycle rounds {rounds}")
