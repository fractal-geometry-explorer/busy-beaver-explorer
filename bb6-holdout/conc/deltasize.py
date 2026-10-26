"""Real size of the line invariant Delta at every plain-loop pass start, over random clean tapes."""
import sys, random, math
from fractions import Fraction as F
from conc import Model, Pos
from depthslack import v2f, dexp
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
vals = []; odd = 0; tot = 0
for t in range(int(sys.argv[1])):
    n0 = random.randrange(2 ** 30, 2 ** 40); w0 = 2 * n0 + 6
    m = Model(1); m.W = Pos([F(1), F(0)], w0); m.add('G', m.const(1)); m.add('M', m.W - 2)
    snaps = []; hist = []
    for r in range(1, 5000):
        m.do_round(); sh = m.shape(); hist.append(sh)
        if sh == 'GWWW':
            mk = m.marks(); a, b, c = [p for tt, p in mk[1:]]; snaps.append((r, b, c, m.W))
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    for (r, b, c, E) in snaps:
        if r + 1 < len(hist) and hist[r] == 'GBW' and hist[r + 1] == 'GMB':
            Rf = E - c - 1; Lf = Pos([1029 * x + 1960 * y - 2744 * z for x, y, z in zip(b.f, E.f, c.f)], 0) - 4046
            lR, kR = Rf.f; lL, kL = Lf.f; D = lR * kL - lL * kR
            tot += 1; vals.append((float(abs(D)), r, n0, v2f(D) - v2f(lL), v2f(D) - v2f(lR)))
            if D.numerator % 2: odd += 1
vals.sort()
print(f"{tot} pass starts; Delta numerator odd in {odd}")
for q in (0, 0.01, 0.1, 0.5, 0.9, 0.99, 1):
    v = vals[min(len(vals) - 1, int(q * len(vals)))]
    print(f"  quantile {q}: |Delta| = {v[0]:.4g} (log2 {math.log2(v[0]) if v[0] else '-inf'}) round {v[1]} n {v[2]} gaps {v[3]},{v[4]}")
