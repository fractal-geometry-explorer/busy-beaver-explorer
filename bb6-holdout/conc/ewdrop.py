"""For the GMM-born routes into G W W W W that allow one extra-wall pass, test pass + drop (+ plain passes)."""
import math
from fractions import Fraction as F
from conc import Model, Pos
from lattice import Coset as LCoset
import mixdrop as MD
import ewroutes as EW
routes, lost = EW.explore(0.5, 26)
def coset_ok(shapes, outs, letters):
    E_ex = 2 ** 40 + 1; m_ex = int(E_ex * 0.5) // 2 * 2; sc = F(2) ** 300
    md = Model(2); md.W = Pos([F(0), F(1), F(0)], F(E_ex) * sc)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(m_ex) * sc)); md.add('M', md.W - 2)
    md.force = list(outs)
    for x in letters: md.force += MD.OUT[x]
    for want in list(shapes) + sum((MD.SH[x] for x in letters), []):
        md.do_round()
        if md.bad or md.shape() != want: return 'geometry'
    C = LCoset(2)
    for pform, res, mod in md.cong:
        f = pform.f; den = 1
        for q in f: den = den * q.denominator // math.gcd(den, q.denominator)
        if not C.impose([int(q * den) for q in f[:2]], den * res - int(f[2] * den), den * mod, reduce=False): return 'inconsistent'
    if not C.impose([1, 0], 0, 2, reduce=False) or not C.impose([0, 1], 1, 2, reduce=False): return 'inconsistent'
    return 'ok'
for (h, o), p in routes.items():
    for first in ('P', 'Q'):
        if coset_ok(h, o, first) != 'ok': continue
        res = {}
        for d in ('D', 'd', 'X', 'Y', 'Z', 'U', 'V', 'T'):
            r1 = coset_ok(h, o, first + d)
            r2 = coset_ok(h, o, first + d + 'L') if r1 == 'ok' else '-'
            res[d] = (r1, r2)
        print(first, ' '.join(h)[-60:], res)
