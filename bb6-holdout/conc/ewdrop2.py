"""For GMM-born routes into G W W W W (cached JSON from ewforms.py) that allow one extra-wall pass, test each drop
after it and write the consistent extended prefixes (route + pass + drop, ending at G W W W) for routeexclude2.
usage: ewdrop2.py routes.json out.jsonl"""
import sys, json, math, collections
from fractions import Fraction as F
from conc import Model, Pos
from lattice import Coset as LCoset
import mixdrop as MD
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
routes = json.load(open(sys.argv[1])); out = open(sys.argv[2], 'w')
tally = collections.Counter(); n = 0
for idx, (h, o, p) in enumerate(routes):
    for first in 'PQ':
        if coset_ok(h, o, first) != 'ok': continue
        res = {d: coset_ok(h, o, first + d) for d in ('D', 'd', 'X', 'Y', 'Z', 'U', 'V', 'T')}
        ok = [d for d, r in res.items() if r == 'ok']
        tally[(first, tuple(ok))] += 1
        print(f"#{idx} {first}: consistent drops {ok}  {res}", flush=True)
        for d in ok:
            out.write(json.dumps({'ratio': 0.5, 'measure': p, 'shapes': list(h) + MD.SH[first] + MD.SH[d],
                                  'outs': list(o) + MD.OUT[first] + MD.OUT[d]}) + '\n'); n += 1
print(dict(tally), 'extended prefixes written:', n)
