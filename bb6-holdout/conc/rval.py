"""2-adic valuation of the right countdown R = E - w_last - 1 at the loop entry, on each route's coset:
determined (and its value) or only bounded below.
usage: rval.py routes.json|routes.jsonl"""
import sys, json, collections
from fractions import Fraction as F
import ewforms as EF
def v2(x):
    x = int(x); 
    if x == 0: return 999
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
src = sys.argv[1]
if src.endswith('.json'): routes = [(h, o) for h, o, p in json.load(open(src))]
else: routes = [(r['shapes'], r['outs']) for r in map(json.loads, open(src))]
tally = collections.Counter()
for idx, (h, o) in enumerate(routes):
    md = EF.route_model(h, o)
    if md is None: tally['geometry'] += 1; continue
    C = EF.coset_from(md.cong)
    C.impose([1, 0], 0, 2, reduce=False); C.impose([0, 1], 1, 2, reduce=False)
    mk = md.marks(); R = md.W - mk[-1][1] - 1
    f = R.f
    val0 = f[0] * C.x0[0] + f[1] * C.x0[1] + f[2]
    lin = [f[0] * b[0] + f[1] * b[1] for b in C.B]
    # all values are rationals with odd... denominators are powers of 2; scale
    den = 1
    for q in [val0] + lin: den = max(den, q.denominator)
    s = v2(den)
    t = min(v2(q * den) for q in lin) - s
    v = v2(val0 * den) - s
    key = ('determined', v) if v < t else ('at least', t)
    tally[key] += 1
print(sorted(tally.items(), key=str))
