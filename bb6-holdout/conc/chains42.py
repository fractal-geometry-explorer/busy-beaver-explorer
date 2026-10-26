"""Every chain from a GMM-born entry into G W W W W decided within 42 bits: extra-wall words allowed on the route's
own coset (up to length 4), then each drop into the plain loop that stays consistent; written as routes (ending at
G W W W) for routeexclude3.
usage: chains42.py rtree_X.jsonl out.jsonl"""
import sys, json, collections
from lattice import Coset as LCoset
import routeexclude3 as R3
import mixdrop as MD
def coset_ok(shapes, outs):
    m = R3.start(0.5, 2 ** 300)
    if not R3.run(m, shapes, outs): return False
    C = LCoset(2)
    return R3.impose_all(C, m.cong) and C.impose([1, 0], 0, 2, reduce=False) and C.impose([0, 1], 1, 2, reduce=False)
rows = [json.loads(l) for l in open(sys.argv[1])]
rows = [r for r in rows if r['shapes'].count('GWWWW') == 1]
out = open(sys.argv[2], 'w'); tally = collections.Counter(); nchain = 0
for i, r in enumerate(rows):
    sh, ou = r['shapes'], r['outs']
    frontier = ['']; allowed = []
    for L in range(1, 5):
        nxt = [w + x for w in frontier for x in 'PQ' if coset_ok(sh + sum((MD.SH[c] for c in w + x), []), ou + sum((MD.OUT[c] for c in w + x), []))]
        if not nxt: break
        allowed += nxt; frontier = nxt
    tally[max([len(w) for w in allowed], default=0)] += 1
    for w in allowed:
        for d in ('D', 'd', 'X', 'Y', 'Z', 'U', 'V', 'T'):
            s2 = sh + sum((MD.SH[c] for c in w + d), []); o2 = ou + sum((MD.OUT[c] for c in w + d), [])
            if coset_ok(s2, o2):
                out.write(json.dumps({'ratio': 0.5, 'measure': r['measure'], 'shapes': s2, 'outs': o2, 'word': w + d}) + '\n'); nchain += 1
    if i % 1000 == 0: print(i, dict(tally), nchain, flush=True)
print("entries by longest word allowed on their coset:", dict(tally), "; chains written:", nchain)
