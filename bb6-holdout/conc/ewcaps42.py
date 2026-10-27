"""Extra-wall caps of every GMM-born first entry into G W W W W found by the C route tree (bare family test).
usage: ewcaps42.py rtree_X.jsonl out.json"""
import sys, json, collections
from fractions import Fraction as F
import fasttree as FT
from ewlock2 import consistent
import routeexclude3 as R3
SC = FT.SC
rows = [json.loads(l) for l in open(sys.argv[1])]
rows = [r for r in rows if r['shapes'].count('GWWWW') == 1]
tally = collections.Counter(); meas = collections.Counter(); found = []
for i, r in enumerate(rows):
    m = R3.start(0.5, 2 ** 300)
    if not R3.run(m, r['shapes'], r['outs']): tally['geometry'] += 1; continue
    mk = m.marks()
    fam = [[F(q.f[0], SC), F(q.f[1], SC), F(q.f[2], SC)] for t, q in mk[1:]] + [[F(m.W.f[0], SC), F(m.W.f[1], SC), F(m.W.f[2], SC)]]
    fam2 = [[f[0] * 2, f[1] * 2, f[2] + f[1]] for f in fam]
    frontier = ['']; L = 0
    while L < 6:
        nxt = [w + x for w in frontier for x in 'PQ' if consistent(fam2, 2, w + x)]
        if not nxt: break
        frontier = nxt; L += 1
    tally[L] += 1; meas[L] += r['measure']
    if L >= 2: found.append((r['shapes'], r['outs'], r['measure'], frontier))
    if i % 2000 == 0: print(i, dict(tally), flush=True)
print("first entries by cap:", dict(tally)); print("measure by cap:", {k: f"{v:.3e}" for k, v in meas.items()})
json.dump(found, open(sys.argv[2], 'w'))
