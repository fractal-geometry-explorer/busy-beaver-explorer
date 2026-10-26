import json, collections
from lattice import Coset as LCoset
import ewforms as EF
from ewlock2 import consistent
import ewroutes as EW
routes = json.load(open('../ewroutes_30.json'))
tally = collections.Counter(); meas = collections.Counter(); agree = 0
for idx, (h, o, p) in enumerate(routes):
    md = EF.route_model(h, o); mk = md.marks()
    fam = [list(q.f) for t, q in mk[1:]] + [list(md.W.f)]
    # family only: words consistent on the bare family (m even, E odd imposed via substitution m = 2u, E = 2v + 1)
    fam2 = [[f[0] * 2, f[1] * 2, f[2] + f[1]] for f in fam]
    frontier = ['']; longest = 0
    for L in range(1, 4):
        nxt = [w + x for w in frontier for x in 'PQ' if consistent(fam2, 2, w + x)]
        if not nxt: break
        longest = L; frontier = nxt
    coset_words = [w for w in ('P', 'Q') if EW.consistent(h, o, w) == 'ok']
    tally[(longest, len(coset_words) > 0)] += 1; meas[longest] += p
print("(longest word on the bare family, some pass allowed on the route coset):", dict(tally))
print("entry measure by family cap:", {k: f"{v:.2e}" for k, v in meas.items()})
