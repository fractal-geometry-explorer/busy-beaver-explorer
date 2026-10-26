"""Words of the extra-wall loop allowed after each GMM-born route into G W W W W (routes cached by ewforms.py).
usage: ewwords.py routes.json"""
import sys, json, collections
import ewroutes as EW
routes = json.load(open(sys.argv[1]))
words = ['P', 'Q', 'PP', 'PQ', 'QP', 'QQ']
summ = collections.Counter(); tot = 0
for idx, (h, o, p) in enumerate(routes):
    tot += p
    res = {w: EW.consistent(h, o, w) for w in words}
    ok = tuple(w for w in words if res[w] == 'ok')
    summ[ok] += 1
    if ok: print(f"#{idx} measure {p:.2e}: allows {list(ok)}; route {' '.join(h)}", flush=True)
print(f"{len(routes)} routes, measure {tot:.3e}; by allowed words: {dict(summ)}")
