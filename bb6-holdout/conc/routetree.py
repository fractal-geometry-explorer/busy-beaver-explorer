"""Enumerate, exactly, the routes from a free GMM state (m, E) into the plain loop: follow every branch of the
segment (2-adic cosets in m and E) and record each prefix that ends at a G W W W, with its full outcome list and its
2-adic measure.  Then run the single-stretch exclusion (routeexclude) on every distinct route, in both loop phases.
usage: routetree.py cut_bits ratio [ratio ...]  -> writes ../routetree_routes.txt"""
import sys, copy, collections, math, json
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch
from gmmreturn import start

def explore(ratio, cut_bits, max_rounds=200):
    m0 = start(ratio); c0 = Coset([0, 1], [[2, 0], [0, 2]])
    stack = [(m0, c0, [], 0, ())]
    routes = collections.defaultdict(F); lost = F(0); seen_gwww = F(0)
    while stack:
        ms, cs, forced, rd, hist = stack.pop()
        m = copy.deepcopy(ms); c = cs.copy(); m.setup_tree(c); m.forced = forced
        try:
            m.do_round()
        except Branch:
            if cs.bits + len(forced) + 1 > cut_bits: lost += F(1, 2 ** (cs.bits + len(forced))); continue
            stack.append((ms, cs, forced + [0], rd, hist)); stack.append((ms, cs, forced + [2], rd, hist)); continue
        except AssertionError:
            continue
        if m.halted or m.bad: continue
        sh = m.shape(); mk = m.marks(); h2 = hist + (sh,)
        if sh == 'GM' and mk[1][1].v == m.W.v - 2: continue
        if sh == 'GMM' and mk[2][1].v == m.W.v - 2: continue
        if sh == 'GWWW':
            routes[(h2, tuple(m.outcomes))] += F(1, 2 ** c.bits)
        if rd + 1 >= max_rounds: lost += F(1, 2 ** c.bits); continue
        stack.append((m, c, [], rd + 1, h2))
    return routes, lost

if __name__ == '__main__':
    cut = int(sys.argv[1]); ratios = [float(x) for x in sys.argv[2:]]
    allr = {}
    for r in ratios:
        routes, lost = explore(r, cut)
        tot = sum(routes.values())
        print(f"ratio {r}: {len(routes)} route prefixes ending at G W W W, total measure {float(tot):.4e}, lost {float(lost):.3e}", flush=True)
        for (h, o), p in routes.items():
            key = (h, o)
            if key not in allr: allr[key] = (r, p)
            else: allr[key] = (allr[key][0], max(allr[key][1], p))
    with open('../routetree_routes.txt', 'w') as f:
        for (h, o), (r, p) in sorted(allr.items(), key=lambda x: -x[1][1]):
            f.write(json.dumps({'ratio': r, 'measure': float(p), 'shapes': list(h), 'outs': list(o)}) + '\n')
    print("distinct routes", len(allr))
