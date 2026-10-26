"""Write the GMM-born chain prefixes (route + plain passes + entry + extra-wall word + progress-keeping drop, ending at
G W W W) found by chainfam.py as routes for routeexclude2."""
import json, sys
import mixdrop as MD
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import CYC, outs as L_out
routes = [json.loads(l) for l in open('../routetree_routes30.txt')]
sfx = [(a, b) for a, b, w in json.load(open('../entry_suffixes.json')) if a.count('GWWWW') == 1 and a[-1] == 'GWWWW']
chains = [(2740, 0, 19, 'QQT'), (2740, 0, 15, 'QQT'), (2705, 0, 5, 'PQT'), (2503, 2, 1, 'QPU'), (2463, 2, 18, 'PPT'),
          (1271, 0, 5, 'PQT'), (1192, 2, 2, 'QQT'), (626, 0, 5, 'PQT'), (433, 0, 5, 'PQT'), (368, 0, 5, 'QPT'),
          (339, 0, 2, 'PPT'), (285, 1, 2, 'QQT'), (143, 1, 6, 'QQT'), (5, 2, 2, 'QQT'), (2281, 0, 11, 'PQQU')]
with open('../chain_routes.jsonl', 'w') as f:
    for ri, p, si, w in chains:
        r = routes[ri]
        shapes = r['shapes'] + CYC * p + sfx[si][0] + sum((MD.SH[x] for x in w), [])
        outs = r['outs'] + L_out * p + list(sfx[si][1]) + sum((MD.OUT[x] for x in w), [])
        f.write(json.dumps({'ratio': r['ratio'], 'measure': r['measure'], 'shapes': shapes, 'outs': outs}) + '\n')
print(len(chains), 'chain prefixes written')
