"""Coverage of deep runs by route prefixes: for each long segment (m, E, entry round re of its deepest run), check
whether its prefix of shapes and outcomes up to round re is one of the enumerated routes.
usage: covercheck.py routes.jsonl runentry_L.txt"""
import sys, json, collections
from conc import Model
routes = set()
for l in open(sys.argv[1]):
    r = json.loads(l); routes.add((tuple(r['shapes']), tuple(r['outs'])))
def concrete(m, E, upto):
    md = Model(0); md.W = md.const(E); md.add('G', md.const(1)); md.add('M', md.const(m)); md.add('M', md.W - 2)
    shapes = []; cuts = []
    for r in range(upto):
        md.do_round(); shapes.append(md.shape()); cuts.append(len(md.outcomes))
    return shapes, md.outcomes, cuts
tot = collections.Counter(); miss = []
for l in open(sys.argv[2]):
    _, m, E, re, R0, Rs = l.split(); m, E, re = int(m), int(E), int(re)
    if re < 0: tot['no loop'] += 1; continue
    sh, outs, cuts = concrete(m, E, re)
    key = (tuple(sh), tuple(outs[:cuts[-1]]))
    first = sh.index('GWWW') + 1 == re
    ok = key in routes
    tot[(('first' if first else 'later'), ok)] += 1
    if not ok: miss.append((m, E, re, ' '.join(sh)))
print(dict(tot))
for x in miss[:40]: print(x)
