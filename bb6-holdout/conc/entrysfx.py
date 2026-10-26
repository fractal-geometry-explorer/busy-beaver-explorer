"""Distinct ways from a G W W W into G W W W W (suffix shapes and outcomes after the last G W W W) among GMM-born
entries; saved for building more entry families."""
import json, collections
from fractions import Fraction as F
from conc import Model, Pos
def per_round(shapes, outs, ratio=0.5):
    E_ex = 2 ** 40 + 1; m_ex = int(E_ex * ratio) // 2 * 2; sc = F(2) ** 140
    md = Model(2); md.W = Pos([F(0), F(1), F(0)], F(E_ex) * sc)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(m_ex) * sc)); md.add('M', md.W - 2)
    md.force = list(outs); cuts = [0]
    for want in shapes:
        md.do_round(); assert md.shape() == want; cuts.append(len(md.outcomes))
    return cuts
routes = json.load(open('../ewroutes_30.json'))
sfx = collections.Counter()
for h, o, p in routes:
    idx = [i for i, s in enumerate(h) if s == 'GWWW']
    if not idx: continue
    i = idx[-1]; cuts = per_round(h, o)
    sfx[(tuple(h[i + 1:]), tuple(o[cuts[i + 1]:]))] += p
out = [[list(a), list(b), w] for (a, b), w in sorted(sfx.items(), key=lambda x: -x[1])]
json.dump(out, open('../entry_suffixes.json', 'w'))
for a, b, w in out[:30]: print(f"{w:.2e}", ' '.join(a), b)
print(len(out), 'suffixes')
