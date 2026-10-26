import json, math
from fractions import Fraction as F
import routeexclude as RX
E_ex = 2 ** 40 + 1; worst = []
for idx, l in enumerate(open('../routetree_routes30.txt')):
    r = json.loads(l); m_ex = int(E_ex * r['ratio']) // 2 * 2
    for ph in 'AB':
        sh = list(r['shapes']); ou = list(r['outs'])
        if ph == 'B': sh += ['GBW', 'GWWW']; ou += [2, 2, 2]
        md, err = RX.forced(m_ex, E_ex, sh, ou, 0, F(2) ** 80)
        if md is None: continue
        d = md.W - md.marks()[-1][1]; a, b, c = d.f
        lo = min(b, a + b)
        if lo <= 0: continue
        # smallest d over the box at k = 18 relative to lo*2^18
        k = 18; E0 = 2 ** k
        dmin = min(b * E0 + a * 4 + c, (a + b) * E0 - 7 * a + c) if a >= 0 else min(b * E0 + 4 * a + c, (a + b) * 2 * E0 - 7 * a + c)
        loss = math.log2(float(lo * E0) / float(dmin)) if dmin > 0 else 99
        worst.append((loss, idx, ph, float(c), float(lo)))
worst.sort(reverse=True)
for w in worst[:8]: print(w)
