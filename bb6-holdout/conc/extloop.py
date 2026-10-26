"""The loop with one more wall (G W W W W ...): from a generic state of that shape, the exact probability that one pass
of the extended pattern completes, and the most run meetings otherwise. Positions a < b < c < d < E free."""
import sys, copy, collections, itertools
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
EXT = [s + 'W' for s in LOOP]
cap = int(sys.argv[1]); geo = [int(x) for x in sys.argv[2].split(',')]
SC = 2 ** 200; big = [F(v) * SC for v in geo]
nv = 5
for par in itertools.product((0, 1), repeat=nv):
    m = TModel(nv)
    for i in range(4): m.add('W', Pos([F(int(i == j)) for j in range(nv)] + [F(0)], big[i]))
    m.W = Pos([F(int(j == 4)) for j in range(nv)] + [F(0)], big[4]); m.add('G', m.const(1)); m.run = []; m.hist = ['GWWWW']
    c = Coset(list(par), [[2 * (i == j) for j in range(nv)] for i in range(nv)])
    stack = [(m, c, [])]; comp = F(0); exits = collections.Counter(); capped = 0; ok = False
    while stack:
        m0, c0, fo = stack.pop()
        mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = fo; ne0 = len(mm.endd)
        try: mm.do_round()
        except Branch:
            if c0.bits + len(fo) + 1 > cap: capped += 1; continue
            stack.append((m0, c0, fo + [0])); stack.append((m0, c0, fo + [2])); continue
        except AssertionError: continue
        if mm.halted or mm.bad: continue
        ok = True
        mm.hist.append(mm.shape()); broken = False
        for (rr, d) in mm.endd[ne0:]:
            if mm.run and pred_form(*mm.run[-1]).f != d.f: broken = True; break
            mm.run.append((d, cc.decided(d.f)))
        if len(mm.hist) == 9 and not broken and any(all(mm.hist[k] == EXT[(ph + k) % 8] for k in range(9)) for ph in (0, 6)):
            comp += F(1, 2 ** cc.bits); continue
        mk = mm.marks(); fin = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
        if broken or fin or len(mm.hist) > 200: exits[len(mm.run)] += 1; continue
        stack.append((mm, cc, []))
    if ok and (comp or exits):
        print(f"parities {par}: P(extended pass completes) = {comp} ; exits by run meetings {dict(sorted(exits.items()))} ; capped {capped}")
