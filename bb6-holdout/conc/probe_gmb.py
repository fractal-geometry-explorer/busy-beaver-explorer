import itertools, collections, copy, sys
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
SC = 2 ** 200
tok = [l.split() for l in open('prerun_examples.txt') if l.startswith(sys.argv[1] + ' ')][0]
shape = tok[0]; Wv = int(tok[1]) * SC; posv = [int(x) * SC for x in tok[2:]]
cap = int(sys.argv[2])
free = [i for i, (t, p) in enumerate(zip(shape[1:], posv)) if not (t == 'M' and p == Wv - 2)]
nv = len(free) + 1
shown = collections.Counter()
for par in itertools.product((0, 1), repeat=nv):
    m = TModel(nv)
    Ef = [F(0)] * (nv + 1); Ef[nv - 1] = F(1); m.W = Pos(Ef, F(Wv))
    for i, (t, p) in enumerate(zip(shape[1:], posv)):
        if i in free: f = [F(0)] * (nv + 1); f[free.index(i)] = F(1); m.add(t, Pos(f, F(p)))
        else: m.add(t, m.W - 2)
    m.add('G', m.const(1)); m.run = []; m.hist = [shape]
    c = Coset(list(par), [[2 * (i == j) for j in range(nv)] for i in range(nv)])
    stack = [(m, c, [])]
    while stack:
        m0, c0, fo = stack.pop()
        mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = fo; ne0 = len(mm.endd)
        try: mm.do_round()
        except Branch:
            if c0.bits + len(fo) + 1 > cap:
                key = ' '.join(m0.hist[-12:])
                if shown['cap'] < 6: print("CAPPED run", len(m0.run), "bits", c0.bits, ":", ' '.join(m0.hist))
                shown['cap'] += 1
                continue
            stack.append((m0, c0, fo + [0])); stack.append((m0, c0, fo + [2])); continue
        except AssertionError: continue
        if mm.halted or mm.bad: continue
        mm.hist.append(mm.shape()); broken = False
        for (rr, d) in mm.endd[ne0:]:
            if mm.run and pred_form(*mm.run[-1]).f != d.f:
                if len(mm.hist) == 2: mm.run = []
                else: broken = True; break
            mm.run.append((d, cc.decided(d.f)))
        if broken:
            if len(mm.run) >= 7 and shown['long'] < 6: print("LONG run", len(mm.run), ":", ' '.join(mm.hist)); shown['long'] += 1
            continue
        if mm.run and mm.hist[-1] == 'GWWW' and len(mm.hist) > 1: continue
        mk = mm.marks(); fin = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
        if fin or (len(mm.hist) == 2 and not mm.run) or len(mm.hist) > 300: continue
        stack.append((mm, cc, []))
