"""Exhaustive one-pass exit search for the loop with k extra walls from a generic state (real geometry): completed
passes are set aside; every other path is followed until its run ends. Reports the most run meetings, the paths cut,
and whether any exit later runs 4 consecutive rounds of any loop of the family (k' = 0..3)."""
import sys, copy, itertools, collections
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
LOOP = ['GWWW', 'GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW']
k = int(sys.argv[1]); cap = int(sys.argv[2]); geo = [int(x) for x in sys.argv[3].split(',')]; Ev = geo.pop()
EXT = [s + 'W' * k for s in LOOP]
def has_loop_stretch(h, start):
    for kk in range(0, 4):
        P = [s + 'W' * kk for s in LOOP]
        for i in range(start, len(h)):
            for ph in range(8):
                j = 0
                while i + j < len(h) and h[i + j] == P[(ph + j) % 8]: j += 1
                if j >= 4: return kk
    return None
nw = 3 + k; nv = nw + 1; SC = 2 ** 200
big = [F(v) * SC for v in geo] + [F(Ev) * SC]
for par in itertools.product((0, 1), repeat=nv):
    m = TModel(nv)
    for i in range(nw): m.add('W', Pos([F(int(i == j)) for j in range(nv)] + [F(0)], big[i]))
    m.W = Pos([F(int(j == nv - 1)) for j in range(nv)] + [F(0)], big[-1]); m.add('G', m.const(1)); m.run = []; m.hist = [EXT[0]]
    c = Coset(list(par), [[2 * (i == j) for j in range(nv)] for i in range(nv)])
    stack = [(m, c, [])]; comp = F(0); exits = collections.Counter(); cut = 0; back = collections.Counter(); valid = False
    while stack:
        m0, c0, fo = stack.pop()
        mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = fo; ne0 = len(mm.endd)
        try: mm.do_round()
        except Branch:
            if c0.bits + len(fo) + 1 > cap: cut += 1; continue
            stack.append((m0, c0, fo + [0])); stack.append((m0, c0, fo + [2])); continue
        except AssertionError: continue
        if mm.halted or mm.bad: continue
        valid = True
        mm.hist.append(mm.shape()); broken = False
        for (rr, d) in mm.endd[ne0:]:
            if mm.run and pred_form(*mm.run[-1]).f != d.f: broken = True; break
            mm.run.append((d, cc.decided(d.f)))
        h = mm.hist
        if len(h) == 9 and not broken and any(all(h[q] == EXT[(ph + q) % 8] for q in range(9)) for ph in (0, 6)):
            comp += F(1, 2 ** cc.bits); continue
        mk = mm.marks(); fin = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
        if broken or fin or len(h) > 150:
            exits[len(mm.run)] += 1
            # prefix following the k-loop
            pre = 0
            for ph0 in (0, 6):
                q = 0
                while q < len(h) and h[q] == EXT[(ph0 + q) % 8]: q += 1
                pre = max(pre, q)
            kk = has_loop_stretch(h, pre)
            if kk is not None: back[kk] += 1
            continue
        stack.append((mm, cc, []))
    if valid and (comp or exits):
        print(f"k = {k} parities {par}: P(pass) = {comp}; exits {sum(exits.values())}, most run meetings {max(exits)}; cut {cut}; later loop stretches by k': {dict(back)}", flush=True)
